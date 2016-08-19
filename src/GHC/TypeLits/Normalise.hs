{-|
Copyright  :  (C) 2015-2016, University of Twente
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>

A type checker plugin for GHC that can solve /equalities/ of types of kind
'GHC.TypeLits.Nat', where these types are either:

* Type-level naturals
* Type variables
* Applications of the arithmetic expressions @(+,-,*,^)@.

It solves these equalities by normalising them to /sort-of/
'GHC.TypeLits.Normalise.SOP.SOP' (Sum-of-Products) form, and then perform a
simple syntactic equality.

For example, this solver can prove the equality between:

@
(x + 2)^(y + 2)
@

and

@
4*x*(2 + x)^y + 4*(2 + x)^y + (2 + x)^y*x^2
@

Because the latter is actually the 'GHC.TypeLits.Normalise.SOP.SOP' normal form
of the former.

To use the plugin, add

@
{\-\# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise \#-\}
@

To the header of your file.
-}

{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections   #-}

{-# OPTIONS_HADDOCK show-extensions #-}

module GHC.TypeLits.Normalise
  ( plugin )
where

-- external
import Control.Arrow       (second)
import Data.IORef          (readIORef)
import Data.List           (intersect)
import Data.Maybe          (catMaybes, mapMaybe)
import GHC.TcPluginM.Extra (tracePlugin)

-- GHC API
import Outputable (Outputable (..), (<+>), ($$), text)
import Plugins    (Plugin (..), defaultPlugin)
import TcEvidence (EvTerm (..))
import TcPluginM  (TcPluginM, tcPluginIO, tcPluginTrace, zonkCt)
import TcRnTypes  (Ct, TcPlugin (..), TcPluginResult(..), ctEvidence, ctEvPred,
                   ctPred, isWanted, mkNonCanonical)
import Type       (EqRel (NomEq), Kind, PredTree (EqPred), PredType, TyVar,
                   classifyPredType, eqType, getEqPredTys, mkTyVarTy)
import TysWiredIn (typeNatKind)

import Coercion   (CoercionHole, Role (..), mkForAllCos, mkHoleCo, mkInstCo,
                   mkNomReflCo, mkUnivCo)
import TcPluginM  (newCoercionHole, newFlexiTyVar)
import TcRnTypes  (CtEvidence (..), TcEvDest (..), ctLoc)
import TyCoRep    (UnivCoProvenance (..))
import Type       (mkPrimEqPred)
import TcType     (typeKind)
import TyCoRep    (Type (..))
import TcTypeNats (typeNatAddTyCon, typeNatExpTyCon, typeNatMulTyCon,
                   typeNatSubTyCon)

import TcTypeNats (typeNatLeqTyCon)
import Type       (mkNumLitTy,mkTyConApp)
import TysWiredIn (promotedFalseDataCon, promotedTrueDataCon)

-- internal
import GHC.TypeLits.Normalise.Unify

import Control.Monad (replicateM)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Maybe (MaybeT (..))
import TcPluginM (getEnvs)
import TcRnTypes (ctsElts, isGivenCt, isWantedCt, tcl_lie, wc_simple, wc_insol)

-- | To use the plugin, add
--
-- @
-- {\-\# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise \#-\}
-- @
--
-- To the header of your file.
plugin :: Plugin
plugin = defaultPlugin { tcPlugin = const $ Just normalisePlugin }

normalisePlugin :: TcPlugin
normalisePlugin = tracePlugin "ghc-typelits-natnormalise"
  TcPlugin { tcPluginInit  = return ()
           , tcPluginSolve = const decideEqualSOP
           , tcPluginStop  = const (return ())
           }

decideEqualSOP :: [Ct] -> [Ct] -> [Ct]
               -> TcPluginM TcPluginResult
decideEqualSOP _givens _deriveds []      = return (TcPluginOk [] [])
decideEqualSOP givens  _deriveds wanteds = do
    -- GHC 7.10.1 puts deriveds with the wanteds, so filter them out
    let wanteds' = filter (isWanted . ctEvidence) wanteds
    let unit_wanteds = mapMaybe toNatEquality wanteds'
    case unit_wanteds of
      [] -> return (TcPluginOk [] [])
      _  -> do
        unit_givens <- mapMaybe toNatEquality <$> mapM zonkCt givens
        sr <- simplifyNats (unit_givens ++ unit_wanteds)
        tcPluginTrace "normalised" (ppr sr)
        case sr of
          Simplified _subst evs -> do
            let solved     = filter (isWanted . ctEvidence . (\(_,x,_) -> x)) evs
            -- Create new wanted constraints
            (solved',newWanteds) <- (second concat . unzip . catMaybes) <$>
                                    mapM (evItemToCt) solved
            -- return
            return (TcPluginOk solved' newWanteds)
          Impossible eq -> return (TcPluginContradiction [fromNatEquality eq])

evItemToCt :: (EvTerm,Ct,CoreUnify CoreNote)
           -> TcPluginM (Maybe ((EvTerm,Ct),[Ct]))
evItemToCt (ev,ct,subst)
    | null newWanteds = return (Just ((ev,ct),[]))
    | otherwise = do
        newWanteds' <- catMaybes <$> mapM (substItemToCt) newWanteds
        return (Just ((ev,ct),newWanteds'))
  where
    newWanteds = filter (isWanted . ctEvidence . snd . siNote) subst

substItemToCt :: UnifyItem TyVar CType CoreNote
              -> TcPluginM (Maybe Ct)
substItemToCt si
  | Left ev' <- ev
  = return (Just (mkNonCanonical (CtWanted predicate (HoleDest ev') (ctLoc ct))))
  | otherwise
  = return Nothing
  where
    predicate     = unifyItemToPredType si
    (ev,ct)       = siNote si

unifyItemToPredType :: UnifyItem TyVar CType a -> PredType
unifyItemToPredType ui =
    mkPrimEqPred ty1 ty2
  where
    ty1 = case ui of
            SubstItem {..} -> mkTyVarTy siVar
            UnifyItem {..} -> reifySOP siLHS
    ty2 = case ui of
            SubstItem {..} -> reifySOP siSOP
            UnifyItem {..} -> reifySOP siRHS

type NatEquality   = (Ct,CoreSOP,CoreSOP)
type NatInEquality = (Ct,CoreSOP)

fromNatEquality :: Either NatEquality NatInEquality -> Ct
fromNatEquality (Left  (ct, _, _)) = ct
fromNatEquality (Right (ct, _))    = ct

type CoreNote = (Either CoercionHole CoercionHole, Ct)

data SimplifyResult
  = Simplified (CoreUnify CoreNote) [(EvTerm,Ct,CoreUnify CoreNote)]
  | Impossible (Either NatEquality NatInEquality)

instance Outputable SimplifyResult where
  ppr (Simplified subst evs) = text "Simplified" $$ ppr subst $$ ppr evs
  ppr (Impossible eq)  = text "Impossible" <+> ppr eq

simplifyNats :: [Either NatEquality NatInEquality]
             -> TcPluginM SimplifyResult
simplifyNats eqs =
    tcPluginTrace "simplifyNats" (ppr eqs) >> simples [] [] [] eqs
  where
    simples :: CoreUnify CoreNote
            -> [(EvTerm, Ct, CoreUnify CoreNote)]
            -> [Either NatEquality NatInEquality]
            -> [Either NatEquality NatInEquality]
            -> TcPluginM SimplifyResult
    simples subst evs _xs [] = return (Simplified subst evs)
    simples subst evs xs (eq@(Left (ct,u,v)):eqs') = do
      ur <- unifyNats ct (substsSOP subst u) (substsSOP subst v)
      tcPluginTrace "unifyNats result" (ppr ur)
      case ur of
        Win -> do evM <- runMaybeT (evMagic ct [])
                  let evs' = maybe evs ((:evs) . (,ct,[])) evM
                  simples subst evs' [] (xs ++ eqs')

        Lose -> return (Impossible eq)

        Draw [] -> simples subst evs (eq:xs) eqs'

        Draw subst'
          | isGivenCt ct -> do
          let subst'' = map (\si -> si {siNote = (Right undefined,siNote si)}) subst'
          simples (substsSubst subst'' subst ++ subst'')
                  evs [] (xs ++ eqs')

        Draw subst' -> do
          new_wantedsM <- runMaybeT (mapM (newWantedCoercion . unifyItemToPredType) subst')
          case new_wantedsM of
            Just new_wanteds -> do
              let new_wanted_holes = map snd new_wanteds
                  subst'' = zipWith (\si h -> si {siNote = (h,siNote si)})
                                    subst' new_wanted_holes
              evM <- runMaybeT (evMagic ct (map (second (either id id)) new_wanteds))
              let evs' = maybe evs ((:evs) . (,ct,subst'')) evM
              simples (substsSubst subst'' subst ++ subst'')
                      evs' [] (xs ++ eqs')
            _ -> return (Impossible eq)

    simples subst evs xs (eq@(Right (ct,u)):eqs') =
      case isNatural u of
        Just True  -> do evM <- runMaybeT (evMagic ct [])
                         let evs' = maybe evs ((:evs) . (,ct,[])) evM
                         simples subst evs' xs eqs'
        Just False -> return (Impossible eq)
        Nothing    -> simples subst evs (eq:xs) eqs'

-- Extract the Nat equality constraints
toNatEquality :: Ct -> Maybe (Either NatEquality NatInEquality)
toNatEquality ct = case classifyPredType $ ctEvPred $ ctEvidence ct of
    EqPred NomEq t1 t2
      -> go t1 t2
    _ -> Nothing
  where
    go (TyConApp tc xs) (TyConApp tc' ys)
      | tc == tc'
      , null ([tc,tc'] `intersect` [typeNatAddTyCon,typeNatSubTyCon
                                   ,typeNatMulTyCon,typeNatExpTyCon])
      = case filter (not . uncurry eqType) (zip xs ys) of
          [(x,y)] | isNatKind (typeKind x) &&  isNatKind (typeKind y)
                  -> Just (Left (ct, normaliseNat x, normaliseNat y))
          _ -> Nothing
      | tc == typeNatLeqTyCon
      , [x,y] <- xs
      = if tc' == promotedTrueDataCon
           then Just (Right (ct,normaliseNat (mkTyConApp typeNatSubTyCon [y,x])))
           else if tc' == promotedFalseDataCon
                then Just (Right (ct,normaliseNat (mkTyConApp typeNatSubTyCon [x,mkTyConApp typeNatAddTyCon [y,mkNumLitTy 1]])))
                else Nothing

    go x y
      | isNatKind (typeKind x) && isNatKind (typeKind y)
      = Just (Left (ct,normaliseNat x,normaliseNat y))
      | otherwise
      = Nothing

    isNatKind :: Kind -> Bool
    isNatKind = (`eqType` typeNatKind)

evMagic :: Ct -> [(PredType, CoercionHole)] -> MaybeT TcPluginM EvTerm
evMagic ct evs = case classifyPredType $ ctEvPred $ ctEvidence ct of
  EqPred NomEq t1 t2 -> do
    let ctEv = mkUnivCo (PluginProv "ghc-typelits-natnormalise") Nominal t1 t2
        (preds,holes) = unzip evs
        holeEvs = zipWith (\h p -> uncurry (mkHoleCo h Nominal) (getEqPredTys p))
                          holes preds
        natReflCo = mkNomReflCo typeNatKind
        natCoBndr = (,natReflCo) <$> lift (newFlexiTyVar typeNatKind)
    forallEv <- mkForAllCos <$> (replicateM (length evs) natCoBndr) <*> pure ctEv
    let finalEv = foldl mkInstCo forallEv holeEvs
    return (EvCoercion finalEv)
  _ -> fail "not an eqpred"


-- | Given a predicate type, look for a coercionhole of a wanted with that type,
-- and otherwise create a new coercion hole
newWantedCoercion :: PredType -> MaybeT TcPluginM (PredType,Either CoercionHole CoercionHole)
newWantedCoercion want = (want,) <$> do
  (_, lcl_env) <- lift getEnvs
  -- lookup the existing wanted constraints
  wanted <- lift (tcPluginIO (readIORef (tcl_lie lcl_env)))
  let insol = ctsElts (wc_insol wanted)
      simpl = ctsElts (wc_simple wanted)
      lookup_want = filter ((== (CType want)) . CType . ctPred)
      -- insoluble wanted constraints
      found_insol = lookup_want insol
      -- all other wanted constraints
      found_simpl = lookup_want simpl
  case found_insol of
    [] -> case found_simpl of
      (found:_) | isWantedCt found
        -- if there is an existing wanted, we use its coercion hole
        -> case ctEvidence found of
             CtWanted { ctev_dest = HoleDest h } -> return (Right h)
             _ -> fail "no hole"
        -- otherwise we create a new coercion hole
      _ -> do h <- lift newCoercionHole
              return (Left h)
    -- if the wanted constraint is known to be insoluable, we fail
    _ -> fail "insoluable"
