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
import Data.IORef          (IORef, newIORef,readIORef, modifyIORef)
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
  TcPlugin { tcPluginInit  = tcPluginIO $ newIORef []
           , tcPluginSolve = decideEqualSOP
           , tcPluginStop  = const (return ())
           }

decideEqualSOP :: IORef [Ct] -> [Ct] -> [Ct] -> [Ct]
               -> TcPluginM TcPluginResult
decideEqualSOP _          _givens _deriveds []      = return (TcPluginOk [] [])
decideEqualSOP discharged givens  _deriveds wanteds = do
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
            discharedWanteds <- tcPluginIO (readIORef discharged)
            let existingWanteds = wanteds' ++ discharedWanteds
            -- Create new wanted constraints
            (solved',newWanteds) <- (second concat . unzip . catMaybes) <$>
                                    mapM (evItemToCt existingWanteds) solved
            -- update set of discharged wanteds
            tcPluginIO (modifyIORef discharged (++ newWanteds))
            -- return
            return (TcPluginOk solved' newWanteds)
          Impossible eq -> return (TcPluginContradiction [fromNatEquality eq])

evItemToCt :: [Ct] -- ^ Existing wanteds
           -> (EvTerm,Ct,CoreUnify CoreNote)
           -> TcPluginM (Maybe ((EvTerm,Ct),[Ct]))
evItemToCt existingWanteds (ev,ct,subst)
    | null newWanteds = return (Just ((ev,ct),[]))
    | otherwise = do
        newWanteds' <- catMaybes <$> mapM (substItemToCt existingWanteds) newWanteds
        -- only allow new (conditional) evidence if conditional wanted constraints
        -- can be added as new work
        if length newWanteds == length newWanteds'
           then return (Just ((ev,ct),newWanteds'))
           else return Nothing
  where
    newWanteds = filter (isWanted . ctEvidence . snd . siNote) subst

substItemToCt :: [Ct] -- ^ Existing wanteds wanted
              -> UnifyItem TyVar CType CoreNote
              -> TcPluginM (Maybe Ct)
substItemToCt existingWanteds si
  | CType predicate  `notElem` wantedPreds
  , CType predicateS `notElem` wantedPreds
  = return (Just (mkNonCanonical (CtWanted predicate (HoleDest ev) (ctLoc ct))))
  | otherwise
  = return Nothing
  where
    predicate     = unifyItemToPredType si
    (ty1,ty2)     = getEqPredTys predicate
    predicateS    = mkPrimEqPred ty2 ty1
    ((ev,_,_),ct) = siNote si
    wantedPreds   = map (CType . ctPred) existingWanteds

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

type CoreNote = ((CoercionHole,TyVar,PredType), Ct)

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
            -> [Maybe (EvTerm, Ct, CoreUnify CoreNote)]
            -> [Either NatEquality NatInEquality]
            -> [Either NatEquality NatInEquality]
            -> TcPluginM SimplifyResult
    simples subst evs _xs [] = return (Simplified subst (catMaybes evs))
    simples subst evs xs (eq@(Left (ct,u,v)):eqs') = do
      ur <- unifyNats ct (substsSOP subst u) (substsSOP subst v)
      tcPluginTrace "unifyNats result" (ppr ur)
      case ur of
        Win         -> simples subst (((,,) <$> evMagic ct [] <*> pure ct <*> pure []):evs) []
                               (xs ++ eqs')
        Lose        -> return (Impossible eq)
        Draw []     -> simples subst evs (eq:xs) eqs'
        Draw subst' -> do
          newEvs <- mapM (\si -> (,,) <$> newCoercionHole
                                      <*> newFlexiTyVar typeNatKind
                                      <*> pure (unifyItemToPredType si))
                         subst'
          let subst'' = zipWith (\si ev -> si {siNote = (ev,siNote si)})
                                subst' newEvs
          simples (substsSubst subst'' subst ++ subst'')
            (((,,) <$> evMagic ct newEvs <*> pure ct <*> pure subst''):evs)
            [] (xs ++ eqs')
    simples subst evs xs (eq@(Right (ct,u)):eqs') =
      case isNatural u of
        Just True  -> simples subst (((,,) <$> evMagic ct [] <*> pure ct <*> pure []):evs) xs eqs'
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

evMagic :: Ct -> [(CoercionHole, TyVar, PredType)] -> Maybe EvTerm
evMagic ct evs = case classifyPredType $ ctEvPred $ ctEvidence ct of
  EqPred NomEq t1 t2 ->
    let ctEv = mkUnivCo (PluginProv "ghc-typelits-natnormalise") Nominal t1 t2
        (holes,tvs,preds) = unzip3 evs
        holeEvs = zipWith (\h p -> uncurry (mkHoleCo h Nominal) (getEqPredTys p))
                          holes preds
        natReflCo = mkNomReflCo typeNatKind
        forallEv = mkForAllCos (map (,natReflCo) tvs) ctEv
        finalEv = foldl mkInstCo forallEv holeEvs
    in  Just (EvCoercion finalEv)
  _ -> Nothing
