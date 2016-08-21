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
import Control.Monad       (replicateM)
import Data.List           (intersect)
import Data.Maybe          (mapMaybe)
import GHC.TcPluginM.Extra (tracePlugin)

-- GHC API
import Outputable (Outputable (..), (<+>), ($$), text)
import Plugins    (Plugin (..), defaultPlugin)
import TcEvidence (EvTerm (..))
import TcPluginM  (TcPluginM, tcPluginTrace, zonkCt)
import TcRnTypes  (Ct, TcPlugin (..), TcPluginResult(..), ctEvidence, ctEvPred,
                   isWanted, mkNonCanonical)
import Type       (EqRel (NomEq), Kind, PredTree (EqPred), PredType,
                   classifyPredType, eqType, getEqPredTys, mkTyVarTy)
import TysWiredIn (typeNatKind)

import Coercion   (CoercionHole, Role (..), mkForAllCos, mkHoleCo, mkInstCo,
                   mkNomReflCo, mkUnivCo)
import TcPluginM  (newCoercionHole, newFlexiTyVar)
import TcRnTypes  (CtEvidence (..), CtLoc, TcEvDest (..), ctLoc)
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
          Simplified evs -> do
            let solved = filter (isWanted . ctEvidence . (\(_,x,_) -> x)) evs
                (solved',newWanteds) = second concat . unzip $ map evItemToCt solved
            return (TcPluginOk solved' newWanteds)
          Impossible eq -> return (TcPluginContradiction [fromNatEquality eq])

evItemToCt :: (EvTerm,Ct,[(CoreUnify,CoercionHole)])
           -> ((EvTerm,Ct),[Ct])
evItemToCt (ev,ct,subst) = ((ev,ct),newWanteds)
  where
    newWanteds = map (substItemToCt (ctLoc ct)) subst

substItemToCt :: CtLoc
              -> (CoreUnify,CoercionHole)
              -> Ct
substItemToCt ct_loc (si,hole) = mkNonCanonical (CtWanted predicate (HoleDest hole) ct_loc)
  where
    predicate = unifyItemToPredType si

unifyItemToPredType :: CoreUnify -> PredType
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

data SimplifyResult
  = Simplified [(EvTerm,Ct,[(CoreUnify,CoercionHole)])]
  | Impossible (Either NatEquality NatInEquality)

instance Outputable SimplifyResult where
  ppr (Simplified evs) = text "Simplified" $$ ppr evs
  ppr (Impossible eq)  = text "Impossible" <+> ppr eq

simplifyNats :: [Either NatEquality NatInEquality]
             -> TcPluginM SimplifyResult
simplifyNats eqs =
    tcPluginTrace "simplifyNats" (ppr eqs) >> simples [] [] [] eqs
  where
    simples :: [CoreUnify]
            -> [(EvTerm, Ct, [(CoreUnify,CoercionHole)])]
            -> [Either NatEquality NatInEquality]
            -> [Either NatEquality NatInEquality]
            -> TcPluginM SimplifyResult
    simples _subst evs _xs [] = return (Simplified evs)
    simples subst evs xs (eq@(Left (ct,u,v)):eqs') = do
      ur <- unifyNats ct (substsSOP subst u) (substsSOP subst v)
      tcPluginTrace "unifyNats result" (ppr ur)
      case ur of
        Win -> do
          evs' <- maybe evs ((:evs) . (,ct,[]) . fst) <$> evMagic ct []
          simples subst evs' [] (xs ++ eqs')
        Lose -> return (Impossible eq)
        Draw [] -> simples subst evs (eq:xs) eqs'
        Draw subst' -> do
          evM <- evMagic ct (map unifyItemToPredType subst')
          case evM of
            Nothing -> simples subst evs xs eqs'
            Just (ev,holes) ->
              let subst'' = zip subst' holes
              in  simples (substsSubst subst' subst ++ subst')
                  ((ev,ct,subst''):evs) [] (xs ++ eqs')
    simples subst evs xs (eq@(Right (ct,u)):eqs') =
      case isNatural u of
        Just True  -> do
          evs' <- maybe evs ((:evs) . (,ct,[]) . fst) <$> evMagic ct []
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

evMagic :: Ct -> [PredType] -> TcPluginM (Maybe (EvTerm, [CoercionHole]))
evMagic ct preds = case classifyPredType $ ctEvPred $ ctEvidence ct of
  EqPred NomEq t1 t2 -> do
    holes <- replicateM (length preds) newCoercionHole
    let ctEv    = mkUnivCo (PluginProv "ghc-typelits-natnormalise") Nominal t1 t2
        holeEvs = zipWith (\h p -> uncurry (mkHoleCo h Nominal) (getEqPredTys p)) holes preds
        natReflCo = mkNomReflCo typeNatKind
        natCoBndr = (,natReflCo) <$> (newFlexiTyVar typeNatKind)
    forallEv <- mkForAllCos <$> (replicateM (length preds) natCoBndr) <*> pure ctEv
    let finalEv = foldl mkInstCo forallEv holeEvs
    return (Just (EvCoercion finalEv,holes))
  _ -> return Nothing
