{-|
Copyright  :  (C) 2015-2016, University of Twente,
                  2017     , QBayLogic B.V.
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

{-# LANGUAGE CPP             #-}
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
import Data.Either         (rights)
import Data.List           (intersect)
import Data.Maybe          (mapMaybe)
import GHC.TcPluginM.Extra (tracePlugin)
#if MIN_VERSION_ghc(8,4,0)
import GHC.TcPluginM.Extra (flattenGivens)
#endif

-- GHC API
#if MIN_VERSION_ghc(8,5,0)
import CoreSyn    (Expr (..))
#endif
import Outputable (Outputable (..), (<+>), ($$), text)
import Plugins    (Plugin (..), defaultPlugin)
import TcEvidence (EvTerm (..))
#if !MIN_VERSION_ghc(8,4,0)
import TcPluginM  (zonkCt)
#endif
import TcPluginM  (TcPluginM, tcPluginTrace)
import TcRnTypes  (Ct, TcPlugin (..), TcPluginResult(..), ctEvidence, ctEvPred,
                   isWanted, mkNonCanonical)
import Type       (EqRel (NomEq), Kind, PredTree (EqPred), PredType,
                   classifyPredType, eqType, getEqPredTys, mkTyVarTy)
import TysWiredIn (typeNatKind)

import Coercion   (CoercionHole, Role (..), mkForAllCos, mkHoleCo, mkInstCo,
                   mkNomReflCo, mkUnivCo)
import TcPluginM  (newCoercionHole, newFlexiTyVar)
import TcRnTypes  (CtEvidence (..), CtLoc, TcEvDest (..), ctLoc)
#if MIN_VERSION_ghc(8,2,0)
import TcRnTypes  (ShadowInfo (WDeriv))
#endif
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
#if MIN_VERSION_ghc(8,4,0)
        let unit_givens = mapMaybe toNatEquality (givens ++ flattenGivens givens)
#else
        unit_givens <- mapMaybe toNatEquality <$> mapM zonkCt givens
#endif
        sr <- simplifyNats unit_givens unit_wanteds
        tcPluginTrace "normalised" (ppr sr)
        case sr of
          Simplified evs -> do
            let solved = filter (isWanted . ctEvidence . (\((_,x),_) -> x)) evs
                (solved',newWanteds) = second concat (unzip solved)
            return (TcPluginOk solved' newWanteds)
          Impossible eq -> return (TcPluginContradiction [fromNatEquality eq])

type NatEquality   = (Ct,CoreSOP,CoreSOP)
type NatInEquality = (Ct,CoreSOP)

fromNatEquality :: Either NatEquality NatInEquality -> Ct
fromNatEquality (Left  (ct, _, _)) = ct
fromNatEquality (Right (ct, _))    = ct

data SimplifyResult
  = Simplified [((EvTerm,Ct),[Ct])]
  | Impossible (Either NatEquality NatInEquality)

instance Outputable SimplifyResult where
  ppr (Simplified evs) = text "Simplified" $$ ppr evs
  ppr (Impossible eq)  = text "Impossible" <+> ppr eq

simplifyNats
  :: [Either NatEquality NatInEquality]
  -- ^ Given constraints
  -> [Either NatEquality NatInEquality]
  -- ^ Wanted constraints
  -> TcPluginM SimplifyResult
simplifyNats eqsG eqsW =
    let eqs = eqsG ++ eqsW
    in  tcPluginTrace "simplifyNats" (ppr eqs) >> simples [] [] [] eqs
  where
    simples :: [CoreUnify]
            -> [((EvTerm, Ct), [Ct])]
            -> [Either NatEquality NatInEquality]
            -> [Either NatEquality NatInEquality]
            -> TcPluginM SimplifyResult
    simples _subst evs _xs [] = return (Simplified evs)
    simples subst evs xs (eq@(Left (ct,u,v)):eqs') = do
      ur <- unifyNats ct (substsSOP subst u) (substsSOP subst v)
      tcPluginTrace "unifyNats result" (ppr ur)
      case ur of
        Win -> do
          evs' <- maybe evs (:evs) <$> evMagic ct []
          simples subst evs' [] (xs ++ eqs')
        Lose -> return (Impossible eq)
        Draw [] -> simples subst evs (eq:xs) eqs'
        Draw subst' -> do
          evM <- evMagic ct (map unifyItemToPredType subst')
          case evM of
            Nothing -> simples subst evs xs eqs'
            Just ev ->
              simples (substsSubst subst' subst ++ subst')
                      (ev:evs) [] (xs ++ eqs')
    simples subst evs xs (eq@(Right (ct,u)):eqs') = do
      let u' = substsSOP subst u
      tcPluginTrace "unifyNats(ineq) results" (ppr (ct,u'))
      case isNatural u' of
        Just True  -> do
          evs' <- maybe evs (:evs) <$> evMagic ct []
          simples subst evs' xs eqs'
        Just False -> return (Impossible eq)
        Nothing    ->
          -- This inequality is either a given constraint, or it is a wanted
          -- constraint, which in normal form is equal to another given
          -- constraint, hence it can be solved.
          if u `elem` (map snd (rights eqsG))
             then do
               evs' <- maybe evs (:evs) <$> evMagic ct []
               simples subst evs' xs eqs'
             else simples subst evs (eq:xs) eqs'

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

evMagic :: Ct -> [PredType] -> TcPluginM (Maybe ((EvTerm, Ct), [Ct]))
evMagic ct preds = case classifyPredType $ ctEvPred $ ctEvidence ct of
  EqPred NomEq t1 t2 -> do
#if MIN_VERSION_ghc(8,4,1)
    holes <- mapM (newCoercionHole . uncurry mkPrimEqPred . getEqPredTys) preds
#else
    holes <- replicateM (length preds) newCoercionHole
#endif
    let newWanted = zipWith (unifyItemToCt (ctLoc ct)) preds holes
        ctEv      = mkUnivCo (PluginProv "ghc-typelits-natnormalise") Nominal t1 t2
#if MIN_VERSION_ghc(8,4,1)
        holeEvs   = map mkHoleCo holes
#else
        holeEvs   = zipWith (\h p -> uncurry (mkHoleCo h Nominal) (getEqPredTys p)) holes preds
#endif
        natReflCo = mkNomReflCo typeNatKind
        natCoBndr = (,natReflCo) <$> (newFlexiTyVar typeNatKind)
    forallEv <- mkForAllCos <$> (replicateM (length preds) natCoBndr) <*> pure ctEv
    let finalEv = foldl mkInstCo forallEv holeEvs
#if MIN_VERSION_ghc(8,5,0)
    return (Just ((EvExpr (Coercion finalEv), ct),newWanted))
#else
    return (Just ((EvCoercion finalEv, ct),newWanted))
#endif
  _ -> return Nothing

unifyItemToCt :: CtLoc
              -> PredType
              -> CoercionHole
              -> Ct
unifyItemToCt loc pred_type hole =
  mkNonCanonical
    (CtWanted
      pred_type
      (HoleDest hole)
#if MIN_VERSION_ghc(8,2,0)
      WDeriv
#endif
      loc)
