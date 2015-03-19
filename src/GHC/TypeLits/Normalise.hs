{-# LANGUAGE TupleSections #-}

{-# OPTIONS_HADDOCK show-extensions #-}

{-|
Copyright  :  (C) 2015, University of Twente
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>
-}
module GHC.TypeLits.Normalise
  ( plugin )
where

-- external
import Data.Maybe (catMaybes, mapMaybe)

-- GHC API
import Coercion   (Role (Nominal), mkUnivCo)
import FastString (fsLit)
import Outputable (Outputable (..), (<+>), ($$), text)
import Plugins    (Plugin (..), defaultPlugin)
import TcEvidence (EvTerm (EvCoercion), TcCoercion (..))
import TcPluginM  (TcPluginM, tcPluginTrace, unsafeTcPluginTcM, zonkCt)
import qualified  TcMType
import TcRnTypes  (Ct, CtEvidence (..), CtOrigin, TcPlugin(..),
                   TcPluginResult(..), ctEvidence, ctEvPred,
                   ctLoc, ctLocOrigin, isGiven, isWanted mkNonCanonical)
import TcType     (mkEqPred, typeKind)
import Type       (EqRel (NomEq), Kind, PredTree (EqPred), PredType, Type,
                   TyVar, classifyPredType, mkTyVarTy)
import TysWiredIn (typeNatKind)

-- internal
import GHC.TypeLits.Normalise.Unify

plugin :: Plugin
plugin = defaultPlugin { tcPlugin = const $ Just normalisePlugin }

normalisePlugin :: TcPlugin
normalisePlugin =
  TcPlugin { tcPluginInit  = return ()
           , tcPluginSolve = decideEqualSOP
           , tcPluginStop  = const (return ())
           }

decideEqualSOP :: () -> [Ct] -> [Ct] -> [Ct] -> TcPluginM TcPluginResult
decideEqualSOP _ _givens _deriveds []      = return (TcPluginOk [] [])
decideEqualSOP _ givens  _deriveds wanteds = do
    let unit_wanteds = mapMaybe toNatEquality wanteds
    case unit_wanteds of
      [] -> return (TcPluginOk [] [])
      _  -> do
        unit_givens <- mapMaybe toNatEquality <$> mapM zonkCt givens
        sr <- simplifyNats (unit_givens ++ unit_wanteds)
        tcPluginTrace "normalised" (ppr sr)
        case sr of
          Simplified subst evs ->
            TcPluginOk (filter (isWanted . ctEvidence . snd) evs) <$>
              mapM substItemToCt (filter (isWanted . ctEvidence . siNote) subst)
          Impossible eq  -> return (TcPluginContradiction [fromNatEquality eq])

substItemToCt :: SubstItem TyVar Ct -> TcPluginM Ct
substItemToCt si
  | isGiven (ctEvidence ct) = return $ mkNonCanonical
                                     $ CtGiven predicate
                                               (evByFiat "units" (ty1, ty2)) loc
  | otherwise               = newSimpleWanted (ctLocOrigin loc) predicate
  where
    predicate = mkEqPred ty1 ty2
    ty1  = mkTyVarTy (siVar si)
    ty2  = reifySOP (siSOP si)
    ct   = siNote si
    loc  = ctLoc ct

type NatEquality = (Ct,CoreSOP,CoreSOP)

fromNatEquality :: NatEquality -> Ct
fromNatEquality (ct, _, _) = ct

data SimplifyResult
  = Simplified CoreSubst [(EvTerm,Ct)]
  | Impossible NatEquality

instance Outputable SimplifyResult where
  ppr (Simplified subst evs) = text "Simplified" $$ ppr subst $$ ppr evs
  ppr (Impossible eq)  = text "Impossible" <+> ppr eq

simplifyNats :: [NatEquality] -> TcPluginM SimplifyResult
simplifyNats eqs = tcPluginTrace "simplifyNats" (ppr eqs) >> simples [] [] [] eqs
  where
    simples :: CoreSubst -> [Maybe (EvTerm, Ct)] -> [NatEquality]
            -> [NatEquality] -> TcPluginM SimplifyResult
    simples subst evs _xs [] = return (Simplified subst (catMaybes evs))
    simples subst evs xs (eq@(ct,u,v):eqs') = do
      ur <- unifyNats ct (substsSOP subst u) (substsSOP subst v)
      tcPluginTrace "unifyNats result" (ppr ur)
      case ur of
        Win         -> simples subst (((,) <$> evMagic ct <*> pure ct):evs) []
                               (xs ++ eqs')
        Lose        -> return  (Impossible eq)
        Draw []     -> simples subst evs (eq:xs) eqs'
        Draw subst' -> simples (substsSubst subst' subst ++ subst') evs [eq]
                               (xs ++ eqs')

-- Extract the Nat equality constraints
toNatEquality :: Ct -> Maybe NatEquality
toNatEquality ct = case classifyPredType $ ctEvPred $ ctEvidence ct of
    EqPred NomEq t1 t2
      | isNatKind (typeKind t1) || isNatKind (typeKind t1)
      -> (ct,,) <$> normaliseNat t1 <*> normaliseNat t2
    _ -> Nothing
  where
    isNatKind :: Kind -> Bool
    isNatKind = (== typeNatKind)

-- Utils
newSimpleWanted :: CtOrigin -> PredType -> TcPluginM Ct
newSimpleWanted orig = unsafeTcPluginTcM . TcMType.newSimpleWanted orig

evMagic :: Ct -> Maybe EvTerm
evMagic ct = case classifyPredType $ ctEvPred $ ctEvidence ct of
    EqPred NomEq t1 t2 -> Just (evByFiat "tylits_magic" (t1, t2))
    _                  -> Nothing

evByFiat :: String -> (Type, Type) -> EvTerm
evByFiat name (t1,t2) = EvCoercion $ TcCoercion
                      $ mkUnivCo (fsLit name) Nominal t1 t2
