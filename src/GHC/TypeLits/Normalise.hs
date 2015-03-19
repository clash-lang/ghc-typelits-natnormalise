{-# LANGUAGE RecordWildCards #-}
module GHC.TypeLits.Normalise
  ( plugin )
where

-- normal
import Data.Either
import Data.Maybe

-- GHC API
import FastString
import Coercion
import Outputable
import Plugins

import TcEvidence
import TcPluginM
import TcRnTypes
import TcType

import TcTypeNats

import Type
import TyCon
import TypeRep
import TysWiredIn

import qualified TcMType

-- local
import GHC.TypeLits.Normalise.SOP
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
decideEqualSOP _ givens _deriveds []      = return (TcPluginOk [] [])
decideEqualSOP _ givens _deriveds wanteds = do
    let (unit_wanteds, _) = partitionEithers $ map toNatEquality wanteds
    case unit_wanteds of
      [] -> return (TcPluginOk [] [])
      _  -> do
        (unit_givens, _) <- partitionEithers . map toNatEquality <$> mapM zonkCt givens
        sr <- simplifyNats (unit_givens ++ unit_wanteds)
        tcPluginTrace "normalised" (ppr sr)
        case sr of
          Simplified evs        -> return (TcPluginOk (filter (isWanted . ctEvidence . snd) evs) [])
          Impossible (ct, u, v) -> return (TcPluginContradiction [ct])

type NatEquality = (Ct,SOP,SOP)

fromNatEquality :: NatEquality -> Ct
fromNatEquality (ct, _, _) = ct

substItemToCt :: SubstItem -> TcPluginM Ct
substItemToCt si
    | isGiven (ctEvidence ct) = return $ mkNonCanonical $ CtGiven predicate (evByFiat "typelit_normalise" (ty1,ty2)) loc
    | otherwise               = newSimpleWanted (ctLocOrigin loc) predicate
  where
    predicate = mkEqPred ty1 ty2
    ty1       = mkTyVarTy (siVar si)
    ty2       = reifySOP (siSOP si)
    ct        = siCt si
    loc       = ctLoc ct

data SimplifyResult
  = Simplified [(EvTerm,Ct)]
  | Impossible NatEquality

instance Outputable SimplifyResult where
  ppr (Simplified evs) = text "Simplified" $$ ppr evs
  ppr (Impossible eq)  = text "Impossible" <+> ppr eq

simplifyNats :: [NatEquality] -> TcPluginM SimplifyResult
simplifyNats eqs = tcPluginTrace "simplifyNats" (ppr eqs) >> simples [] [] [] eqs
  where
    simples :: TySubst -> [Maybe (EvTerm, Ct)] -> [NatEquality] -> [NatEquality] -> TcPluginM SimplifyResult
    simples subst evs xs [] = return (Simplified (catMaybes evs))
    simples subst evs xs (eq@(ct,u,v):eqs) = do
      ur <- unifyNats ct (substsSOP subst u) (substsSOP subst v)
      tcPluginTrace "unifyNats result" (ppr ur)
      case ur of
        Win         -> simples subst (((,) <$> evMagic ct <*> pure ct):evs) [] (xs ++ eqs)
        Lose        -> return  (Impossible eq)
        Draw []     -> simples subst evs (eq:xs) eqs
        Draw subst' -> simples (substsSubst subst' subst ++ subst') evs [eq] (xs ++ eqs)

-- Extract the Nat equality constraints
toNatEquality :: Ct -> Either NatEquality Ct
toNatEquality ct = case classifyPredType $ ctEvPred $ ctEvidence ct of
    EqPred NomEq t1 t2
      | isNatKind (typeKind t1) || isNatKind (typeKind t1)
      , Just u1 <- normaliseNat t1
      , Just u2 <- normaliseNat t2 -> Left (ct, u1, u2)
    _                              -> Right ct
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
