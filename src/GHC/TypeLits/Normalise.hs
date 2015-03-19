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
import TcPluginM  (TcPluginM, tcPluginTrace, zonkCt)
import TcRnTypes  (Ct, TcPlugin(..), TcPluginResult(..), ctEvidence, ctEvPred,
                   isWanted)
import TcType     (typeKind)
import Type       (EqRel (NomEq), Kind, PredTree (EqPred), Type,
                   classifyPredType)
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
          Simplified evs -> return (TcPluginOk
                                      (filter (isWanted . ctEvidence . snd) evs)
                                      [])
          Impossible eq  -> return (TcPluginContradiction [fromNatEquality eq])

type NatEquality = (Ct,CoreSOP,CoreSOP)

fromNatEquality :: NatEquality -> Ct
fromNatEquality (ct, _, _) = ct

data SimplifyResult
  = Simplified [(EvTerm,Ct)]
  | Impossible NatEquality

instance Outputable SimplifyResult where
  ppr (Simplified evs) = text "Simplified" $$ ppr evs
  ppr (Impossible eq)  = text "Impossible" <+> ppr eq

simplifyNats :: [NatEquality] -> TcPluginM SimplifyResult
simplifyNats eqs = tcPluginTrace "simplifyNats" (ppr eqs) >> simples [] [] [] eqs
  where
    simples :: CoreSubst -> [Maybe (EvTerm, Ct)] -> [NatEquality]
            -> [NatEquality] -> TcPluginM SimplifyResult
    simples _subst evs _xs [] = return (Simplified (catMaybes evs))
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
evMagic :: Ct -> Maybe EvTerm
evMagic ct = case classifyPredType $ ctEvPred $ ctEvidence ct of
    EqPred NomEq t1 t2 -> Just (evByFiat "tylits_magic" (t1, t2))
    _                  -> Nothing

evByFiat :: String -> (Type, Type) -> EvTerm
evByFiat name (t1,t2) = EvCoercion $ TcCoercion
                      $ mkUnivCo (fsLit name) Nominal t1 t2
