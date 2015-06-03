{-# LANGUAGE CPP             #-}
{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections   #-}

{-# OPTIONS_HADDOCK show-extensions #-}

{-|
Copyright  :  (C) 2015, University of Twente
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
module GHC.TypeLits.Normalise
  ( plugin )
where

-- external
import Data.IORef          (IORef, newIORef,readIORef, modifyIORef)
import Data.Maybe          (catMaybes, mapMaybe)
import GHC.TcPluginM.Extra (evByFiat, failWithProvenace, newGiven,
                            newWantedWithProvenance, tracePlugin)

-- GHC API
import Outputable (Outputable (..), (<+>), ($$), text)
import Plugins    (Plugin (..), defaultPlugin)
import TcEvidence (EvTerm)
import TcPluginM  (TcPluginM, tcPluginIO, tcPluginTrace, zonkCt)
import TcRnTypes  (Ct, TcPlugin (..), TcPluginResult(..), ctEvidence, ctEvPred,
                   ctPred, ctLoc, isGiven, isWanted, mkNonCanonical)
import TcType     (mkEqPred, typeKind)
import Type       (EqRel (NomEq), Kind, PredTree (EqPred), Type, TyVar,
                   classifyPredType, mkTyVarTy)
import TysWiredIn (typeNatKind)

-- internal
import GHC.Extra.Instances () -- Ord instance for Ct
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
          Simplified subst evs -> do
            let solved     = filter (isWanted . ctEvidence . snd) evs
            -- Create new wanted constraints
            let newWanteds = filter (isWanted . ctEvidence . siNote) subst
            discharedWanteds <- tcPluginIO (readIORef discharged)
            let existingWanteds = wanteds' ++ discharedWanteds
            newWantedConstraints <- catMaybes <$>
                                    mapM (substItemToCt existingWanteds)
                                         newWanteds
            -- update set of discharged wanteds
            tcPluginIO (modifyIORef discharged (++ newWantedConstraints))
            -- return
            return (TcPluginOk solved newWantedConstraints)
          Impossible eq -> failWithProvenace $ fromNatEquality eq

substItemToCt :: [Ct] -- ^ Existing wanteds wanted
              -> UnifyItem TyVar Type Ct
              -> TcPluginM (Maybe Ct)
substItemToCt existingWanteds si
  | isGiven (ctEvidence ct)
  = Just <$> mkNonCanonical <$> newGiven loc predicate evTm

  -- Only create new wanteds
  | predicate  `notElem` wantedPreds
  , predicateS `notElem` wantedPreds
  = Just <$> mkNonCanonical <$> newWantedWithProvenance (ctEvidence ct) predicate

  | otherwise
  = return Nothing
  where
    predicate   = mkEqPred ty1 ty2
    predicateS  = mkEqPred ty2 ty1
    wantedPreds = map ctPred existingWanteds

    ty1       = case si of
                  (SubstItem {..}) -> mkTyVarTy siVar
                  (UnifyItem {..}) -> reifySOP siLHS
    ty2       = case si of
                  (SubstItem {..}) -> reifySOP siSOP
                  (UnifyItem {..}) -> reifySOP siRHS
    ct        = siNote si
    loc       = ctLoc ct
    evTm      = evByFiat "ghc-typelits-natnormalise" ty1 ty2

type NatEquality = (Ct,CoreSOP,CoreSOP)

fromNatEquality :: NatEquality -> Ct
fromNatEquality (ct, _, _) = ct

data SimplifyResult
  = Simplified CoreUnify [(EvTerm,Ct)]
  | Impossible NatEquality

instance Outputable SimplifyResult where
  ppr (Simplified subst evs) = text "Simplified" $$ ppr subst $$ ppr evs
  ppr (Impossible eq)  = text "Impossible" <+> ppr eq

simplifyNats :: [NatEquality]
             -> TcPluginM SimplifyResult
simplifyNats eqs =
    tcPluginTrace "simplifyNats" (ppr eqs) >> simples [] [] [] eqs
  where
    simples :: CoreUnify -> [Maybe (EvTerm, Ct)] -> [NatEquality]
            -> [NatEquality] -> TcPluginM SimplifyResult
    simples subst evs _xs [] = return (Simplified subst (catMaybes evs))
    simples subst evs xs (eq@(ct,u,v):eqs') = do
      ur <- unifyNats ct (substsSOP subst u) (substsSOP subst v)
      tcPluginTrace "unifyNats result" (ppr ur)
      case ur of
        Win         -> simples subst (((,) <$> evMagic ct <*> pure ct):evs) []
                               (xs ++ eqs')
        Lose        -> return (Impossible eq)
        Draw []     -> simples subst evs (eq:xs) eqs'
        Draw subst' -> simples (substsSubst subst' subst ++ subst')
                               (((,) <$> evMagic ct <*> pure ct):evs)
                               [] (xs ++ eqs')

-- Extract the Nat equality constraints
toNatEquality :: Ct -> Maybe NatEquality
toNatEquality ct = case classifyPredType $ ctEvPred $ ctEvidence ct of
    EqPred NomEq t1 t2
      | isNatKind (typeKind t1) || isNatKind (typeKind t1)
      -> Just (ct,normaliseNat t1,normaliseNat t2)
    _ -> Nothing
  where
    isNatKind :: Kind -> Bool
    isNatKind = (== typeNatKind)

evMagic :: Ct -> Maybe EvTerm
evMagic ct = case classifyPredType $ ctEvPred $ ctEvidence ct of
  EqPred NomEq t1 t2 -> Just (evByFiat "ghc-typelits-natnormalise" t1 t2)
  _                  -> Nothing
