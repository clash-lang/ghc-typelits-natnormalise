{-# LANGUAGE RecordWildCards #-}
module GHC.TypeLits.Normalise
  ( plugin )
where

-- normal
import Data.Either

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
normalisePlugin = tracePlugin "ghc-tynat-normalise" $
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
          Simplified subst evs  -> TcPluginOk (filter (isWanted . ctEvidence . snd) evs)
                                              <$> mapM substItemToCt (filter (isWanted . ctEvidence . siCt) subst)
          Impossible (ct, u, v) -> return (TcPluginContradiction [ct])

type NatEquality = (Ct,Expr,Expr)

fromNatEquality :: NatEquality -> Ct
fromNatEquality (ct, _, _) = ct

substItemToCt :: SubstItem -> TcPluginM Ct
substItemToCt si
    | isGiven (ctEvidence ct) = return $ mkNonCanonical $ CtGiven predicate (evByFiat "typelit_normalise" (ty1,ty2)) loc
    | otherwise               = newSimpleWanted (ctLocOrigin loc) predicate
  where
    predicate = mkEqPred ty1 ty2
    ty1       = mkTyVarTy (siVar si)
    ty2       = reifyUnit (siUnit si)
    ct        = siCt si
    loc       = ctLoc ct

evByFiat :: String -> (Type, Type) -> EvTerm
evByFiat name (t1,t2) = EvCoercion $ TcCoercion $ mkUnivCo (fsLit name) Nominal t1 t2

data SimplifyResult
  = Simplified TySubst [(EvTerm,Ct)]
  | Impossible NatEquality

instance Outputable SimplifyResult where
  ppr (Simplified subst evs) = text "Simplified" $$ ppr subst $$ ppr evs
  ppr (Impossible eq)        = text "Impossible" <+> ppr eq

simplifyNats :: [NatEquality] -> TcPluginM SimplifyResult
simplifyNats eqs = tcPluginTrace "simplifyNats" (ppr eqs) >> simples [] [] [] eqs
  where
    simples :: TySubst -> [(EvTerm, Ct)] -> [NatEquality] -> [NatEquality] -> TcPluginM SimplifyResult
    simples subst evs xs [] = return (Simplified subst evs)
    simples subst evs xs (eq@(ct,u,v):eqs) = do
      ur <- unifyNats ct (substsExpr subst u) (substsExpr subst v)
      tcPluginTrace "unifyNats result" (ppr ur)
      case ur of
        Win         -> simples subst ((evMagic ct,ct):evs) [] (xs ++ eqs)
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

isNatKind :: Kind -> Bool
isNatKind = (== typeNatKind)

normaliseNat :: Type -> Maybe Expr
normaliseNat ty | Just ty1 <- tcView ty = normaliseNat ty1
normaliseNat (TyVarTy v)          = pure (Var v)
normaliseNat (LitTy (NumTyLit i)) = pure (Lit i)
normaliseNat (TyConApp tc tys)
  | tc == typeNatAddTyCon, [x,y] <- tys = Op Add <$> normaliseNat x <*> normaliseNat y
  | tc == typeNatSubTyCon, [x,y] <- tys = Op Sub <$> normaliseNat x <*> normaliseNat y
  | tc == typeNatMulTyCon, [x,y] <- tys = Op Mul <$> normaliseNat x <*> normaliseNat y
  | tc == typeNatExpTyCon, [x,y] <- tys = Op Exp <$> normaliseNat x <*> normaliseNat y
  | otherwise                           = Nothing

-- Utils
tracePlugin :: String -> TcPlugin -> TcPlugin
tracePlugin s TcPlugin{..} = TcPlugin { tcPluginInit  = traceInit
                                      , tcPluginSolve = traceSolve
                                      , tcPluginStop  = traceStop
                                      }
  where
    traceInit    = tcPluginTrace ("tcPluginInit " ++ s) empty >> tcPluginInit
    traceStop  z = tcPluginTrace ("tcPluginStop " ++ s) empty >> tcPluginStop z

    traceSolve z given derived wanted = do
        tcPluginTrace ("tcPluginSolve start " ++ s)
                          (text "given   =" <+> ppr given
                        $$ text "derived =" <+> ppr derived
                        $$ text "wanted  =" <+> ppr wanted)
        r <- tcPluginSolve z given derived wanted
        case r of
          TcPluginOk solved new     -> tcPluginTrace ("tcPluginSolve ok " ++ s)
                                           (text "solved =" <+> ppr solved
                                         $$ text "new    =" <+> ppr new)
          TcPluginContradiction bad -> tcPluginTrace ("tcPluginSolve contradiction " ++ s)
                                           (text "bad =" <+> ppr bad)
        return r

newSimpleWanted :: CtOrigin -> PredType -> TcPluginM Ct
newSimpleWanted orig = unsafeTcPluginTcM . TcMType.newSimpleWanted orig

evMagic :: Ct -> EvTerm
evMagic ct = case classifyPredType $ ctEvPred $ ctEvidence ct of
    EqPred NomEq t1 t2 -> evByFiat "tylits_magic" (t1, t2)
