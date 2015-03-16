{-# LANGUAGE RecordWildCards #-}
module GHC.TypeLits.Normalise
  ( plugin )
where

-- normal
import Data.Either

-- GHC API
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
        tcPluginTrace "normalise wanteds" (ppr unit_wanteds)
        tcPluginTrace "normalise givens" (ppr unit_givens)
        return (TcPluginOk [] [])

data Op = Add | Sub | Mul | Exp
  deriving Eq

data Expr
  = Lit Integer
  | Var TyVar
  | Op Op Expr Expr
  deriving Eq

data Symbol
  = I Integer
  | V TyVar
  | E SOP Product
  deriving (Eq,Ord)

newtype Product = P { unP :: [Symbol] }
  deriving (Eq,Ord)

newtype SOP = S { unS :: [Product] }
  deriving (Eq,Ord)

instance Outputable Expr where
  ppr (Lit i) = integer i
  ppr (Var v) = ppr v
  ppr (Op op e1 e2) = parens (ppr e1) <+> parens (ppr e2)

instance Outputable Op where
  ppr Add = text "+"
  ppr Sub = text "-"
  ppr Mul = text "*"
  ppr Exp = text "^"

instance Outputable SOP where
  ppr = hcat . punctuate (text " + ") . map ppr . unS

instance Outputable Product where
  ppr = hcat . punctuate (text " * ") . map ppr . unP

instance Outputable Symbol where
  ppr (I i)   = integer i
  ppr (V s)   = ppr s
  ppr (E b e) = case (pprSimple b, pprSimple (S [e])) of
                  (bS,eS) -> bS <+> text "^" <+> eS
    where
      pprSimple (S [P [I i]]) = integer i
      pprSimple (S [P [V v]]) = ppr v
      pprSimple sop           = text "(" <+> ppr sop <+> text ")"

type NatEquality = (Ct,Expr,Expr)

fromNatEquality :: NatEquality -> Ct
fromNatEquality (ct, _, _) = ct

-- | A substitution is essentially a list of (variable, unit) pairs,
-- but we keep the original 'Ct' that lead to the substitution being
-- made, for use when turning the substitution back into constraints.
type TySubst = [SubstItem]

data SubstItem = SubstItem { siVar    :: TyVar
                           , siUnit   :: Expr
                           , siCt     :: Ct
                           }

instance Outputable SubstItem where
  ppr si = ppr (siVar si) <+> text " := " <+> ppr (siUnit si)

data SimplifyResult
  = Simplified [TyVar] TySubst [(EvTerm,Ct)] [NatEquality]
  | Impossible NatEquality [NatEquality]

instance Outputable SimplifyResult where
  ppr (Simplified tvs subst evs eqs) = text "Simplified" $$ ppr tvs $$ ppr subst $$ ppr evs $$ ppr eqs
  ppr (Impossible eq eqs)            = text "Impossible" <+> ppr eq <+> ppr eqs

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
