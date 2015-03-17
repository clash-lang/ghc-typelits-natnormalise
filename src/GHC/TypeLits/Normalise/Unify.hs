module GHC.TypeLits.Normalise.Unify where

-- External
import Data.Function (on)
import Data.List ((\\))

-- GHC API
import TcRnMonad
import Type
import Outputable
import TcPluginM
import UniqSet       ( UniqSet, emptyUniqSet, unionUniqSets, unitUniqSet)

-- Internal
import GHC.TypeLits.Normalise.SOP

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

-- | Apply a substitution to a single normalised expr
substsExpr :: TySubst -> Expr -> Expr
substsExpr []     u = u
substsExpr (si:s) u = substsExpr s (substExpr (siVar si) (siUnit si) u)

substExpr :: TyVar -> Expr -> Expr -> Expr
substExpr _ _  (Lit i)      = Lit i
substExpr tv e (Var tv')
  | tv == tv'               = e
  | otherwise               = Var tv'
substExpr tv e (Op o e1 e2) = Op o (substExpr tv e e1) (substExpr tv e e2)

substsSubst :: TySubst -> TySubst -> TySubst
substsSubst s = map (\si -> si {siUnit = substsExpr s (siUnit si)})

data UnifyResult = Win TySubst | Lose | Draw TySubst

instance Outputable UnifyResult where
  ppr (Win  subst) = text "Win"  <+> ppr subst
  ppr (Draw subst) = text "Draw" <+> ppr subst
  ppr Lose         = text "Lose"

unifyNats :: Ct -> Expr -> Expr -> TcPluginM UnifyResult
unifyNats ct u0 v0 = do tcPluginTrace "unifyNats" (ppr ct $$ ppr u0 $$ ppr v0)
                        return (unifyNats' ct u0 v0)

unifyNats' :: Ct -> Expr -> Expr -> UnifyResult
unifyNats' ct u0 v0
    | eqFV u0 v0 = if uS == vS then (Win su)
                               else Lose
    | otherwise  = Draw su
  where
    uS = toSOP u0
    vS = toSOP v0
    su | isGiven (ctEvidence ct) = injective ct u0 v0
       | otherwise               = []

injective ct u0 (Var v0) = [SubstItem v0 u0 ct]
injective ct (Var u0) v0 = [SubstItem u0 v0 ct]
injective ct (Op op1 u1 u2) (Op op2 v1 v2)
  | op1 == op2
  , [u0] <- toVar u1 ++ toVar u2
  , [v0] <- toVar v1 ++ toVar v2
  = [SubstItem u0 (Var v0) ct]
injective _ _ _ = []

toVar (Var v)      = [v]
toVar (Lit _)      = []
toVar (Op _ e1 e2) = toVar e1 ++ toVar e2

isConstant (Var _)      = False
isConstant (Lit _)      = True
isConstant (Op _ e1 e2) = isConstant e1 && isConstant e2

fvExpr :: Expr -> UniqSet TyVar
fvExpr (Lit _)      = emptyUniqSet
fvExpr (Var v)      = unitUniqSet v
fvExpr (Op _ e1 e2) = fvExpr e1 `unionUniqSets` fvExpr e2

eqFV :: Expr -> Expr -> Bool
eqFV = (==) `on` fvExpr
