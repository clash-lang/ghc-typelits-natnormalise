module GHC.TypeLits.Normalise.Unify where

-- External
import Data.Function (on)
import Data.List ((\\),intersect)

-- GHC API
import TcRnMonad
import Type
import Outputable
import TcPluginM
import UniqSet       ( UniqSet, emptyUniqSet, unionUniqSets, unitUniqSet, unionManyUniqSets)

-- Internal
import GHC.TypeLits.Normalise.SOP

-- | A substitution is essentially a list of (variable, unit) pairs,
-- but we keep the original 'Ct' that lead to the substitution being
-- made, for use when turning the substitution back into constraints.
type TySubst = [SubstItem]

data SubstItem = SubstItem { siVar    :: TyVar
                           , siSOP   :: SOP
                           , siCt     :: Ct
                           }

instance Outputable SubstItem where
  ppr si = ppr (siVar si) <+> text " := " <+> ppr (siSOP si)

-- | Apply a substitution to a single normalised expr
substsSOP :: TySubst -> SOP -> SOP
substsSOP []     u = u
substsSOP (si:s) u = substsSOP s (substSOP (siVar si) (siSOP si) u)

substSOP :: TyVar -> SOP -> SOP -> SOP
substSOP tv e = foldr1 mergeSOPAdd . map (substProduct tv e) . unS

substProduct :: TyVar -> SOP -> Product -> SOP
substProduct tv e = foldr1 mergeSOPMul . map (substSymbol tv e) . unP

substSymbol :: TyVar -> SOP -> Symbol -> SOP
substSymbol _ _ (I i)    = S [P [I i]]
substSymbol tv e (V tv')
  | tv == tv'            = e
  | otherwise            = S [P [V tv']]
substSymbol tv e (E s p) = expandExp (substSOP tv e s) (substProduct tv e p)

substsSubst :: TySubst -> TySubst -> TySubst
substsSubst s = map (\si -> si {siSOP = substsSOP s (siSOP si)})

data UnifyResult = Win | Lose | Draw TySubst

instance Outputable UnifyResult where
  ppr Win          = text "Win"
  ppr (Draw subst) = text "Draw" <+> ppr subst
  ppr Lose         = text "Lose"


unifyNats :: Ct -> SOP -> SOP -> TcPluginM UnifyResult
unifyNats ct u v = do
  tcPluginTrace "unifyNats" (ppr ct $$ ppr u $$ ppr v)
  unifyNats' ct u v

unifyNats' :: Ct -> SOP -> SOP -> TcPluginM UnifyResult
unifyNats' ct u v
    | eqFV u v  = if u == v then return Win else return Lose
    | otherwise = Draw <$> subst
  where
    subst | isGiven (ctEvidence ct) = unifiers ct u v
          | otherwise               = pure []

unifiers :: Ct -> SOP -> SOP -> TcPluginM TySubst
unifiers ct (S [P [V x]]) (S [])        = return [SubstItem x (S [P [I 0]]) ct]
unifiers ct (S [])        (S [P [V x]]) = return [SubstItem x (S [P [I 0]]) ct]
unifiers ct (S [P [V x]]) s             = return [SubstItem x s     ct]
unifiers ct s             (S [P [V x]]) = return [SubstItem x s     ct]
unifiers ct (S ps1)       (S ps2)
    | null psx  = return []
    | otherwise = unifiers ct (S (ps1 \\ psx)) (S (ps2 \\ psx))
  where
    psx = intersect ps1 ps2


fvSOP :: SOP -> UniqSet TyVar
fvSOP = unionManyUniqSets . map fvProduct . unS

fvProduct :: Product -> UniqSet TyVar
fvProduct = unionManyUniqSets . map fvSymbol . unP

fvSymbol :: Symbol -> UniqSet TyVar
fvSymbol (I i)   = emptyUniqSet
fvSymbol (V v)   = unitUniqSet v
fvSymbol (E s p) = fvSOP s `unionUniqSets` fvProduct p

eqFV :: SOP -> SOP -> Bool
eqFV = (==) `on` fvSOP
