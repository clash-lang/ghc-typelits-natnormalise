{-# OPTIONS_GHC -fno-warn-unused-imports #-}

{-|
Copyright  :  (C) 2015, University of Twente
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>
-}
module GHC.TypeLits.Normalise.Unify
  ( -- * 'Nat' expressions \<-\> 'SOP' terms
    CoreSOP
  , normaliseNat
  , reifySOP
    -- * Substitution on 'SOP' terms
  , SubstItem (..)
  , TySubst
  , CoreSubst
  , substsSOP
  , substsSubst
    -- * Find unifiers
  , UnifyResult (..)
  , unifyNats
  , unifiers
    -- * Free variables in 'SOP' terms
  , fvSOP
  )
where

-- External
import Data.Function (on)
import Data.List     ((\\), intersect)

-- GHC API
import Outputable    (Outputable (..), (<+>), ($$), text)
import TcPluginM     (TcPluginM, tcPluginTrace)
import TcRnMonad     (Ct, ctEvidence, isGiven)
import TcTypeNats    (typeNatAddTyCon, typeNatExpTyCon, typeNatMulTyCon,
                      typeNatSubTyCon)
import Type          (TyVar, mkNumLitTy, mkTyConApp, mkTyVarTy, tcView)
import TypeRep       (Type (..), TyLit (..))
import UniqSet       (UniqSet, unionManyUniqSets, emptyUniqSet, unionUniqSets,
                      unitUniqSet)

-- Internal
import GHC.Type.Instances () -- Ord instance for Type
import GHC.TypeLits.Normalise.SOP

-- Used for haddock
import GHC.TypeLits (Nat)

-- | 'SOP' with 'TyVar' variables
type CoreSOP     = SOP TyVar Type
type CoreProduct = Product TyVar Type
type CoreSymbol  = Symbol TyVar Type

-- | Convert a type of /kind/ 'GHC.TypeLits.Nat' to an 'SOP' term, but
-- only when the type is constructed out of:
--
-- * literals
-- * type variables
-- * Applications of the arithmetic operators @(+,-,*,^)@
normaliseNat :: Type -> CoreSOP
normaliseNat ty | Just ty1 <- tcView ty = normaliseNat ty1
normaliseNat (TyVarTy v)          = S [P [V v]]
normaliseNat (LitTy (NumTyLit i)) = S [P [I i]]
normaliseNat (TyConApp tc [x,y])
  | tc == typeNatAddTyCon = mergeSOPAdd (normaliseNat x) (normaliseNat y)
  | tc == typeNatSubTyCon = mergeSOPAdd (normaliseNat x)
                                        (mergeSOPMul (S [P [I (-1)]])
                                                     (normaliseNat y))
  | tc == typeNatMulTyCon = mergeSOPMul (normaliseNat x) (normaliseNat y)
  | tc == typeNatExpTyCon = normaliseExp (normaliseNat x) (normaliseNat y)
normaliseNat t = S [P [C t]]

-- | Convert a 'SOP' term back to a type of /kind/ 'GHC.TypeLits.Nat'
reifySOP :: CoreSOP -> Type
reifySOP = combineP . map negateP . unS
  where
    negateP :: CoreProduct -> Either CoreProduct CoreProduct
    negateP (P ((I i):ps)) | i < 0 = Left  (P ps)
    negateP ps                     = Right ps

    combineP :: [Either CoreProduct CoreProduct] -> Type
    combineP []     = mkNumLitTy 0
    combineP [p]    = either (\p' -> mkTyConApp typeNatSubTyCon
                                                [mkNumLitTy 0, reifyProduct p'])
                             reifyProduct p
    combineP (p:ps) = let es = combineP ps
                      in  either (\x -> mkTyConApp typeNatSubTyCon
                                                   [es, reifyProduct x])
                                 (\x -> mkTyConApp typeNatAddTyCon
                                                  [reifyProduct x, es])
                                 p

reifyProduct :: CoreProduct -> Type
reifyProduct = foldr1 (\t1 t2 -> mkTyConApp typeNatMulTyCon [t1,t2])
             . map reifySymbol . unP

reifySymbol :: CoreSymbol -> Type
reifySymbol (I i)   = mkNumLitTy i
reifySymbol (C c)   = c
reifySymbol (V v)   = mkTyVarTy v
reifySymbol (E s p) = mkTyConApp typeNatExpTyCon [reifySOP s,reifyProduct p]

-- | A substitution is essentially a list of (variable, 'SOP') pairs,
-- but we keep the original 'Ct' that lead to the substitution being
-- made, for use when turning the substitution back into constraints.
type CoreSubst     = TySubst TyVar Type Ct
type TySubst v c n = [SubstItem v c n]

data SubstItem v c n = SubstItem { siVar  :: v
                                 , siSOP  :: SOP v c
                                 , siNote :: n
                                 }

instance (Outputable v, Outputable c) => Outputable (SubstItem v c n) where
  ppr si = ppr (siVar si) <+> text " := " <+> ppr (siSOP si)

-- | Apply a substitution to a single normalised 'SOP' term
substsSOP :: (Ord v, Ord c) => TySubst v c n -> SOP v c -> SOP v c
substsSOP []     u = u
substsSOP (si:s) u = substsSOP s (substSOP (siVar si) (siSOP si) u)

substSOP :: (Ord v, Ord c) => v -> SOP v c -> SOP v c -> SOP v c
substSOP tv e = foldr1 mergeSOPAdd . map (substProduct tv e) . unS

substProduct :: (Ord v, Ord c) => v -> SOP v c -> Product v c -> SOP v c
substProduct tv e = foldr1 mergeSOPMul . map (substSymbol tv e) . unP

substSymbol :: (Ord v, Ord c) => v -> SOP v c -> Symbol v c -> SOP v c
substSymbol _  _ s@(I _) = S [P [s]]
substSymbol _  _ s@(C _) = S [P [s]]
substSymbol tv e (V tv')
  | tv == tv'            = e
  | otherwise            = S [P [V tv']]
substSymbol tv e (E s p) = normaliseExp (substSOP tv e s) (substProduct tv e p)

-- | Apply a substitution to a substitution
substsSubst :: (Ord v, Ord c) => TySubst v c n -> TySubst v c n -> TySubst v c n
substsSubst s = map (\si -> si {siSOP = substsSOP s (siSOP si)})

-- | Result of comparing two 'SOP' terms, returning a potential substitution
-- list under which the two terms are equal.
data UnifyResult
  = Win            -- ^ Two terms are equal
  | Lose           -- ^ Two terms are /not/ equal
  | Draw CoreSubst -- ^ Two terms are only equal if the given substitution holds

instance Outputable UnifyResult where
  ppr Win          = text "Win"
  ppr (Draw subst) = text "Draw" <+> ppr subst
  ppr Lose         = text "Lose"

-- | Given two 'SOP's @u@ and @v@, when their free variables ('fvSOP') are the
-- same, then we 'Win' if @u@ and @v@ are equal, and 'Lose' otherwise.
--
-- If @u@ and @v@ do not have the same free variables, we result in a 'Draw',
-- ware @u@ and @v@ are only equal when the returned 'CoreSubst' holds.
unifyNats :: Ct -> CoreSOP -> CoreSOP -> TcPluginM UnifyResult
unifyNats ct u v = do
  tcPluginTrace "unifyNats" (ppr ct $$ ppr u $$ ppr v)
  return (unifyNats' ct u v)

unifyNats' :: Ct -> CoreSOP -> CoreSOP -> UnifyResult
unifyNats' ct u v
    | eqFV u v  = if u == v then Win else Lose
    | otherwise = Draw (unifiers ct u v)

-- | Find unifiers for two SOP terms
--
-- Can find the following unifiers:
--
-- @
-- t ~ a + b          ==>  [t := a + b]
-- a + b ~ t          ==>  [t := a + b]
-- (a + c) ~ (b + c)  ==>  \[a := b\]
-- (2*a) ~ (2*b)      ==>  [a := b]
-- (2 + a) ~ 5        ==>  [a := 3]
-- @
--
-- However, given a wanted:
--
-- @
-- [W] t ~ a + b
-- @
--
-- this function returns @[]@, or otherwise we \"solve\" the constraint by
-- finding a unifier equal to the constraint.
--
-- However, given a wanted:
--
-- @
-- [W] (a + c) ~ (b + c)
-- @
--
-- we do return the unifier:
--
-- @
-- [a := b]
-- @
unifiers :: Ct -> CoreSOP -> CoreSOP -> CoreSubst
unifiers ct (S [P [V x]]) s
  | isGiven (ctEvidence ct) = [SubstItem x s     ct]
  | otherwise               = []
unifiers ct s (S [P [V x]])
  | isGiven (ctEvidence ct) = [SubstItem x s     ct]
  | otherwise               = []
unifiers ct u v             = unifiers' ct u v

unifiers' :: Ct -> CoreSOP -> CoreSOP -> CoreSubst
unifiers' ct (S [P [V x]]) (S [])        = [SubstItem x (S [P [I 0]]) ct]
unifiers' ct (S [])        (S [P [V x]]) = [SubstItem x (S [P [I 0]]) ct]
unifiers' ct (S [P [V x]]) s             = [SubstItem x s     ct]
unifiers' ct s             (S [P [V x]]) = [SubstItem x s     ct]
unifiers' ct (S [P (p:ps1)]) (S [P (p':ps2)])
    | p == p'    = unifiers' ct (S [P ps1]) (S [P ps2])
    | otherwise = []
unifiers' ct (S ((P [I i]):ps1)) (S ((P [I j]):ps2))
    | i < j     = unifiers' ct (S ps1) (S ((P [I (j-i)]):ps2))
    | i > j     = unifiers' ct (S ((P [I (i-j)]):ps1)) (S ps2)
unifiers' ct (S ps1)       (S ps2)
    | null psx  = []
    | otherwise = unifiers' ct (S (ps1 \\ psx)) (S (ps2 \\ psx))
  where
    psx = intersect ps1 ps2

-- | Find the 'TyVar' in a 'CoreSOP'
fvSOP :: CoreSOP -> UniqSet TyVar
fvSOP = unionManyUniqSets . map fvProduct . unS

fvProduct :: CoreProduct -> UniqSet TyVar
fvProduct = unionManyUniqSets . map fvSymbol . unP

fvSymbol :: CoreSymbol -> UniqSet TyVar
fvSymbol (I _)   = emptyUniqSet
fvSymbol (C _)   = emptyUniqSet
fvSymbol (V v)   = unitUniqSet v
fvSymbol (E s p) = fvSOP s `unionUniqSets` fvProduct p

eqFV :: CoreSOP -> CoreSOP -> Bool
eqFV = (==) `on` fvSOP
