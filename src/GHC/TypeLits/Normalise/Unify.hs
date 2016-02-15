{-|
Copyright  :  (C) 2015-2016, University of Twente
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>
-}

{-# LANGUAGE CPP             #-}
{-# LANGUAGE RecordWildCards #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-}

module GHC.TypeLits.Normalise.Unify
  ( -- * 'Nat' expressions \<-\> 'SOP' terms
    CoreSOP
  , normaliseNat
  , reifySOP
    -- * Substitution on 'SOP' terms
  , UnifyItem (..)
  , TyUnify
  , CoreUnify
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
import Data.List     ((\\), intersect, mapAccumL)

-- GHC API
import Outputable    (Outputable (..), (<+>), ($$), text)
import TcPluginM     (TcPluginM, tcPluginTrace)
import TcRnMonad     (Ct, ctEvidence, isGiven)
import TcRnTypes     (ctEvPred)
import TcTypeNats    (typeNatAddTyCon, typeNatExpTyCon, typeNatMulTyCon,
                      typeNatSubTyCon)
import Type          (EqRel (NomEq), PredTree (EqPred), TyVar, classifyPredType,
                      coreView, mkNumLitTy, mkTyConApp, mkTyVarTy)
#if __GLASGOW_HASKELL__ >= 711
import TyCoRep       (Type (..), TyLit (..))
#else
import TypeRep       (Type (..), TyLit (..))
#endif
import UniqSet       (UniqSet, unionManyUniqSets, emptyUniqSet, unionUniqSets,
                      unitUniqSet)

-- Internal
import GHC.Extra.Instances () -- Ord instance for Type
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
normaliseNat ty | Just ty1 <- coreView ty = normaliseNat ty1
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
    negateP (P ((I i):ps)) | i < 0 = Left  (P ((I (abs i)):ps))
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
type CoreUnify a = TyUnify TyVar Type a

type TyUnify v c n = [UnifyItem v c n]

data UnifyItem v c n = SubstItem { siVar  :: v
                                 , siSOP  :: SOP v c
                                 , siNote :: n
                                 }
                     | UnifyItem { siLHS  :: SOP v c
                                 , siRHS  :: SOP v c
                                 , siNote :: n
                                 }

instance (Outputable v, Outputable c) => Outputable (UnifyItem v c n) where
  ppr (SubstItem {..}) = ppr siVar <+> text " := " <+> ppr siSOP
  ppr (UnifyItem {..}) = ppr siLHS <+> text " :~ " <+> ppr siRHS

-- | Apply a substitution to a single normalised 'SOP' term
substsSOP :: (Ord v, Ord c) => TyUnify v c n -> SOP v c -> SOP v c
substsSOP []                   u = u
substsSOP ((SubstItem {..}):s) u = substsSOP s (substSOP siVar siSOP u)
substsSOP ((UnifyItem {}):s)   u = substsSOP s u

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
substsSubst :: (Ord v, Ord c) => TyUnify v c n -> TyUnify v c n -> TyUnify v c n
substsSubst s = map subt
  where
    subt si@(SubstItem {..}) = si {siSOP = substsSOP s siSOP}
    subt si@(UnifyItem {..}) = si {siLHS = substsSOP s siLHS, siRHS = substsSOP s siRHS}
{-# INLINEABLE substsSubst #-}

-- | Result of comparing two 'SOP' terms, returning a potential substitution
-- list under which the two terms are equal.
data UnifyResult
  = Win            -- ^ Two terms are equal
  | Lose           -- ^ Two terms are /not/ equal
  | Draw (CoreUnify Ct) -- ^ Two terms are only equal if the given substitution holds

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
  = if eqFV u v
       then if containsConstants u || containsConstants v
               then if u == v
                       then Win
                       else Draw (unifiers ct u v)
               else if u == v
                       then Win
                       else Lose
       else Draw (unifiers ct u v)

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
-- (i * a) ~ j        ==>  [a := div j i], when (mod j i == 0)
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
unifiers :: Ct -> CoreSOP -> CoreSOP -> CoreUnify Ct
unifiers ct u@(S [P [V x]]) v
  = case classifyPredType $ ctEvPred $ ctEvidence ct of
      EqPred NomEq t1 _
        | reifySOP u /= t1 || isGiven (ctEvidence ct) -> [SubstItem x v ct]
      _ -> []
unifiers ct u v@(S [P [V x]])
  = case classifyPredType $ ctEvPred $ ctEvidence ct of
      EqPred NomEq _ t2
        | reifySOP v /= t2 || isGiven (ctEvidence ct) -> [SubstItem x u ct]
      _ -> []
unifiers ct u@(S [P [C _]]) v
  = case classifyPredType $ ctEvPred $ ctEvidence ct of
      EqPred NomEq t1 t2
        | reifySOP u /= t1 || reifySOP v /= t2 -> [UnifyItem u v ct]
      _ -> []
unifiers ct u v@(S [P [C _]])
  = case classifyPredType $ ctEvPred $ ctEvidence ct of
      EqPred NomEq t1 t2
        | reifySOP u /= t1 || reifySOP v /= t2 -> [UnifyItem u v ct]
      _ -> []
unifiers ct u v             = unifiers' ct u v

unifiers' :: Ct -> CoreSOP -> CoreSOP -> CoreUnify Ct
unifiers' ct (S [P [V x]]) (S [])        = [SubstItem x (S [P [I 0]]) ct]
unifiers' ct (S [])        (S [P [V x]]) = [SubstItem x (S [P [I 0]]) ct]

unifiers' ct (S [P [V x]]) s             = [SubstItem x s ct]
unifiers' ct s             (S [P [V x]]) = [SubstItem x s ct]

unifiers' ct s1@(S [P [C _]]) s2               = [UnifyItem s1 s2 ct]
unifiers' ct s1               s2@(S [P [C _]]) = [UnifyItem s1 s2 ct]


-- (z ^ a) ~ (z ^ b) ==> [a := b]
unifiers' ct (S [P [E s1 p1]]) (S [P [E s2 p2]])
  | s1 == s2 = unifiers' ct (S [p1]) (S [p2])

-- (2*e ^ d) ~ (2*e*a*c) ==> [a*c := 2*e ^ (d-1)]
unifiers' ct (S [P [E (S [P s1]) p1]]) (S [P p2])
  | all (`elem` p2) s1
  = let base = intersect s1 p2
        diff = p2 \\ s1
    in  unifiers ct (S [P diff]) (S [P [E (S [P base]) (P [I (-1)]),E (S [P base]) p1]])

unifiers' ct (S [P p2]) (S [P [E (S [P s1]) p1]])
  | all (`elem` p2) s1
  = let base = intersect s1 p2
        diff = p2 \\ s1
    in  unifiers ct (S [P [E (S [P base]) (P [I (-1)]),E (S [P base]) p1]]) (S [P diff])

-- (i ^ a) ~ j ==> [a := round (logBase i j)], when `i` and `j` are integers,
-- and `ceiling (logBase i j) == floor (logBase i j)`
unifiers' ct (S [P [E (S [P [I i]]) p]]) (S [P [I j]])
    = if kC == kF
         then unifiers' ct (S [p]) (S [P [I kC]])
         else []
  where
    k  = logBase (fromInteger i :: Double) (fromInteger j)
    kC = ceiling k :: Integer
    kF = floor k :: Integer

unifiers' ct (S [P [I j]]) (S [P [E (S [P [I i]]) p]])
    = if kC == kF
         then unifiers' ct (S [p]) (S [P [I kC]])
         else []
  where
    k  = logBase (fromInteger i :: Double) (fromInteger j)
    kC = ceiling k :: Integer
    kF = floor k :: Integer

-- a^d * a^e ~ a^c ==> [c := d + e]
unifiers' ct (S [P [E s1 p1]]) (S [p2]) = case collectBases p2 of
  Just (b:bs,ps) | all (== s1) (b:bs) ->
    unifiers' ct (S [p1]) (S ps)
  _ -> []

unifiers' ct (S [p2]) (S [P [E s1 p1]]) = case collectBases p2 of
  Just (b:bs,ps) | all (== s1) (b:bs) ->
    unifiers' ct (S ps) (S [p1])
  _ -> []

-- (i * a) ~ j ==> [a := div j i]
-- Where 'a' is a variable, 'i' and 'j' are integer literals, and j `mod` i == 0
unifiers' ct (S [P ((I i):ps)]) (S [P [I j]]) =
  case safeDiv j i of
    Just k  -> unifiers' ct (S [P ps]) (S [P [I k]])
    _       -> []

unifiers' ct (S [P [I j]]) (S [P ((I i):ps)]) =
  case safeDiv j i of
    Just k  -> unifiers' ct (S [P ps]) (S [P [I k]])
    _       -> []

-- (2*a) ~ (2*b) ==> [a := b]
-- unifiers' ct (S [P (p:ps1)]) (S [P (p':ps2)])
--     | p == p'   = unifiers' ct (S [P ps1]) (S [P ps2])
--     | otherwise = []
unifiers' ct (S [P ps1]) (S [P ps2])
    | null psx  = []
    | otherwise = unifiers' ct (S [P ps1'']) (S [P ps2''])
  where
    ps1'  = ps1 \\ psx
    ps2'  = ps2 \\ psx
    ps1'' | null ps1' = [I 1]
          | otherwise = ps1'
    ps2'' | null ps2' = [I 1]
          | otherwise = ps2'
    psx  = intersect ps1 ps2

-- (2 + a) ~ 5 ==> [a := 3]
unifiers' ct (S ((P [I i]):ps1)) (S ((P [I j]):ps2))
    | i < j     = unifiers' ct (S ps1) (S ((P [I (j-i)]):ps2))
    | i > j     = unifiers' ct (S ((P [I (i-j)]):ps1)) (S ps2)

-- (a + c) ~ (b + c) ==> [a := b]
unifiers' ct (S ps1)       (S ps2)
    | null psx  = unifiers'' ct (S ps1) (S ps2)
    | otherwise = unifiers' ct (S ps1'') (S ps2'')
  where
    ps1'  = ps1 \\ psx
    ps2'  = ps2 \\ psx
    ps1'' | null ps1' = [P [I 0]]
          | otherwise = ps1'
    ps2'' | null ps2' = [P [I 0]]
          | otherwise = ps2'
    psx = intersect ps1 ps2

unifiers'' ct (S [P [I i],P [V v]]) s2
  | isGiven (ctEvidence ct) = [SubstItem v (mergeSOPAdd s2 (S [P [I (negate i)]])) ct]
unifiers'' ct s1 (S [P [I i],P [V v]])
  | isGiven (ctEvidence ct) = [SubstItem v (mergeSOPAdd s1 (S [P [I (negate i)]])) ct]
unifiers'' _ _ _ = []

collectBases :: CoreProduct -> Maybe ([CoreSOP],[CoreProduct])
collectBases = fmap unzip . traverse go . unP
  where
    go (E s1 p1) = Just (s1,p1)
    go _         = Nothing

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

containsConstants :: CoreSOP -> Bool
containsConstants = any (any (\c -> case c of {(C _) -> True; _ -> False}) . unP) . unS

safeDiv :: Integer -> Integer -> Maybe Integer
safeDiv i j
  | j == 0    = Just 0
  | otherwise = case divMod i j of
                  (k,0) -> Just k
                  _     -> Nothing
