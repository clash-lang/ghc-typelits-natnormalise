{-|
Copyright  :  (C) 2015-2016, University of Twente,
                  2017     , QBayLogic B.V.
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>
-}

{-# LANGUAGE CPP                        #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MagicHash                  #-}
{-# LANGUAGE RecordWildCards            #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-}
#if __GLASGOW_HASKELL__ < 801
#define nonDetCmpType cmpType
#endif

module GHC.TypeLits.Normalise.Unify
  ( -- * 'Nat' expressions \<-\> 'SOP' terms
    CType (..)
  , CoreSOP
  , normaliseNat
  , normaliseNatEverywhere
  , normaliseSimplifyNat
  , reifySOP
    -- * Substitution on 'SOP' terms
  , UnifyItem (..)
  , CoreUnify
  , substsSOP
  , substsSubst
    -- * Find unifiers
  , UnifyResult (..)
  , unifyNats
  , unifiers
    -- * Free variables in 'SOP' terms
  , fvSOP
    -- * Inequalities
  , subtractIneq
  , solveIneq
  , ineqToSubst
  , subtractionToPred
  , instantSolveIneq
    -- * Properties
  , isNatural
  )
where

-- External
import Control.Arrow (second)
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Writer.Strict
import Data.Function (on)
import Data.List     ((\\), intersect, mapAccumL, nub)
import Data.Maybe    (fromMaybe, mapMaybe)
import Data.Set      (Set)
import Data.Generics (mkM, everywhereM)
import qualified Data.Set as Set

import GHC.Base               (isTrue#,(==#))
import GHC.Integer            (smallInteger)
import GHC.Integer.Logarithms (integerLogBase#)

-- GHC API
import Outputable    (Outputable (..), (<+>), ($$), text)
import TcPluginM     (TcPluginM, tcPluginTrace)
import TcRnMonad     (Ct, ctEvidence, isGiven)
import TcRnTypes     (ctEvPred)
import TcTypeNats    (typeNatAddTyCon, typeNatExpTyCon, typeNatMulTyCon,
                      typeNatSubTyCon, typeNatLeqTyCon)
import Type          (EqRel (NomEq), PredTree (EqPred), TyVar, classifyPredType,
                      coreView, eqType, mkNumLitTy, mkTyConApp, mkTyVarTy,
                      nonDetCmpType, PredType, mkPrimEqPred, typeKind)
import TyCoRep       (Kind, Type (..), TyLit (..))
import TysWiredIn    (boolTy, promotedTrueDataCon, typeNatKind)
import UniqSet       (UniqSet, unionManyUniqSets, emptyUniqSet, unionUniqSets,
                      unitUniqSet)

-- Internal
import GHC.TypeLits.Normalise.SOP

-- Used for haddock
import GHC.TypeLits (Nat)

newtype CType = CType { unCType :: Type }
  deriving Outputable

instance Eq CType where
  (CType ty1) == (CType ty2) = eqType ty1 ty2

instance Ord CType where
  compare (CType ty1) (CType ty2) = nonDetCmpType ty1 ty2

-- | 'SOP' with 'TyVar' variables
type CoreSOP     = SOP TyVar CType
type CoreProduct = Product TyVar CType
type CoreSymbol  = Symbol TyVar CType

-- | Convert a type of /kind/ 'GHC.TypeLits.Nat' to an 'SOP' term, but
-- only when the type is constructed out of:
--
-- * literals
-- * type variables
-- * Applications of the arithmetic operators @(+,-,*,^)@
normaliseNat :: Type -> Writer [(Type,Type)] CoreSOP
normaliseNat ty | Just ty1 <- coreView ty = normaliseNat ty1
normaliseNat (TyVarTy v)          = return (S [P [V v]])
normaliseNat (LitTy (NumTyLit i)) = return (S [P [I i]])
normaliseNat (TyConApp tc [x,y])
  | tc == typeNatAddTyCon = mergeSOPAdd <$> normaliseNat x <*> normaliseNat y
  | tc == typeNatSubTyCon = do
    tell [(x,y)]
    mergeSOPAdd <$> normaliseNat x
                <*> (mergeSOPMul (S [P [I (-1)]]) <$> normaliseNat y)
  | tc == typeNatMulTyCon = mergeSOPMul <$> normaliseNat x <*> normaliseNat y
  | tc == typeNatExpTyCon = normaliseExp <$> normaliseNat x <*> normaliseNat y
normaliseNat t = return (S [P [C (CType t)]])

-- | Applies 'normaliseNat' and 'simplifySOP' to type or predicats
--   to reduce any occurence of sub-terms
--   of /kind/ 'GHC.TypeLits.Nat'.
--   If the result is the same as input, returns @'Nothing'@.
normaliseNatEverywhere
  :: Type -> Writer [(Type, Type)] (Maybe Type)
normaliseNatEverywhere ty
  | typeKind ty `eqType` typeNatKind = do
      ty' <- normaliseSimplifyNat ty
      return $ if ty `eqType` ty' then Nothing else Just ty'
  | otherwise = do
      ty' <- everywhereM (mkM normaliseSimplifyNat) ty
      return $ if ty `eqType` ty' then Nothing else Just ty'

normaliseSimplifyNat :: Type -> Writer [(Type, Type)] Type
normaliseSimplifyNat ty
  | typeKind ty `eqType` typeNatKind = do
      ty' <- normaliseNat ty
      return $ reifySOP $ simplifySOP ty'
  | otherwise = return ty

-- | Convert a 'SOP' term back to a type of /kind/ 'GHC.TypeLits.Nat'
reifySOP :: CoreSOP -> Type
reifySOP = combineP . map negateP . unS
  where
    negateP :: CoreProduct -> Either CoreProduct CoreProduct
    negateP (P ((I i):ps@(_:_))) | i == (-1) = Left  (P ps)
    negateP (P ((I i):ps)) | i < 0           = Left  (P ((I (abs i)):ps))
    negateP ps                               = Right ps

    combineP :: [Either CoreProduct CoreProduct] -> Type
    combineP []     = mkNumLitTy 0
    combineP [p]    = either (\p' -> mkTyConApp typeNatSubTyCon
                                                [mkNumLitTy 0, reifyProduct p'])
                             reifyProduct p
    combineP [p1,p2] = either
      (\x -> either
               -- x neg, y neg
               (\y -> let r = mkTyConApp typeNatSubTyCon [reifyProduct x
                                                         ,reifyProduct y]
                      in  mkTyConApp typeNatSubTyCon [mkNumLitTy 0, r])
               -- x neg, y pos
               (\y -> mkTyConApp typeNatSubTyCon [reifyProduct y, reifyProduct x])
               p2)
      (\x -> either
               -- x pos, y neg
               (\y -> mkTyConApp typeNatSubTyCon [reifyProduct x, reifyProduct y])
               -- x pos, y pos
               (\y -> mkTyConApp typeNatAddTyCon [reifyProduct x, reifyProduct y])
               p2)
      p1


    combineP (p:ps)  = let es = combineP ps
                       in  either (\x -> mkTyConApp typeNatSubTyCon
                                                    [es, reifyProduct x])
                                  (\x -> mkTyConApp typeNatAddTyCon
                                                   [reifyProduct x, es])
                                  p

reifyProduct :: CoreProduct -> Type
reifyProduct (P ps) =
    let ps' = map reifySymbol (foldr mergeExp [] ps)
    in  foldr (\t1 t2 -> mkTyConApp typeNatMulTyCon [t1,t2]) (head ps') (tail ps')
  where
    -- "2 ^ -1 * 2 ^ a" must be merged into "2 ^ (a-1)", otherwise GHC barfs
    -- at the "2 ^ -1" because of the negative exponent.
    mergeExp :: CoreSymbol -> [Either CoreSymbol (CoreSOP,[CoreProduct])]
                           -> [Either CoreSymbol (CoreSOP,[CoreProduct])]
    mergeExp (E s p)   []     = [Right (s,[p])]
    mergeExp (E s1 p1) (y:ys)
      | Right (s2,p2) <- y
      , s1 == s2
      = Right (s1,(p1:p2)) : ys
      | otherwise
      = Right (s1,[p1]) : y : ys
    mergeExp x ys = Left x : ys

reifySymbol :: Either CoreSymbol (CoreSOP,[CoreProduct]) -> Type
reifySymbol (Left (I i)  )  = mkNumLitTy i
reifySymbol (Left (C c)  )  = unCType c
reifySymbol (Left (V v)  )  = mkTyVarTy v
reifySymbol (Left (E s p))  = mkTyConApp typeNatExpTyCon [reifySOP s,reifyProduct p]
reifySymbol (Right (s1,s2)) = mkTyConApp typeNatExpTyCon
                                         [reifySOP s1
                                         ,reifySOP (S s2)
                                         ]

-- | Subtract an inequality, in order to either:
--
-- * See if the smallest solution is a natural number
-- * Cancel sums, i.e. monotonicity of addition
--
-- @
-- subtractIneq (2*y <=? 3*x ~ True)  = (-2*y + 3*x)
-- subtractIneq (2*y <=? 3*x ~ False) = (-3*x + (-1) + 2*y)
-- @
subtractIneq
  :: (CoreSOP, CoreSOP, Bool)
  -> CoreSOP
subtractIneq (x,y,isLE)
  | isLE
  = mergeSOPAdd y (mergeSOPMul (S [P [I (-1)]]) x)
  | otherwise
  = mergeSOPAdd x (mergeSOPMul (S [P [I (-1)]]) (mergeSOPAdd y (S [P [I 1]])))

-- | Try to reverse the process of 'subtractIneq'
--
-- E.g.
--
-- @
-- subtractIneq (2*y <=? 3*x ~ True) = (-2*y + 3*x)
-- sopToIneq (-2*y+3*x) = Just (2*x <=? 3*x ~ True)
-- @
sopToIneq
  :: CoreSOP
  -> Maybe Ineq
sopToIneq (S [P ((I i):l),r])
  | i < 0
  = Just (mergeSOPMul (S [P [I (negate i)]]) (S [P l]),S [r],True)
sopToIneq (S [r,P ((I i:l))])
  | i < 0
  = Just (mergeSOPMul (S [P [I (negate i)]]) (S [P l]),S [r],True)
sopToIneq _ = Nothing

-- | Give the smallest solution for an inequality
ineqToSubst
  :: Ineq
  -> Maybe CoreUnify
ineqToSubst (x,S [P [V v]],True)
  = Just (SubstItem v x)
ineqToSubst _
  = Nothing

subtractionToPred
  :: (Type,Type)
  -> (PredType, Kind)
subtractionToPred (x,y) =
  (mkPrimEqPred (mkTyConApp typeNatLeqTyCon [y,x])
                (mkTyConApp promotedTrueDataCon [])
  ,boolTy)

-- | A substitution is essentially a list of (variable, 'SOP') pairs,
-- but we keep the original 'Ct' that lead to the substitution being
-- made, for use when turning the substitution back into constraints.
type CoreUnify = UnifyItem TyVar CType

data UnifyItem v c = SubstItem { siVar :: v
                               , siSOP :: SOP v c
                               }
                   | UnifyItem { siLHS :: SOP v c
                               , siRHS :: SOP v c
                               }
  deriving Eq

instance (Outputable v, Outputable c) => Outputable (UnifyItem v c) where
  ppr (SubstItem {..}) = ppr siVar <+> text " := " <+> ppr siSOP
  ppr (UnifyItem {..}) = ppr siLHS <+> text " :~ " <+> ppr siRHS

-- | Apply a substitution to a single normalised 'SOP' term
substsSOP :: (Ord v, Ord c) => [UnifyItem v c] -> SOP v c -> SOP v c
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
substsSubst :: (Ord v, Ord c) => [UnifyItem v c] -> [UnifyItem v c] -> [UnifyItem v c]
substsSubst s = map subt
  where
    subt si@(SubstItem {..}) = si {siSOP = substsSOP s siSOP}
    subt si@(UnifyItem {..}) = si {siLHS = substsSOP s siLHS, siRHS = substsSOP s siRHS}
{-# INLINEABLE substsSubst #-}

-- | Result of comparing two 'SOP' terms, returning a potential substitution
-- list under which the two terms are equal.
data UnifyResult
  = Win              -- ^ Two terms are equal
  | Lose             -- ^ Two terms are /not/ equal
  | Draw [CoreUnify] -- ^ Two terms are only equal if the given substitution holds

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
                       else Draw (filter diffFromConstraint (unifiers ct u v))
               else if u == v
                       then Win
                       else Lose
       else Draw (filter diffFromConstraint (unifiers ct u v))
  where
    -- A unifier is only a unifier if differs from the original constraint
    diffFromConstraint (UnifyItem x y) = not (x == u && y == v)
    diffFromConstraint _               = True

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
unifiers :: Ct -> CoreSOP -> CoreSOP -> [CoreUnify]
unifiers ct u@(S [P [V x]]) v
  = case classifyPredType $ ctEvPred $ ctEvidence ct of
      EqPred NomEq t1 _
        | CType (reifySOP u) /= CType t1 || isGiven (ctEvidence ct) -> [SubstItem x v]
      _ -> []
unifiers ct u v@(S [P [V x]])
  = case classifyPredType $ ctEvPred $ ctEvidence ct of
      EqPred NomEq _ t2
        | CType (reifySOP v) /= CType t2 || isGiven (ctEvidence ct) -> [SubstItem x u]
      _ -> []
unifiers ct u@(S [P [C _]]) v
  = case classifyPredType $ ctEvPred $ ctEvidence ct of
      EqPred NomEq t1 t2
        | CType (reifySOP u) /= CType t1 || CType (reifySOP v) /= CType t2 -> [UnifyItem u v]
      _ -> []
unifiers ct u v@(S [P [C _]])
  = case classifyPredType $ ctEvPred $ ctEvidence ct of
      EqPred NomEq t1 t2
        | CType (reifySOP u) /= CType t1 || CType (reifySOP v) /= CType t2 -> [UnifyItem u v]
      _ -> []
unifiers ct u v             = unifiers' ct u v

unifiers' :: Ct -> CoreSOP -> CoreSOP -> [CoreUnify]
unifiers' _ct (S [P [V x]]) (S [])        = [SubstItem x (S [P [I 0]])]
unifiers' _ct (S [])        (S [P [V x]]) = [SubstItem x (S [P [I 0]])]

unifiers' _ct (S [P [V x]]) s             = [SubstItem x s]
unifiers' _ct s             (S [P [V x]]) = [SubstItem x s]

unifiers' _ct s1@(S [P [C _]]) s2               = [UnifyItem s1 s2]
unifiers' _ct s1               s2@(S [P [C _]]) = [UnifyItem s1 s2]


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
  = case integerLogBase i j of
      Just k  -> unifiers' ct (S [p]) (S [P [I k]])
      Nothing -> []

unifiers' ct (S [P [I j]]) (S [P [E (S [P [I i]]) p]])
  = case integerLogBase i j of
      Just k  -> unifiers' ct (S [p]) (S [P [I k]])
      Nothing -> []

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
    Just k -> unifiers' ct (S [P ps]) (S [P [I k]])
    _      -> []

unifiers' ct (S [P [I j]]) (S [P ((I i):ps)]) =
  case safeDiv j i of
    Just k -> unifiers' ct (S [P ps]) (S [P [I k]])
    _      -> []

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
unifiers' ct s1@(S ps1) s2@(S ps2) = case sopToIneq k1 of
  Just (s1',s2',_)
    | s1' /= s1 || s2' /= s1
    , maybe True (uncurry (&&) . second Set.null) (runWriterT (isNatural s1'))
    , maybe True (uncurry (&&) . second Set.null) (runWriterT (isNatural s2'))
    -> unifiers' ct s1' s2'
  _ | null psx
    , length ps1 == length ps2
    -> case nub (concat (zipWith (\x y -> unifiers' ct (S [x]) (S [y])) ps1 ps2)) of
        []                             -> unifiers'' ct (S ps1) (S ps2)
        [k] | length ps1 == length ps2 -> [k]
        _                              -> []
    | null psx
    , isGiven (ctEvidence ct)
    -> unifiers'' ct (S ps1) (S ps2)
    | null psx
    -> []
  _ -> unifiers' ct (S ps1'') (S ps2'')
  where
    k1 = subtractIneq (s1,s2,True)
    ps1'  = ps1 \\ psx
    ps2'  = ps2 \\ psx
    ps1'' | null ps1' = [P [I 0]]
          | otherwise = ps1'
    ps2'' | null ps2' = [P [I 0]]
          | otherwise = ps2'
    psx = intersect ps1 ps2

unifiers'' :: Ct -> CoreSOP -> CoreSOP -> [CoreUnify]
unifiers'' ct (S [P [I i],P [V v]]) s2
  | isGiven (ctEvidence ct) = [SubstItem v (mergeSOPAdd s2 (S [P [I (negate i)]]))]
unifiers'' ct s1 (S [P [I i],P [V v]])
  | isGiven (ctEvidence ct) = [SubstItem v (mergeSOPAdd s1 (S [P [I (negate i)]]))]
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

-- | Given `x` and `y`, return `Just n` when
--
-- `ceiling (logBase x y) == floor (logBase x y)`
integerLogBase :: Integer -> Integer -> Maybe Integer
integerLogBase x y | x > 1 && y > 0 =
  let z1 = integerLogBase# x y
      z2 = integerLogBase# x (y-1)
  in  if isTrue# (z1 ==# z2)
         then Nothing
         else Just (smallInteger z1)
integerLogBase _ _ = Nothing

isNatural :: CoreSOP -> WriterT (Set CType) Maybe Bool
isNatural (S [])           = return True
isNatural (S [P []])       = return True
isNatural (S [P (I i:ps)])
  | i >= 0    = isNatural (S [P ps])
  | otherwise = return False
isNatural (S [P (V _:ps)]) = isNatural (S [P ps])
isNatural (S [P (E s p:ps)]) = do
  sN <- isNatural s
  pN <- isNatural (S [p])
  if sN && pN
     then isNatural (S [P ps])
     else WriterT Nothing
-- This is a quick hack, it determines that
--
-- > a^b - 1
--
-- is a natural number as long as 'a' and 'b' are natural numbers.
-- This used to assert that:
--
-- > (1 <=? a^b) ~ True
isNatural (S [P [I (-1)],P [E s p]]) = (&&) <$> isNatural s <*> isNatural (S [p])
-- We give up for all other products for now
isNatural (S [P (C c:ps)]) = do
  tell (Set.singleton c)
  isNatural (S [P ps])
-- Adding two natural numbers is also a natural number
isNatural (S (p:ps)) = do
  pN <- isNatural (S [p])
  pK <- isNatural (S ps)
  case (pN,pK) of
    (True,True)   -> return True  -- both are natural
    (False,False) -> return False -- both are non-natural
    _             -> WriterT Nothing
    -- if one is natural and the other isn't, then their sum *might* be natural,
    -- but we simply cant be sure.

-- | Try to solve inequalities
solveIneq
  :: Word
  -- ^ Solving depth
  -> Ineq
  -- ^ Inequality we want to solve
  -> Ineq
  -- ^ Given/proven inequality
  -> Maybe Bool
  -- ^ Solver result
  --
  -- * /Nothing/: exhausted solver steps
  --
  -- * /Just True/: inequality is solved
  --
  -- * /Just False/: solver is unable to solve inequality, note that this does
  -- __not__ mean the wanted inequality does not hold.
solveIneq 0 _ _ = Nothing
solveIneq k want@(_,_,True) have@(_,_,True)
  | want == have
  = Just True
  | null solved
  = Nothing
  | otherwise
  = Just (or solved)
  where
    solved = mapMaybe (uncurry (solveIneq (k - 1))) new
    new    = concatMap (\f -> f want have) ineqRules
solveIneq _ _ _ = Just False

-- | Try to instantly solve an inequality by using the inequality solver using
-- @1 <=? 1 ~ True@ as the given constraint.
instantSolveIneq
  :: Word
  -- ^ Solving depth
  -> Ineq
  -- ^ Inequality we want to solve
  -> Bool
instantSolveIneq k u = case solveIneq k u (one,one,True) of
  Just p  -> p
  Nothing -> False
 where
  one = S [P [I 1]]

type Ineq = (CoreSOP, CoreSOP, Bool)
type IneqRule = Ineq -> Ineq  -> [(Ineq,Ineq)]

ineqRules
  :: [IneqRule]
ineqRules =
  [ leTrans
  , plusMonotone
  , timesMonotone
  , powMonotone
  , pow2MonotoneSpecial
  , haveSmaller
  , haveBigger
  ]

-- | Transitivity of inequality
leTrans :: IneqRule
leTrans want@(a,b,le) (x,y,_)
  -- want: 1 <=? y ~ True
  -- have: 2 <=? y ~ True
  --
  -- new want: want
  -- new have: 1 <=? y ~ True
  | S [P [I a']] <- a
  , S [P [I x']] <- x
  , x' >= a'
  = [(want,(a,y,le))]
  -- want: y <=? 10 ~ True
  -- have: y <=? 9 ~ True
  --
  -- new want: want
  -- new have: y <=? 10 ~ True
  | S [P [I b']] <- b
  , S [P [I y']] <- y
  , y' < b'
  = [(want,(x,b,le))]
leTrans _ _ = []

-- | Monotonicity of addition
--
-- We use SOP normalization to apply this rule by e.g.:
--
-- * Given: (2*x+1) <= (3*x-1)
-- * Turn to: (3*x-1) - (2*x+1)
-- * SOP version: -2 + x
-- * Convert back to inequality: 2 <= x
plusMonotone :: IneqRule
plusMonotone want have
  | Just want' <- sopToIneq (subtractIneq want)
  , want' /= want
  = [(want',have)]
  | Just have' <- sopToIneq (subtractIneq have)
  , have' /= have
  = [(want,have')]
plusMonotone _ _ = []

-- | Make the `a` of a given `a <= b` smaller
haveSmaller :: IneqRule
haveSmaller want have
  | (S (x:y:ys),us,True) <- have
  = [(want,(S (x:ys),us,True))
    ,(want,(S (y:ys),us,True))
    ]
  | (S [P [I 1]], S [P (I _:p@(_:_))],True) <- have
  = [(want,(S [P [I 1]],S [P p],True))]
haveSmaller _ _ = []

-- | Make the `b` of a given `a <= b` bigger
haveBigger :: IneqRule
haveBigger want have
  | (_,S vs,True) <- want
  , (as,S bs,True) <- have
  , let vs' = vs \\ bs
  , not (null vs')
  -- want : a <= x + 1
  -- have : y <= x
  --
  -- new want: want
  -- new have: y <= x + 1
  = [(want,(as,mergeSOPAdd (S bs) (S vs'),True))]
haveBigger _ _ = []

-- | Monotonicity of multiplication
timesMonotone :: IneqRule
timesMonotone want@(a,b,le) have@(x,y,_)
  -- want: C*a <=? b ~ True
  -- have: x <=? y ~ True
  --
  -- new want: want
  -- new have: C*a <=? C*y ~ True
  | S [P a'@(_:_:_)] <- a
  , S [P x'] <- x
  , S [P y'] <- y
  , let ax = a' \\ x'
  , let ay = a' \\ y'
  -- Ensure we don't repeat this rule over and over
  , not (null ax)
  , not (null ay)
  -- Pick the smallest product
  , let az = if length ax <= length ay then S [P ax] else S [P ay]
  = [(want,(mergeSOPMul az x, mergeSOPMul az y,le))]

  -- want: a <=? C*b ~ True
  -- have: x <=? y ~ True
  --
  -- new want: want
  -- new have: C*a <=? C*y ~ True
  | S [P b'@(_:_:_)] <- b
  , S [P x'] <- x
  , S [P y'] <- y
  , let bx = b' \\ x'
  , let by = b' \\ y'
  -- Ensure we don't repeat this rule over and over
  , not (null bx)
  , not (null by)
  -- Pick the smallest product
  , let bz = if length bx <= length by then S [P bx] else S [P by]
  = [(want,(mergeSOPMul bz x, mergeSOPMul bz y,le))]

  -- want: a <=? b ~ True
  -- have: C*x <=? y ~ True
  --
  -- new want: C*a <=? C*b ~ True
  -- new have: have
  | S [P x'@(_:_:_)] <- x
  , S [P a'] <- a
  , S [P b'] <- b
  , let xa = x' \\ a'
  , let xb = x' \\ b'
  -- Ensure we don't repeat this rule over and over
  , not (null xa)
  , not (null xb)
  -- Pick the smallest product
  , let xz = if length xa <= length xb then S [P xa] else S [P xb]
  = [((mergeSOPMul xz a, mergeSOPMul xz b,le),have)]

  -- want: a <=? b ~ True
  -- have: x <=? C*y ~ True
  --
  -- new want: C*a <=? C*b ~ True
  -- new have: have
  | S [P y'@(_:_:_)] <- y
  , S [P a'] <- a
  , S [P b'] <- b
  , let ya = y' \\ a'
  , let yb = y' \\ b'
  -- Ensure we don't repeat this rule over and over
  , not (null ya)
  , not (null yb)
  -- Pick the smallest product
  , let yz = if length ya <= length yb then S [P ya] else S [P yb]
  = [((mergeSOPMul yz a, mergeSOPMul yz b,le),have)]

timesMonotone _ _ = []

-- | Monotonicity of exponentiation
powMonotone :: IneqRule
powMonotone want (x, S [P [E yS yP]],le)
  = case x of
      S [P [E xS xP]]
        -- want: XXX
        -- have: 2^x <=? 2^y ~ True
        --
        -- new want: want
        -- new have: x <=? y ~ True
        | xS == yS
        -> [(want,(S [xP],S [yP],le))]
        -- want: XXX
        -- have: x^2 <=? y^2 ~ True
        --
        -- new want: want
        -- new have: x <=? y ~ True
        | xP == yP
        -> [(want,(xS,yS,le))]
        -- want: XXX
        -- have: 2 <=? 2 ^ x ~ True
        --
        -- new want: want
        -- new have: 1 <=? x ~ True
      _ | x == yS
        -> [(want,(S [P [I 1]],S [yP],le))]
      _ -> []

powMonotone (a,S [P [E bS bP]],le) have
  = case a of
      S [P [E aS aP]]
        -- want: 2^x <=? 2^y ~ True
        -- have: XXX
        --
        -- new want: x <=? y ~ True
        -- new have: have
        | aS == bS
        -> [((S [aP],S [bP],le),have)]
        -- want: x^2 <=? y^2 ~ True
        -- have: XXX
        --
        -- new want: x <=? y ~ True
        -- new have: have
        | aP == bP
        -> [((aS,bS,le),have)]
        -- want: 2 <=? 2 ^ x ~ True
        -- have: XXX
        --
        -- new want: 1 <=? x ~ True
        -- new have: XXX
      _ | a == bS
        -> [((S [P [I 1]],S [bP],le),have)]
      _ -> []

powMonotone _ _ = []

-- | Try to get the power-of-2 factors, and apply the monotonicity of
-- exponentiation rule.
--
-- TODO: I wish we could generalize to find arbitrary factors, but currently
-- I don't know how.
pow2MonotoneSpecial :: IneqRule
pow2MonotoneSpecial (a,b,le) have
  -- want: 4 * 4^x <=? 8^x ~ True
  -- have: XXX
  --
  -- want as pow 2 factors: 2^(2+2*x) <=? 2^(3*x) ~ True
  --
  -- new want: 2+2*x <=? 3*x ~ True
  -- new have: have
  | Just a' <- facSOP 2 a
  , Just b' <- facSOP 2 b
  = [((a',b',le),have)]
pow2MonotoneSpecial want (x,y,le)
  -- want: XXX
  -- have:4 * 4^x <=? 8^x ~ True
  --
  -- have as pow 2 factors: 2^(2+2*x) <=? 2^(3*x) ~ True
  --
  -- new want: want
  -- new have: 2+2*x <=? 3*x ~ True
  | Just x' <- facSOP 2 x
  , Just y' <- facSOP 2 y
  = [(want,(x',y',le))]
pow2MonotoneSpecial _ _ = []

-- | Get the power of /N/ factors of a SOP term
facSOP
  :: Integer
  -- ^ The power /N/
  -> CoreSOP
  -> Maybe CoreSOP
facSOP n (S [P ps]) = fmap (S . concat . map unS) (traverse (facSymbol n) ps)
facSOP _ _          = Nothing

-- | Get the power of /N/ factors of a Symbol
facSymbol
  :: Integer
  -- ^ The power
  -> CoreSymbol
  -> Maybe CoreSOP
facSymbol n (I i)
  | Just j <- integerLogBase n i
  = Just (S [P [I j]])
facSymbol n (E s p)
  | Just s' <- facSOP n s
  = Just (mergeSOPMul s' (S [p]))
facSymbol _ _ = Nothing
