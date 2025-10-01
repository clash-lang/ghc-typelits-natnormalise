{-|
Copyright  :  (C) 2015-2016, University of Twente,
                  2017     , QBayLogic B.V.
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>
-}

{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MagicHash                  #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE TupleSections              #-}

{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

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
  , instantSolveIneq
  , solvedInEqSmallestConstraint
  , negateProd
    -- * Properties
  , isNatural
  )
where

-- base
import Control.Arrow
  ( first, second )
import Control.Monad
  ( guard, zipWithM )
import Data.Either
  ( partitionEithers )
import Data.List
  ( (\\), intersect, nub )
import Data.Maybe
  ( fromMaybe, mapMaybe, isJust )
import GHC.Base
  ( (==#), isTrue# )
import GHC.Integer
  ( smallInteger )
import GHC.Integer.Logarithms
  ( integerLogBase# )

-- containers
import Data.Set
  ( Set )
import qualified Data.Set as Set

-- ghc
import GHC.Builtin.Types.Literals
  ( typeNatAddTyCon, typeNatExpTyCon, typeNatMulTyCon, typeNatSubTyCon
  )
import GHC.Types.Unique.Set
  ( UniqSet
  , emptyUniqSet, unionManyUniqSets, unionUniqSets, unitUniqSet
  , nonDetEltsUniqSet, elementOfUniqSet
  )

-- ghc-tcplugin-api
import GHC.TcPlugin.API
import GHC.TcPlugin.API.TyConSubst
  ( TyConSubst )
import GHC.Utils.Outputable


-- ghc-typelits-natnormalise
import GHC.TypeLits.Normalise.SOP

-- transformers
import Control.Monad.Trans.Writer.Strict
  ( Writer, WriterT(..), runWriter, tell )

--------------------------------------------------------------------------------

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
normaliseNat :: TyConSubst -> Type -> Writer [(Type,Type)] (CoreSOP, [Coercion])
normaliseNat givensTyConSubst ty
  | Just (tc, xs) <- splitTyConApp_maybe ty
  = goTyConApp tc xs
  | Just i <- isNumLitTy ty
  = return (S [P [I i]], [])
  | Just v <- getTyVar_maybe ty
  = return (S [P [V v]], [])
  | otherwise
  = return (S [P [C (CType ty)]], [])
    where
      goTyConApp :: TyCon -> [Type] -> Writer [(Type,Type)] (CoreSOP, [Coercion])
      goTyConApp tc [x,y]
        | tc == typeNatAddTyCon =
            do (x', cos1) <- normaliseNat givensTyConSubst x
               (y', cos2) <- normaliseNat givensTyConSubst y
               return (mergeSOPAdd x' y', cos1 ++ cos2)
        | tc == typeNatSubTyCon = do
          (x', cos1) <- normaliseNat givensTyConSubst x
          (y', cos2) <- normaliseNat givensTyConSubst y
          tell [(reifySOP $ simplifySOP x', reifySOP $ simplifySOP y')]
          return (mergeSOPAdd x' (mergeSOPMul (S [P [I (-1)]]) y'), cos1 ++ cos2)
        | tc == typeNatMulTyCon =
          do (x', cos1) <- normaliseNat givensTyConSubst x
             (y', cos2) <- normaliseNat givensTyConSubst y
             return (mergeSOPMul x' y', cos1 ++ cos2)
        | tc == typeNatExpTyCon =
          do (x', cos1) <- normaliseNat givensTyConSubst x
             (y', cos2) <- normaliseNat givensTyConSubst y
             return (normaliseExp x' y', cos1 ++ cos2)
      goTyConApp tc xs
        = return (S [P [C (CType $ mkTyConApp tc xs)]], [])

knownTyCons :: [TyCon]
knownTyCons = [typeNatExpTyCon, typeNatMulTyCon, typeNatSubTyCon, typeNatAddTyCon]


-- | Runs writer action. If the result is /Nothing/, writer actions will be
-- discarded.
maybeRunWriter
  :: Monoid a
  => Writer a (Maybe b)
  -> Writer a (Maybe b)
maybeRunWriter w =
  case runWriter w of
    (Nothing, _) -> pure Nothing
    (b, a) -> tell a >> pure b

-- | Applies 'normaliseNat' and 'simplifySOP' to type or predicates to reduce
-- any occurrences of sub-terms of /kind/ 'GHC.TypeLits.Nat'. If the result is
-- the same as input, returns @'Nothing'@.
normaliseNatEverywhere :: TyConSubst -> Type -> Writer [(Type, Type)] (Maybe (Type, [Coercion]))
normaliseNatEverywhere givensTyConSubst ty0
  | Just (tc, fields) <- splitTyConApp_maybe ty0
  =   if tc `elem` knownTyCons
      then do
        -- Normalize under current type constructor application. 'go' skips all
        -- known type constructors.
        ty1M <- maybeRunWriter (go tc fields)
        let (ty1, cos1) = fromMaybe (ty0, []) ty1M
        -- Normalize (subterm-normalized) type given to 'normaliseNatEverywhere'
        (ty2, cos2) <- normaliseSimplifyNat givensTyConSubst ty1
        -- TODO: 'normaliseNat' could keep track whether it changed anything. That's
        -- TODO: probably cheaper than checking for equality here.
        pure $
          if ty2 `eqType` ty1
          then second (cos1 ++) <$> ty1M
          else Just (ty2, cos1 ++ cos2)
      else
        go tc fields

  | otherwise
  = pure Nothing
 where

  -- Normalize given type, but ignore all top-level
  go :: TyCon -> [Type] -> Writer [(Type, Type)] (Maybe (Type, [Coercion]))
  go tc_ fields0_ = do
    fields1_ <- mapM (maybeRunWriter . cont) fields0_
    if any isJust fields1_
    then do
      let cos' = concat $ mapMaybe (fmap snd) fields1_
          ty' = mkTyConApp tc_ (zipWith (\ f0 f1 -> maybe f0 fst f1) fields0_ fields1_)
      pure (Just (ty', cos'))
    else
      pure Nothing
   where
    cont ty'
      | tc_ `elem` knownTyCons
      , Just (tc', flds') <- splitTyConApp_maybe ty'
      = go tc' flds'
      | otherwise
      = normaliseNatEverywhere givensTyConSubst ty'

normaliseSimplifyNat :: TyConSubst -> Type -> Writer [(Type, Type)] (Type, [Coercion])
normaliseSimplifyNat givensTyConSubst ty
  | typeKind ty `eqType` natKind = do
      (ty', cos1) <- normaliseNat givensTyConSubst ty
      return $ (reifySOP $ simplifySOP ty', cos1)
  | otherwise = return (ty, [])

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
    in  foldr1 (\t1 t2 -> mkTyConApp typeNatMulTyCon [t1,t2]) ps'
  where
    -- "2 ^ -1 * 2 ^ a" must be merged into "2 ^ (a-1)", otherwise GHC barfs
    -- at the "2 ^ -1" because of the negative exponent.
    mergeExp :: CoreSymbol -> [Either CoreSymbol (CoreSOP,[CoreProduct])]
                           -> [Either CoreSymbol (CoreSOP,[CoreProduct])]
    mergeExp (E (S [P [I 1]]) _) ys = ys
    mergeExp (E s p)             [] = [Right (s,[p])]
    mergeExp (E (S [P [I s1]]) p1) (y:ys)
      | Right ((S [P [I s2]]), p2s) <- y
      , let s = gcd s1 s2
            t1 = s1 `quot` s
            t2 = s2 `quot` s
      , s > 1
      -- Deal with e.g. "2 ^ -1 * 6 ^ x", where the bases differ.
      --
      --   (s * t1) ^ p1 * (s * t2) ^ (p2 + ...) * rest
      --     ===>
      --   s ^ (p1 + p2 + ...) * t1 ^ p1 * t2 ^ (p2 + ..) * rest
      = Right (S [P [I s]], (p1:p2s)) :
         mergeExp (E (S [P [I t1]]) p1)
           (Right ((S [P [I t2]]), p2s):ys)
    mergeExp (E s1 p1) (y:ys)
      | Right (s2,p2s) <- y
      , s1 == s2
      = Right (s1,(p1:p2s)) : ys
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

-- | Simplify an inequality by first calling 'subtractIneq', producing a SOP
-- term, and then creating a new inequality by moving all the terms with
-- negative coefficients to one side.
--
-- Returns 'Nothing' if it is not able to simplify the original inequality.
simplifyIneq :: Ineq -> Maybe Ineq
simplifyIneq ineq@(x, y, isLE)
  = if x' == x && y' == y
    then Nothing
    else Just (x', y', isLE)
  where
    S ps = subtractIneq ineq
    (neg, pos) = partitionEithers $ map classify ps
    (x', y') =
      if isLE
      then ( S neg, S pos )
      else ( S pos, S neg )
    classify :: CoreProduct -> Either CoreProduct CoreProduct
    classify p@(P (I i : _))
      | i < 0
      = Left $ negateProd p
    classify prod
      = Right prod

negateProd :: CoreProduct -> CoreProduct
negateProd (P (I i : r)) =
  -- preserve normal form
  if i == (-1)
  then
    if null r
    then P [I 1]
    else P r
  else P $ I (negate i) : r
negateProd (P r) = P $ I (-1) : r

-- | Subtract an inequality, in order to either:
--
-- * See if the smallest solution is a natural number
-- * Cancel sums, i.e. monotonicity of addition
--
-- @
-- subtractIneq (2*y <=? 3*x ~ True)  = 3*x + (-2)*y
-- subtractIneq (2*y <=? 3*x ~ False) = -3*x + (-2)*y
-- @
subtractIneq
  :: (CoreSOP, CoreSOP, Bool)
  -> CoreSOP
subtractIneq (x,y,isLE)
  | isLE
  -- NB: keep orientations
  = mergeSOPAdd (mergeSOPMul (S [P [I (-1)]]) x) y
  | otherwise
  = mergeSOPAdd x (mergeSOPMul (S [P [I (-1)]]) (mergeSOPAdd y (S [P [I 1]])))

-- | Give the smallest solution for an inequality
ineqToSubst
  :: Ineq
  -> Maybe CoreUnify
ineqToSubst (x,S [P [V v]],True)
  = Just (SubstItem v x)
ineqToSubst _
  = Nothing

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
substsSOP :: (Outputable v, Outputable c, Ord v, Ord c) => [UnifyItem v c] -> SOP v c -> SOP v c
substsSOP []                   u = u
substsSOP ((SubstItem {..}):s) u = substsSOP s (substSOP siVar siSOP u)
substsSOP ((UnifyItem {}):s)   u = substsSOP s u

substSOP :: (Outputable v, Outputable c, Ord v, Ord c) => v -> SOP v c -> SOP v c -> SOP v c
substSOP tv e = foldr mergeSOPAdd (S []) . map (substProduct tv e) . unS

substProduct :: (Outputable v, Outputable c, Ord v, Ord c) => v -> SOP v c -> Product v c -> SOP v c
substProduct tv e = foldr1 mergeSOPMul . map (substSymbol tv e) . unP

substSymbol :: (Outputable v, Outputable c, Ord v, Ord c) => v -> SOP v c -> Symbol v c -> SOP v c
substSymbol _  _ s@(I _) = S [P [s]]
substSymbol _  _ s@(C _) = S [P [s]]
substSymbol tv e (V tv')
  | tv == tv'            = e
  | otherwise            = S [P [V tv']]
substSymbol tv e (E s p) = normaliseExp (substSOP tv e s) (substProduct tv e p)

-- | Apply a substitution to a substitution
substsSubst :: (Outputable v, Outputable c, Ord v, Ord c) => [UnifyItem v c] -> [UnifyItem v c] -> [UnifyItem v c]
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
-- where @u@ and @v@ are only equal when the returned 'CoreSubst' holds.
unifyNats :: Ct -> CoreSOP -> CoreSOP -> TcPluginM Solve UnifyResult
unifyNats ct u v = do
  tcPluginTrace "unifyNats" (ppr ct $$ ppr u $$ ppr v)
  return (unifyNats' ct u v)

unifyNats' :: Ct -> CoreSOP -> CoreSOP -> UnifyResult
unifyNats' ct u v
  | u == v
  = Win
  | Just unifs <- unifiers ct u v
  , let newUnifs = if isGiven (ctEvidence ct)
                   then unifs
                   else filter diffFromConstraint unifs
  = Draw newUnifs
  | otherwise
  = Lose
  where

    -- A unifier is only a unifier if it differs from the original constraint
    diffFromConstraint (UnifyItem x y) = not (x == u && y == v)

    -- SubstItems can be in different orders
    diffFromConstraint (SubstItem x y) =
      not $ (S [P [V x]] == u && y == v)
         || (S [P [V x]] == v && y == u)

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
unifiers :: Ct -> CoreSOP -> CoreSOP -> Maybe [CoreUnify]
unifiers ct u@(S [P [V x]]) v
  | EqPred NomEq t1 _ <- classifyPredType $ ctEvPred $ ctEvidence ct
  , CType (reifySOP u) /= CType t1 || isGiven (ctEvidence ct)
  = return [SubstItem x v]
unifiers ct u v@(S [P [V x]])
  | EqPred NomEq _ t2 <- classifyPredType $ ctEvPred $ ctEvidence ct
  , CType (reifySOP v) /= CType t2 || isGiven (ctEvidence ct)
  = return [SubstItem x u]
unifiers ct u@(S [P [C _]]) v
  | EqPred NomEq t1 t2 <- classifyPredType $ ctEvPred $ ctEvidence ct
  , CType (reifySOP u) /= CType t1 || CType (reifySOP v) /= CType t2
  = return [UnifyItem u v]
unifiers ct u v@(S [P [C _]])
  | EqPred NomEq t1 t2 <- classifyPredType $ ctEvPred $ ctEvidence ct
  , CType (reifySOP u) /= CType t1 || CType (reifySOP v) /= CType t2
  = return [UnifyItem u v]
unifiers ct u v             = unifiers' ct u v

unifiers' :: Ct -> CoreSOP -> CoreSOP -> Maybe [CoreUnify]
unifiers' _ct (S [])        (S [])        = return []

unifiers' _ct (S [P [V x]]) (S [])        = return [SubstItem x (S [P [I 0]])]
unifiers' _ct (S [])        (S [P [V x]]) = return [SubstItem x (S [P [I 0]])]

unifiers' _ct (S [P [V x]]) s = do
  guard $ canBeNatural s
  return [SubstItem x s]
unifiers' _ct s (S [P [V x]]) = do
  guard $ canBeNatural s
  return [SubstItem x s]
unifiers' _ct s1@(S [P [C {}]]) s2@(S [P [C {}]])
  | s1 == s2
  = return []

-- (z ^ a) ~ (z ^ b) ==> [a := b]
unifiers' ct (S [P [E s1 p1]]) (S [P [E s2 p2]])
  | s1 == s2 = unifiers' ct (S [p1]) (S [p2])

-- (2*e ^ d) ~ (2*e*a*c) ==> [a*c := 2*e ^ (d-1)]
unifiers' ct (S [P [E (S [P s1]) p1]]) (S [P p2])
  | all (`elem` p2) s1
  = let base = intersect s1 p2
        diff = p2 \\ s1
    in  unifiers' ct (S [P diff]) (S [P [E (S [P base]) (P [I (-1)]),E (S [P base]) p1]])

unifiers' ct (S [P p2]) (S [P [E (S [P s1]) p1]])
  | all (`elem` p2) s1
  = let base = intersect s1 p2
        diff = p2 \\ s1
    in  unifiers' ct (S [P [E (S [P base]) (P [I (-1)]),E (S [P base]) p1]]) (S [P diff])

-- (i ^ a) ~ j ==> [a := round (logBase i j)], when `i` and `j` are integers,
-- and `ceiling (logBase i j) == floor (logBase i j)`
unifiers' ct (S [P [E (S [P [I i]]) p]]) (S [P [I j]])
  | Just k <- integerLogBase i j
  = unifiers' ct (S [p]) (S [P [I k]])

unifiers' ct (S [P [I j]]) (S [P [E (S [P [I i]]) p]])
  | Just k <- integerLogBase i j
  = unifiers' ct (S [p]) (S [P [I k]])

-- a^d * a^e ~ a^c ==> [c := d + e]
unifiers' ct (S [P [E s1 p1]]) (S [p2])
  | Just (b:bs,ps) <- collectBases p2
  , all (== s1) (b:bs)
  = unifiers' ct (S [p1]) (S ps)

unifiers' ct (S [p2]) (S [P [E s1 p1]])
  | Just (b:bs,ps) <- collectBases p2
  , all (== s1) (b:bs)
  = unifiers' ct (S ps) (S [p1])

-- (i * a) ~ j ==> [a := div j i]
-- Where 'a' is a variable, 'i' and 'j' are integer literals, and j `mod` i == 0
unifiers' ct (S [P ((I i):ps)]) (S [P [I j]])
  | Just k <- safeDiv j i
  = unifiers' ct (S [P ps]) (S [P [I k]])

unifiers' ct (S [P [I j]]) (S [P ((I i):ps)])
  | Just k <- safeDiv j i
  = unifiers' ct (S [P ps]) (S [P [I k]])

-- (2*a) ~ (2*b) ==> [a := b]
-- unifiers' ct (S [P (p:ps1)]) (S [P (p':ps2)])
--     | p == p'   = unifiers' ct (S [P ps1]) (S [P ps2])
--     | otherwise = []
unifiers' ct (S [P ps1]) (S [P ps2])
  | not $ null psx
  = unifiers' ct (S [P ps1'']) (S [P ps2''])
  where
    ps1'  = ps1 \\ psx
    ps2'  = ps2 \\ psx
    ps1'' | null ps1' = [I 1]
          | otherwise = ps1'
    ps2'' | null ps2' = [I 1]
          | otherwise = ps2'
    psx  = intersect ps1 ps2

-- (a + c) ~ (b + c) ==> [a := b]
--
-- NB: this also handles situations such as (2 + x) ~ 5 ==> [x := 3].
unifiers' ct s1@(S ps1) s2@(S ps2)
  | Just (s1',s2',_) <- simplifyIneq (s1, s2, True)
  = unifiers' ct s1' s2'
  | Just term_unifs <- termByTerm ct ps1 ps2
  = Just term_unifs
  -- If there are only two variables, try to collect them on either side.
  -- This makes 'termByTerm' more likely to succeed.
  | Just (S coll1, S coll2) <- partitionTerms ps1 ps2
  , Just term_unifs <- termByTerm ct coll1 coll2
  = Just term_unifs
  | null psx
  , isGiven (ctEvidence ct)
  = unifiers'' ct (S ps1) (S ps2)
  | not $ null psx
  = unifiers' ct (S ps1'') (S ps2'')
  where
    ps1'  = ps1 \\ psx
    ps2'  = ps2 \\ psx
    ps1'' | null ps1' = [P [I 0]]
          | otherwise = ps1'
    ps2'' | null ps2' = [P [I 0]]
          | otherwise = ps2'
    psx = intersect ps1 ps2

unifiers' _ s1 s2 = return [UnifyItem s1 s2]

-- | Try to match the two expressions term-by-term.
-- If this produces a **single unifier**, then we succeed.
--
-- Example: x + 3^(x+2) ~ 2*y - 3^(2*(y+1))
--
-- We recur on each pair, (x, 2*y), (3^(x+2),3^(2*(y+1))).
-- This produces a single unifier "x ~ 2*y", so we proceed.
--
-- NB: this is somewhat fragile: if one moves the terms with negative
-- coefficients to the other side, due to the variable ordering x < y,
-- we would get:
--
--   x + 3^(2*(y+1)) ~ 3^(x+2) + 2*y
--
-- for which the same approach fails. So we use 'partitionTerms' as a heuristic
-- in the case there are only two free variables.
-- See https://github.com/clash-lang/ghc-typelits-natnormalise/issues/96.
termByTerm :: Ct -> [CoreProduct] -> [CoreProduct] -> Maybe [CoreUnify]
termByTerm ct ps1 ps2
  | length ps1 == length ps2
  , length ps1 > 1
  , Just u@[_] <- unifs
  = Just u
  | otherwise
  = Nothing
  where
    unifs = fmap (nub . concat) (zipWithM (\x y -> unifiers' ct (S [x]) (S [y])) ps1 ps2)

-- | If an equality only contains two free variables, try to collect
-- terms with either FV on either side of the equality.
--
-- This makes 'termByTerm' more likely to succeed.
partitionTerms :: [CoreProduct] -> [CoreProduct] -> Maybe (CoreSOP, CoreSOP)
partitionTerms lhs rhs
  | [fv1, fv2] <- fvs
  , Just (lhs1, lhs2) <- mbPairs fv1 fv2 lhs
  , Just (rhs1, rhs2) <- mbPairs fv1 fv2 rhs
  = Just $
      let (lhs', rhs') =
            if length rhs1 + length lhs2 <= length lhs1 + length rhs2
            then (lhs1 ++ map negateProd rhs1, map negateProd lhs2 ++ rhs2)
            else (map negateProd lhs1 ++ rhs1, lhs2 ++ map negateProd rhs2)
      in (simplifySOP (S lhs'), simplifySOP (S rhs'))
  | otherwise
  = Nothing
  where
    fvs :: [TyVar]
    fvs = nonDetEltsUniqSet $ fvSOP (S $ lhs ++ rhs)

    mbPairs :: TyVar -> TyVar -> [CoreProduct] -> Maybe ([CoreProduct], [CoreProduct])
    mbPairs fv1 fv2 x = partitionEithers <$> traverse ( collect fv1 fv2 ) x

    collect :: TyVar -> TyVar -> CoreProduct -> Maybe (Either CoreProduct CoreProduct)
    collect fv1 fv2 tm =
      let tmFvs = fvProduct tm
      in case (fv1 `elementOfUniqSet` tmFvs, fv2 `elementOfUniqSet` tmFvs) of
           (True, False) -> Just $ Left  tm
           (False, True) -> Just $ Right tm
           _             -> Nothing

unifiers'' :: Ct -> CoreSOP -> CoreSOP -> Maybe [CoreUnify]
unifiers'' ct (S [P [I i],P [V v]]) s2
  | isGiven (ctEvidence ct)
  , let s' = mergeSOPAdd s2 (S [P [I (negate i)]])
  = if canBeNatural s'
    then Just [SubstItem v s']
    else Nothing
unifiers'' ct s1 (S [P [I i],P [V v]])
  | isGiven (ctEvidence ct)
  , let s' = mergeSOPAdd s1 (S [P [I (negate i)]])
  = if canBeNatural s'
    then Just [SubstItem v s']
    else Nothing
unifiers'' _ _ _ = Just []

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

-- | Might this be a natural number?
--
-- Equivalently: it is not the case that this is definitely not a natural number.
--
-- For example, @-1@ is definitely not a natural number, while @α@ or
-- @-2 * β@ could both be natural numbers (where @α, β@ are metavariables).
canBeNatural :: CoreSOP -> Bool
canBeNatural = maybe True fst . runWriterT . isNatural

-- | Is this a natural number?
--
--  - @Just True@ <=> definitely a natural number
--  - @Just False@ <=> definitely not a natural number
--  - @Nothing@ <=> not sure
--
-- The 'Set CType' writer accumulator returns inner types that must also be
-- positive for the overall 'CoreSOP' to be positive.
isNatural :: CoreSOP -> WriterT (Set CType) Maybe Bool
isNatural (S [])           = return True
isNatural (S [P []])       = return True
isNatural (S [P (I i:ps)]) =
  case compare i 0 of
    EQ -> return True
    GT ->
      -- NB: assumes the SOP term has been normalised, so no possibly of
      -- a second negative constant factor to cancel out this one.
      isNatural (S [P ps])
    LT ->
      -- '-1 * ty' can be a natural number if 'ty' ends up being zero
      if any canBeZero ps
      then WriterT Nothing
      else return False
isNatural (S [P (V _:ps)]) = isNatural (S [P ps])
isNatural (S [P (E s p:ps)]) = do
  sN <- isNatural s
  pN <- isNatural (S [p])
  if sN && pN
     then isNatural (S [P ps])
     else WriterT Nothing
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

-- | Can this 'CoreSymbol' be zero?
--
-- Examples:
--
--  - the literal '0',
--  - a metavariable,
--  - a type family application.
canBeZero :: CoreSymbol -> Bool
canBeZero (I i) = i == 0
canBeZero (C {}) = True -- e.g. 'F 3' where 'F' is a type family
canBeZero (E (S es) _)
  | [P bs] <- es
  = any canBeZero bs
  | otherwise
  = True
canBeZero (V {}) = True -- e.g. 'tau' where 'tau' is an unfilled metavariable

-- | Try to solve inequalities
solveIneq
  :: Word
  -- ^ Solving depth
  -> Ineq
  -- ^ Inequality we want to solve
  -> Ineq
  -- ^ Given/proven inequality
  -> WriterT (Set CType) Maybe Bool
  -- ^ Solver result
  --
  -- * /Nothing/: exhausted solver steps
  --
  -- * /Just True/: inequality is solved
  --
  -- * /Just False/: solver is unable to solve inequality, note that this does
  -- __not__ mean the wanted inequality does not hold.
solveIneq 0 _ _ = noRewrite
solveIneq k want@(_,_,True) have@(_,_,True)
  | want == have
  = pure True
  | otherwise
  = do
    let -- Apply all the rules, and get all the successful ones
        new     = mapMaybe (\f -> runWriterT (f want have)) ineqRules
        -- Recurse down with all the transformed equations
        solved  = map (first (mapMaybe (runWriterT . uncurry (solveIneq (k-1))))) new
        -- For the results of every recursive call, find the one that yields
        -- 'True' and has the smallest set of constraints.
        solved1 = map (first solvedInEqSmallestConstraint) solved
        -- Union the constraints from the corresponding rewrites with the
        -- constraints from the recursive results
        solved2 = map (\((b,s1),s2) -> (b,Set.union s1 s2)) solved1
        -- From these results, again find the single result that yields 'True'
        -- and has the smallest set of constraints.
        solved3 = solvedInEqSmallestConstraint solved2
    if null solved then
      noRewrite
    else do
      WriterT (Just solved3)

solveIneq _ _ _ = pure False

-- Find the solved inequality with the fewest number of constraints
solvedInEqSmallestConstraint :: [(Bool,Set a)] -> (Bool, Set a)
solvedInEqSmallestConstraint = go (False, Set.empty)
 where
  go bs [] = bs
  go (b,s) ((b1,s1):solved)
    | not b && b1
    = go (b1,s1) solved
    | b && b1
    , Set.size s >  Set.size s1
    = go (b1,s1) solved
    | otherwise
    = go (b,s) solved

-- | Try to instantly solve an inequality by using the inequality solver using
-- @1 <=? 1 ~ True@ as the given constraint.
instantSolveIneq
  :: Word
  -- ^ Solving depth
  -> Ineq
  -- ^ Inequality we want to solve
  -> WriterT (Set CType) Maybe Bool
instantSolveIneq k u = solveIneq k u (one,one,True)
 where
  one = S [P [I 1]]

type Ineq = (CoreSOP, CoreSOP, Bool)
type IneqRule = Ineq -> Ineq  -> WriterT (Set CType) Maybe [(Ineq,Ineq)]

noRewrite :: WriterT (Set CType) Maybe a
noRewrite = WriterT Nothing

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
  = pure [(want,(a,y,le))]
  -- want: y <=? 10 ~ True
  -- have: y <=? 9 ~ True
  --
  -- new want: want
  -- new have: y <=? 10 ~ True
  | S [P [I b']] <- b
  , S [P [I y']] <- y
  , y' < b'
  = pure [(want,(x,b,le))]
leTrans _ _ = noRewrite

-- | Monotonicity of addition
--
-- We use SOP normalization to apply this rule by e.g.:
--
-- * Given: (2*x+1) <= (3*x-1)
-- * Turn to: (3*x-1) - (2*x+1)
-- * SOP version: -2 + x
-- * Convert back to inequality: 2 <= x
plusMonotone :: IneqRule
plusMonotone want have =
  case (simplifyIneq want, simplifyIneq have) of
    (Just want', Just have') -> pure [(want', have')]
    (Just want', _         ) -> pure [(want', have )]
    (_         , Just have') -> pure [(want , have')]
    _ -> noRewrite

-- | Make the `a` of a given `a <= b` smaller
haveSmaller :: IneqRule
haveSmaller want have
  | (S (x:y:ys),us,True) <- have
  = pure [(want,(S (x:ys),us,True))
    ,(want,(S (y:ys),us,True))
    ]
  | (S [P [I 1]], S [P (I _:p@(_:_))],True) <- have
  = pure [(want,(S [P [I 1]],S [P p],True))]
haveSmaller _ _ = noRewrite

-- | Make the `b` of a given `a <= b` bigger
haveBigger :: IneqRule
haveBigger want have
  | (_ ,S vs,True) <- want
  , (as,S bs,True) <- have
  , let vs' = vs \\ bs
  , not (null vs')
  -- want : a <= x + 1
  -- have : y <= x
  --
  -- new want: want
  -- new have: y <= x + 1
  = do
    -- Ensure that we're actually making the RHS larger
    b <- isNatural (S vs')
    if b then
      pure [(want,(as,mergeSOPAdd (S bs) (S vs'),True))]
    else
      noRewrite
haveBigger _ _ = noRewrite

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
  = pure [(want,(mergeSOPMul az x, mergeSOPMul az y,le))]

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
  = pure [(want,(mergeSOPMul bz x, mergeSOPMul bz y,le))]

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
  = pure [((mergeSOPMul xz a, mergeSOPMul xz b,le),have)]

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
  = pure [((mergeSOPMul yz a, mergeSOPMul yz b,le),have)]

timesMonotone _ _ = noRewrite

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
        -> pure [(want,(S [xP],S [yP],le))]
        -- want: XXX
        -- have: x^2 <=? y^2 ~ True
        --
        -- new want: want
        -- new have: x <=? y ~ True
        | xP == yP
        -> pure [(want,(xS,yS,le))]
        -- want: XXX
        -- have: 2 <=? 2 ^ x ~ True
        --
        -- new want: want
        -- new have: 1 <=? x ~ True
      _ | x == yS
        -> pure [(want,(S [P [I 1]],S [yP],le))]
      _ -> noRewrite

powMonotone (a,S [P [E bS bP]],le) have
  = case a of
      S [P [E aS aP]]
        -- want: 2^x <=? 2^y ~ True
        -- have: XXX
        --
        -- new want: x <=? y ~ True
        -- new have: have
        | aS == bS
        -> pure [((S [aP],S [bP],le),have)]
        -- want: x^2 <=? y^2 ~ True
        -- have: XXX
        --
        -- new want: x <=? y ~ True
        -- new have: have
        | aP == bP
        -> pure [((aS,bS,le),have)]
        -- want: 2 <=? 2 ^ x ~ True
        -- have: XXX
        --
        -- new want: 1 <=? x ~ True
        -- new have: XXX
      _ | a == bS
        -> pure [((S [P [I 1]],S [bP],le),have)]
      _ -> noRewrite

powMonotone _ _ = noRewrite

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
  = pure [((a',b',le),have)]
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
  = pure [(want,(x',y',le))]
pow2MonotoneSpecial _ _ = noRewrite

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
