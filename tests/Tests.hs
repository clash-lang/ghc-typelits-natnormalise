{-# LANGUAGE CPP                       #-}
{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FunctionalDependencies    #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoImplicitPrelude         #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE RoleAnnotations           #-}
{-# LANGUAGE Rank2Types                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}

#if __GLASGOW_HASKELL__ >= 805
{-# LANGUAGE NoStarIsType              #-}
#endif

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -dcore-lint #-}

import GHC.TypeLits
#if MIN_VERSION_base(4,18,0)
  hiding (type SNat)
#endif

import Unsafe.Coerce
import Prelude hiding (head,tail,init,(++),splitAt,concat,drop)
import qualified Prelude as P

import Data.Kind (Type)
import Data.List (isInfixOf)
import Data.Proxy
import Control.Exception
import Test.Tasty
import Test.Tasty.HUnit

import ErrorTests

data Vec :: Nat -> Type -> Type where
  Nil  :: Vec 0 a
  (:>) :: a -> Vec n a -> Vec (n + 1) a

instance Show a => Show (Vec n a) where
  show vs = "<" P.++ punc vs P.++ ">"
    where
      punc :: Vec m a -> String
      punc Nil        = ""
      punc (x :> Nil) = show x
      punc (x :> xs)  = show x P.++ "," P.++ punc xs

infixr 5 :>

data SNat (n :: Nat) = KnownNat n => SNat (Proxy n)

instance Show (SNat n) where
  show (SNat p) = 'd' : show (natVal p)

{-# INLINE snat #-}
-- | Create a singleton literal for a type-level natural number
snat :: KnownNat n => SNat n
snat = SNat Proxy

{-# INLINE withSNat #-}
-- | Supply a function with a singleton natural 'n' according to the context
withSNat :: KnownNat n => (SNat n -> a) -> a
withSNat f = f (SNat Proxy)

{-# INLINE snatToInteger #-}
snatToInteger :: SNat n -> Integer
snatToInteger (SNat p) = natVal p

data UNat :: Nat -> Type where
  UZero :: UNat 0
  USucc :: UNat n -> UNat (n + 1)

-- | Convert a singleton natural number to its unary representation
--
-- __NB__: Not synthesisable
toUNat :: SNat n -> UNat n
toUNat (SNat p) = fromI (natVal p)
  where
    fromI :: Integer -> UNat m
    fromI 0 = unsafeCoerce UZero
    fromI n = unsafeCoerce (USucc (fromI (n - 1)))

-- | Add two singleton natural numbers
--
-- __NB__: Not synthesisable
addUNat :: UNat n -> UNat m -> UNat (n + m)
addUNat UZero     y     = y
addUNat x         UZero = x
addUNat (USucc x) y     = USucc (addUNat x y)

-- | Multiply two singleton natural numbers
--
-- __NB__: Not synthesisable
multUNat :: UNat n -> UNat m -> UNat (n * m)
multUNat UZero      _     = UZero
multUNat _          UZero = UZero
multUNat (USucc x) y      = addUNat y (multUNat x y)

-- | Exponential of two singleton natural numbers
--
-- __NB__: Not synthesisable
powUNat :: UNat n -> UNat m -> UNat (n ^ m)
powUNat _ UZero     = USucc UZero
powUNat x (USucc y) = multUNat x (powUNat x y)

-- | Extract the first element of a vector
--
-- >>> head (1:>2:>3:>Nil)
-- 1
head :: Vec (n + 1) a -> a
head (x :> _) = x

head'
  :: forall n a
   . (1 <= n)
  => Vec n a
  -> a
head' = head @(n-1)

-- | Extract the elements after the head of a vector
--
-- >>> tail (1:>2:>3:>Nil)
-- <2,3>
tail :: Vec (n + 1) a -> Vec n a
tail (_ :> xs) = xs

tail' :: (1 <= m) => Vec m a -> Vec (m-1) a
tail' = tail

-- | Extract all the elements of a vector except the last element
--
-- >>> init (1:>2:>3:>Nil)
-- <1,2>
init :: Vec (n + 1) a -> Vec n a
init (_ :> Nil)     = Nil
init (x :> y :> ys) = x :> init (y :> ys)

init' :: (1 <= m) => Vec m a -> Vec (m-1) a
init' = init

infixr 5 ++
-- | Append two vectors
--
-- >>> (1:>2:>3:>Nil) ++ (7:>8:>Nil)
-- <1,2,3,7,8>
(++) :: Vec n a -> Vec m a -> Vec (n + m) a
Nil       ++ ys = ys
(x :> xs) ++ ys = x :> xs ++ ys

-- | Split a vector into two vectors at the given point
--
-- >>> splitAt (snat :: SNat 3) (1:>2:>3:>7:>8:>Nil)
-- (<1,2,3>, <7,8>)
-- >>> splitAt d3 (1:>2:>3:>7:>8:>Nil)
-- (<1,2,3>, <7,8>)
splitAt :: SNat m -> Vec (m + n) a -> (Vec m a, Vec n a)
splitAt n xs = splitAtU (toUNat n) xs

splitAtU :: UNat m -> Vec (m + n) a -> (Vec m a, Vec n a)
splitAtU UZero     ys        = (Nil,ys)
splitAtU (USucc s) (y :> ys) = let (as,bs) = splitAtU s ys
                               in  (y :> as, bs)

{-# INLINE splitAtI #-}
-- | Split a vector into two vectors where the length of the two is determined
-- by the context
--
-- >>> splitAtI (1:>2:>3:>7:>8:>Nil) :: (Vec 2 Int, Vec 3 Int)
-- (<1,2>,<3,7,8>)
splitAtI :: KnownNat m => Vec (m + n) a -> (Vec m a, Vec n a)
splitAtI = withSNat splitAt

-- | Shift in elements to the head of a vector, bumping out elements at the
-- tail. The result is a tuple containing:
--
-- * The new vector
-- * The shifted out elements
--
-- >>> shiftInAt0 (1 :> 2 :> 3 :> 4 :> Nil) ((-1) :> 0 :> Nil)
-- (<-1,0,1,2,>,<3,4>)
-- >>> shiftInAt0 (1 :> Nil) ((-1) :> 0 :> Nil)
-- (<-1>,<0,1>)
shiftInAt0 :: KnownNat n
           => Vec n a -- ^ The old vector
           -> Vec m a -- ^ The elements to shift in at the head
           -> (Vec n a, Vec m a) -- ^ (The new vector, shifted out elements)
shiftInAt0 xs ys = splitAtI zs
  where
    zs = ys ++ xs

-- | Shift in element to the tail of a vector, bumping out elements at the head.
-- The result is a tuple containing:
--
-- * The new vector
-- * The shifted out elements
--
-- >>> shiftInAtN (1 :> 2 :> 3 :> 4 :> Nil) (5 :> 6 :> Nil)
-- (<3,4,5,6>,<1,2>)
-- >>> shiftInAtN (1 :> Nil) (2 :> 3 :> Nil)
-- (<3>,<1,2>)
shiftInAtN :: KnownNat m
           => Vec n a -- ^ The old vector
           -> Vec m a -- ^ The elements to shift in at the tail
           -> (Vec n a,Vec m a) -- ^ (The new vector, shifted out elements)
shiftInAtN xs ys = (zsR, zsL)
  where
    zs        = xs ++ ys
    (zsL,zsR) = splitAtI zs

-- | Concatenate a vector of vectors
--
-- >>> concat ((1:>2:>3:>Nil) :> (4:>5:>6:>Nil) :> (7:>8:>9:>Nil) :> (10:>11:>12:>Nil) :> Nil)
-- <1,2,3,4,5,6,7,8,9,10,11,12>
concat :: Vec n (Vec m a) -> Vec (n * m) a
concat Nil       = Nil
concat (x :> xs) = x ++ concat xs

-- | Split a vector of (n * m) elements into a vector of vectors with length m,
-- where m is given
--
-- >>> unconcat d4 (1:>2:>3:>4:>5:>6:>7:>8:>9:>10:>11:>12:>Nil)
-- <<1,2,3,4>,<5,6,7,8>,<9,10,11,12>>
unconcat :: KnownNat n => SNat m -> Vec (n * m) a -> Vec n (Vec m a)
unconcat n xs = unconcatU (withSNat toUNat) (toUNat n) xs

unconcatU :: UNat n -> UNat m -> Vec (n * m) a -> Vec n (Vec m a)
unconcatU UZero      _ _  = Nil
unconcatU (USucc n') m ys = let (as,bs) = splitAtU m ys
                            in  as :> unconcatU n' m bs

-- | Merge two vectors, alternating their elements, i.e.,
--
-- >>> merge (1 :> 2 :> 3 :> 4 :> Nil) (5 :> 6 :> 7 :> 8 :> Nil)
-- <1,5,2,6,3,7,4,8>
merge :: Vec n a -> Vec n a -> Vec (n + n) a
merge Nil       Nil       = Nil
merge (x :> xs) (y :> ys) = x :> y :> merge xs ys

-- | 'drop' @n xs@ returns the suffix of @xs@ after the first @n@ elements
--
-- >>> drop (snat :: SNat 3) (1:>2:>3:>4:>5:>Nil)
-- <4,5>
-- >>> drop d3               (1:>2:>3:>4:>5:>Nil)
-- <4,5>
-- >>> drop d0               (1:>2:>Nil)
-- <1,2>
drop :: SNat m -> Vec (m + n) a -> Vec n a
drop n = snd . splitAt n

drop' :: (m <= k) => SNat m -> Vec k a -> Vec (k - m) a
drop' = drop

-- | 'at' @n xs@ returns @n@'th element of @xs@
--
-- __NB__: vector elements have an __ASCENDING__ subscript starting from 0 and
-- ending at 'maxIndex'.
--
-- >>> at (snat :: SNat 1) (1:>2:>3:>4:>5:>Nil)
-- 2
-- >>> at d1               (1:>2:>3:>4:>5:>Nil)
-- 2
at :: SNat m -> Vec (m + (n + 1)) a -> a
at n xs = head $ snd $ splitAt n xs

at'
  :: forall k m a
   . (1 <= k, m <= (k-1))
   => SNat m
   -> Vec k a
   -> a
at' = at @m @(k - 1 - m)

leToPlus
  :: forall (k :: Nat) (n :: Nat) (f :: Nat -> Type) (r :: Type)
   . (k <= n)
  => Proxy k
  -> f n
  -- ^ Argument with the @(k <= n)@ constraint
  -> (forall (m :: Nat) . f (m + k) -> r)
  -- ^ Function with the @(n + k)@ constraint
  -> r
leToPlus _ a f = f @(n-k) a

data BNat :: Nat -> Type where
  BT :: BNat 0
  B0 :: BNat n -> BNat (2*n)
  B1 :: BNat n -> BNat ((2*n) + 1)

instance KnownNat n => Show (BNat n) where
  show x = 'b':show (natVal x)

predBNat :: (1 <= n) => BNat n -> BNat (n-1)
predBNat (B1 a) = case a of
  BT -> BT
  a' -> B0 a'
predBNat (B0 x)  = B1 (predBNat x)

-- issue 52 begin
type role Signal nominal representational
data Signal (dom :: Symbol) a = a :- Signal dom a

type role BitVector nominal
newtype BitVector (n :: Nat) = BV { unsafeToNatural :: Integer }

class Bundle (f :: Type -> Type) a res | f a -> res, f res -> a, a res -> f
bundle :: Bundle f a res => res -> f a
bundle = bundle

instance Bundle (Signal dom) (a,b) (Signal dom a, Signal dom b)

issue52 :: (1 <= n, KnownNat n) => (Signal dom (),Signal dom (BitVector (n-1+1))) -> Signal dom ((),BitVector n)
issue52 = bundle
-- issue 52 end

proxyInEq1 :: Proxy a -> Proxy (a+1) -> ()
proxyInEq1 = proxyInEq

proxyInEq2 :: Proxy ((a+1) :: Nat) -> Proxy a -> ()
proxyInEq2 = proxyInEq'

proxyInEq3 :: Proxy (a :: Nat) -> Proxy (a+b) -> ()
proxyInEq3 = proxyInEq

proxyInEq4 :: Proxy (2*a) -> Proxy (4*a) -> ()
proxyInEq4 = proxyInEq

proxyInEq5 :: Proxy 1 -> Proxy (2^a) -> ()
proxyInEq5 = proxyInEq

proxyInEq6 :: Proxy 1 -> Proxy (a + 3) -> ()
proxyInEq6 = proxyInEq

proxyInEq7 :: Proxy 1 -> Proxy (2^(a + 3)) -> ()
proxyInEq7 = proxyInEq

proxyEq1
  :: (1 <= x)
  => Proxy ((2 ^ x) * (2 ^ (x + x)))
  -> Proxy (2 * (2 ^ ((x + (x + x)) - 1)))
proxyEq1 = id

proxyEq2
  :: (2 <= x)
  => Proxy (((2 ^ x) - 2) * (2 ^ (x + x)))
  -> Proxy ((2 ^ ((x + (x + x)) - 1)) + ((2 ^ ((x + (x + x)) - 1)) - (2 ^ ((x + x) + 1))))
proxyEq2 = id

proxyEq3
  :: forall x y
   . ((x + 1) ~ (2 * y), 1 <= y)
  => Proxy x
  -> Proxy y
  -> Proxy (((2 * (y - 1)) + 1))
  -> Proxy x
proxyEq3 _ _ x = x

-- Would yield (b <=? c) ~ 'True
proxyEq4
  :: forall a b c
   . (KnownNat a, c <= b, b <= a)
  => Proxy b
  -> Proxy c
  -> Proxy a
  -> Proxy (((a - b) + c) + (b - c))
proxyEq4 = theProxy
 where
  theProxy
    :: forall a b c
     . (KnownNat (((a - b) + c) + (b - c)), c <= b, b <= a)
    => Proxy b
    -> Proxy c
    -> Proxy a
    -> Proxy (((a - b) + c) + (b - c))
  theProxy _ _ = id

proxyInEqImplication :: (2 <= (2 ^ (n + d)))
  => Proxy d
  -> Proxy n
  -> Proxy n
proxyInEqImplication = proxyInEqImplication'

proxyInEqImplication' :: (2 <= (2 ^ (d + n)))
  => Proxy d
  -> Proxy n
  -> Proxy n
proxyInEqImplication' _ = id

proxyEqSubst
  :: ((n+1) ~ ((n1 + m) + 1), m ~ n1, n1 ~ ((n2 + m1) + 1))
  => Proxy n1
  -> Proxy n2
  -> Proxy m1
  -> Proxy n
  -> Proxy m
  -> Proxy (1 + (n2 + m1))
  -> Proxy n1
proxyEqSubst _ _ _ _ _ = id

proxyInEqImplication2
  :: forall n n1 n2
   . (n1 ~ (n2 + 1), (2^n) ~ (n1 + 1))
  => Proxy n1
  -> Proxy n2
  -> Proxy n
  -> Proxy ((n - 1) + 1)
  -> Proxy n
proxyInEqImplication2 _ _ _ x = x

type family F (n :: Nat) :: Nat
type instance F 3 = 8

proxyInEqImplication3 :: (KnownNat (F n))
  => Proxy (n :: Nat)
  -> Proxy (n :: Nat)
proxyInEqImplication3 = proxyInEqImplication3'

proxyInEqImplication3' :: (F n <= (3 * (F n)))
  => Proxy (n :: Nat)
  -> Proxy (n :: Nat)
proxyInEqImplication3' = id

type family G (n :: Nat) :: Nat
type instance G 2 = 3

proxyInEqImplication4 :: (1 <= (G n))
  => Proxy (n :: Nat)
  -> Proxy (n :: Nat)
proxyInEqImplication4 = proxyInEqImplication4'

proxyInEqImplication4' :: (F n <= ((G n) * (F n)))
  => Proxy (n :: Nat)
  -> Proxy (n :: Nat)
proxyInEqImplication4' = id

data AtMost n = forall a. (KnownNat a, a <= n) => AtMost (Proxy a)

instance Show (AtMost n) where
  show (AtMost (x :: Proxy a)) = "AtMost " P.++ show (natVal x)

succAtMost :: AtMost n -> AtMost (n + 1)
succAtMost (AtMost (Proxy :: Proxy a)) = AtMost (Proxy :: Proxy a)

eqReduceForward
  :: Eq (Boo (n + 1))
  => Dict (Eq (Boo (n + 2 - 1)))
eqReduceForward = Dict

eqReduceForwardMinusPlus
  :: (Eq (Boo (0 + n + 1)), 1 <= n)
  => Dict (Eq (Boo (n - 1 + 2)))
eqReduceForwardMinusPlus = Dict

eqReduceBackward
  :: (Eq (Boo (m + 2 - 1)))
  => Dict (Eq (Boo (m + 1)))
eqReduceBackward = Dict

eqReduceBackward'
  :: (Eq (Boo (1 + m + 2)))
  => Dict (Eq (Boo (m + 3)))
eqReduceBackward' = Dict

proxyInEq8fun
  :: (1 <= (n + CLog 2 n))
  => Proxy n
  -> Proxy n
proxyInEq8fun = id

proxyInEq8
  :: (1 <= n, KnownNat (CLog 2 n))
  => Proxy n
  -> Proxy n
proxyInEq8 = proxyInEq8fun

data H2 = H2 { p :: Nat }

class Q (dom :: Symbol) where
  type G2 dom :: H2

type family P (c :: H2) :: Nat where
  P ('H2 p) = p

type F2 (dom :: Symbol) = P (G2 dom)

type Dom = "System"

instance Q Dom where
  type G2 Dom = 'H2 2

tyFamMonotonicityFun :: (1 <= F2 dom) => Proxy (dom :: Symbol) -> ()
tyFamMonotonicityFun _ = ()

tyFamMonotonicity :: (2 <= F2 dom) => Proxy (dom :: Symbol) -> ()
tyFamMonotonicity dom = tyFamMonotonicityFun dom

oneLtPowSubst :: forall a b. (b ~ (2^a)) => Proxy a -> Proxy a
oneLtPowSubst = go
  where
    go :: 1 <= b => Proxy a -> Proxy a
    go = id

givenLEZeroNotImpossible :: forall (a :: Nat) . a <= 0 => Proxy a -> Proxy 'True
givenLEZeroNotImpossible p = Proxy @((a + a - a) <=? 0)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "ghc-typelits-natnormalise"
  [ testGroup "Basic functionality"
    [ testCase "show (head (1:>2:>3:>Nil))" $
      show (head (1:>2:>3:>Nil)) @?=
      "1"
    , testCase "show (tail (1:>2:>3:>Nil))" $
      show (tail (1:>2:>3:>Nil)) @?=
      "<2,3>"
    , testCase "show (init (1:>2:>3:>Nil))" $
      show (init (1:>2:>3:>Nil)) @?=
      "<1,2>"
    , testCase "show ((1:>2:>3:>Nil) ++ (7:>8:>Nil))" $
      show ((1:>2:>3:>Nil) ++ (7:>8:>Nil)) @?=
      "<1,2,3,7,8>"
    , testCase "show (splitAt (snat :: SNat 3) (1:>2:>3:>7:>8:>Nil))" $
      show (splitAt (snat :: SNat 3) (1:>2:>3:>7:>8:>Nil)) @?=
      "(<1,2,3>,<7,8>)"
    , testCase "show (concat ((1:>2:>3:>Nil) :> (4:>5:>6:>Nil) :> (7:>8:>9:>Nil) :> (10:>11:>12:>Nil) :> Nil))" $
      show (concat ((1:>2:>3:>Nil) :> (4:>5:>6:>Nil) :> (7:>8:>9:>Nil) :> (10:>11:>12:>Nil) :> Nil)) @?=
      "<1,2,3,4,5,6,7,8,9,10,11,12>"
    , testCase "show (unconcat (snat :: SNat 4) (1:>2:>3:>4:>5:>6:>7:>8:>9:>10:>11:>12:>Nil))" $
      show (unconcat (snat :: SNat 4) (1:>2:>3:>4:>5:>6:>7:>8:>9:>10:>11:>12:>Nil)) @?=
      "<<1,2,3,4>,<5,6,7,8>,<9,10,11,12>>"
    , testCase "show (proxyFun3 (Proxy :: Proxy 9))" $
      show (proxyFun3 (Proxy :: Proxy 9)) @?=
      "()"
    , testCase "show (proxyFun4 (Proxy :: Proxy 8))" $
      show (proxyFun4 (Proxy :: Proxy 8)) @?=
      "()"
    , testCase "show (proxyFun7 (Proxy :: Proxy 8) :: Proxy 3)" $
      show (proxyFun7 (Proxy :: Proxy 8) :: Proxy 3) @?=
      "Proxy"
    ]
  , testGroup "Equality"
    [ testCase "((2 ^ x) * (2 ^ (x + x))) ~ (2 * (2 ^ ((x + (x + x)) - 1)))" $
      show (proxyEq1 @1 Proxy) @?=
      "Proxy"
    , testCase "(((2 ^ x) - 2) * (2 ^ (x + x))) ~ ((2 ^ ((x + (x + x)) - 1)) + ((2 ^ ((x + (x + x)) - 1)) - (2 ^ ((x + x) + 1))))" $
      show (proxyEq2 @2 Proxy) @?=
      "Proxy"
    ]
  , testGroup "Implications"
    [ testCase "(x + 1) ~ (2 * y)) implies (((2 * (y - 1)) + 1)) ~ x" $
      show (proxyEq3 (Proxy :: Proxy 3) (Proxy :: Proxy 2) Proxy) @?=
      "Proxy"
    , testCase "(n+1) ~ ((n1 + m) + 1), m ~ n1, n1 ~ ((n2 + m1) + 1) implies n1 ~ 1 + (n2 + m1)" $
      show (proxyEqSubst (Proxy :: Proxy 6) (Proxy :: Proxy 2) (Proxy :: Proxy 3)
                         (Proxy :: Proxy 12) (Proxy :: Proxy 6) (Proxy :: Proxy 6)) @?=
      "Proxy"
    ]
  , testGroup "Inequality"
    [ testCase "a <= a+1" $
      show (proxyInEq1 (Proxy :: Proxy 2) (Proxy :: Proxy 3)) @?=
      "()"
    , testCase "(a+1 <=? a) ~ False" $
      show (proxyInEq2 (Proxy :: Proxy 3) (Proxy :: Proxy 2)) @?=
      "()"
    , testCase "a <= a+b" $
      show (proxyInEq3 (Proxy :: Proxy 2) (Proxy :: Proxy 2)) @?=
      "()"
    , testCase "2a <= 4a" $
      show (proxyInEq4 (Proxy :: Proxy 2) (Proxy :: Proxy 4)) @?=
      "()"
    , testCase "1 <= 2^a" $
      show (proxyInEq5 (Proxy :: Proxy 1) (Proxy :: Proxy 1)) @?=
      "()"
    , testCase "`(2 <= (2 ^ (n + d)))` implies `(2 <= (2 ^ (d + n)))`" $
      show (proxyInEqImplication (Proxy :: Proxy 3) (Proxy :: Proxy 4)) @?=
      "Proxy"
    , testCase "1 <= a+3" $
      show (proxyInEq6 (Proxy :: Proxy 1) (Proxy :: Proxy 8)) @?=
      "()"
    , testCase "`1 <= 2*x` implies `1 <= x`" $
      show (predBNat (B1 (B1 BT))) @?=
      "b2"
    , testCase "`x + 2 <= y` implies `x <= y` and `2 <= y`" $
      show (proxyInEqImplication2 (Proxy :: Proxy 3) (Proxy :: Proxy 2) (Proxy :: Proxy 2) Proxy) @?=
      "Proxy"
    , testCase "`a <= n` implies `a <= (n+1)`" $
      show (succAtMost (AtMost (Proxy :: Proxy 3) :: AtMost 5)) @?=
      "AtMost 3"
    , testCase "1 <= 2^(a+3)" $
      show (proxyInEq7 (Proxy :: Proxy 1) (Proxy :: Proxy 8)) @?=
      "()"
    , testCase "KnownNat (F a) implies F a <= 3 * F a" $
      show (proxyInEqImplication3 (Proxy :: Proxy 3)) @?=
      "Proxy"
    , testCase "1 <= G a implies F a <= G a * F a" $
      show (proxyInEqImplication4 (Proxy :: Proxy 2)) @?=
      "Proxy"
    , testCase "`(1 <= n)` only implies `(1 <= n + F n)` when `KnownNat (F n)`" $
      show (proxyInEq8 (Proxy :: Proxy 2)) @?=
      "Proxy"
    , testCase "2 <= P (G2 dom) implies 1 <= P (G2 dom)" $
      show (tyFamMonotonicity (Proxy :: Proxy Dom)) @?=
      "()"
    , testCase "b ~ (2^a) => 1 <= b" $
      show (oneLtPowSubst (Proxy :: Proxy 0)) @?=
      "Proxy"
    , testCase "a <= 0 is not impossible" $
      givenLEZeroNotImpossible (Proxy @0) @?= Proxy
    ]
  , testGroup "errors"
    [ testCase "x + 2 ~ 3 + x" $ testProxy1 `throws` testProxy1Errors
    , testCase "GCD 6 8 + x ~ x + GCD 9 6" $ testProxy2 `throws` testProxy2Errors
    , testCase "Unify \"x + x + x\" with \"8\"" $ testProxy3 `throws` testProxy3Errors
    , testCase "Unify \"(2*x)+4\" with \"2\"" $ testProxy4 `throws` testProxy4Errors
    , testCase "Unify \"(2*x)+4\" with \"7\"" $ testProxy5 `throws` testProxy5Errors
    , testCase "Unify \"2^k\" with \"7\"" $ testProxy6 `throws` testProxy6Errors
    , testCase "x ~ y + x" $ testProxy8 `throws` testProxy8Errors
    , testCase "(CLog 2 (2 ^ n) ~ n, (1 <=? n) ~ True) => n ~ (n+d)" $
        testProxy15 (Proxy :: Proxy 1) `throws` testProxy15Errors
    , testCase "(n - 1) + 1 ~ n implies (1 <= n)" $ test16 `throws` test16Errors
    , testGroup "Inequality"
      [ testCase "a+1 <= a" $ testProxy9 `throws` testProxy9Errors
      , testCase "(a <=? a+1) ~ False" $ testProxy10 `throws` testProxy10Errors
      , testCase "(a <=? a) ~ False" $ testProxy11 `throws` testProxy11Errors
      , testCase "() => (a+b <= a+c)" $ testProxy12 `throws` testProxy12Errors
      , testCase "4a <= 2a" $ testProxy13 `throws` testProxy13Errors
      , testCase "2a <=? 4a ~ False" $ testProxy14 `throws` testProxy14Errors
      , testCase "Show (Boo n) => Show (Boo (n - 1 + 1))" $
          testProxy17 `throws` test17Errors
      , testCase "1 <= m, m <= rp implies 1 <= rp - m" $ (testProxy19 (Proxy @1) (Proxy @1)) `throws` test19Errors
      , testCase "Vacuously: 1 <= m ^ 2 ~ True" $ testProxy20 `throws` testProxy20Errors
      ]
    ]
  ]

-- | Assert that evaluation of the first argument (to WHNF) will throw
-- an exception whose string representation contains the given
-- substrings.
throws :: a -> [String] -> Assertion
throws v xs = do
  result <- try (evaluate v)
  case result of
    Right _ -> assertFailure "No exception!"
    Left (TypeError msg) ->
      if all (`isInfixOf` msg) xs
         then return ()
         else assertFailure msg

showFin :: forall n. KnownNat n => Fin n -> String
showFin f = mconcat [
  show (finToInt f)
  , "/"
  , show (natVal (Proxy :: Proxy n))
  ]

finToInt :: Fin n -> Int
finToInt FZ      = 0
finToInt (FS fn) = finToInt fn + 1

predFin :: Fin (n + 2) -> Fin (n + 1)
predFin (FS fn) = fn
predFin FZ      = FZ

showSucPred :: KnownNat (n + 2) => Fin (n + 2) -> String
showSucPred = showFin .  FS . predFin

class Up env (n :: Nat) where
  up :: env -> Fin n -> Fin (n + 1)

class Down env (n :: Nat) where
  down :: env -> Fin n -> Fin (n - 1)

class ShowWith env (n :: Nat) where
  showWith :: env -> Fin n -> String

showDownUp
  :: (Up env n, Down env (n + 1), ShowWith env n)
  => env -> Fin n -> String
showDownUp env fn = showWith env $ down env $ up env fn

showDownUp'
  :: (Up env n, Down env (n + 1), KnownNat n)
  => env -> Fin n -> String
showDownUp' env fn = showFin $ down env $ up env fn

data family FakeUVector (n :: Nat) :: Type
data family FakeMUVector (n :: Nat) :: Type
type family Mutable (v :: Nat -> Type) :: Nat -> Type
type instance Mutable FakeUVector = FakeMUVector

class (IsMVector FakeMUVector n, IsVector FakeUVector n)
   => FakeUnbox n
class IsMVector (v :: Nat -> Type) a where
  touchMVector :: v a -> v a
class IsMVector (Mutable v) a => IsVector v a where
  touchVector :: v a -> v a

newtype WrapFakeVector n = WFV { unWrap :: FakeUVector (1 + n) }
newtype WrapFakeMVector n = MWFV { unWrapM :: FakeMUVector (1 + n) }
type instance Mutable WrapFakeVector = WrapFakeMVector

-- The following two instances cannot be derived without simplification phase!
instance FakeUnbox (n + 1) => IsVector WrapFakeVector n where
  touchVector = WFV . touchVector . unWrap
instance FakeUnbox (n + 1) => IsMVector WrapFakeMVector n where
  touchMVector = MWFV . touchMVector . unWrapM
