{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

import GHC.TypeLits
import Unsafe.Coerce
import Prelude hiding (head,tail,init,(++),splitAt,concat,drop)
import qualified Prelude as P

import Data.List (isInfixOf)
import Data.Proxy
import Control.Exception
import Test.Tasty
import Test.Tasty.HUnit

import ErrorTests

data Vec :: Nat -> * -> * where
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

data UNat :: Nat -> * where
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

-- | Extract the elements after the head of a vector
--
-- >>> tail (1:>2:>3:>Nil)
-- <2,3>
tail :: Vec (n + 1) a -> Vec n a
tail (_ :> xs) = xs

-- | Extract all the elements of a vector except the last element
--
-- >>> init (1:>2:>3:>Nil)
-- <1,2>
init :: Vec (n + 1) a -> Vec n a
init (_ :> Nil)      = Nil
init (x :> y :> ys) = x :> init (y :> ys)

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
    ]
  , testGroup "errors"
    [ testCase "x + 2 ~ 3 + x" $ testProxy1 `throws` testProxy1Errors
    , testCase "GCD 6 8 + x ~ x + GCD 9 6" $ testProxy2 `throws` testProxy2Errors
    , testCase "Unify \"x + x + x\" with \"8\"" $ testProxy3 `throws` testProxy3Errors
    , testCase "Unify \"(2*x)+4\" with \"2\"" $ testProxy4 `throws` testProxy4Errors
    , testCase "Unify \"(2*x)+4\" with \"7\"" $ testProxy5 `throws` testProxy5Errors
    , testCase "Unify \"2^k\" with \"7\"" $ testProxy6 `throws` testProxy6Errors
    , testCase "x ~ y + x" $ testProxy8 `throws` testProxy8Errors
    , testCase "(CLog 2 (2 ^ n) ~ n, (1 <=? n) ~ True) => n ~ (n+d)" $ (testProxy15 (Proxy :: Proxy 1)) `throws` testProxy15Errors
    , testGroup "Inequality"
      [ testCase "a+1 <= a" $ testProxy9 `throws` testProxy9Errors
      , testCase "(a <=? a+1) ~ False" $ testProxy10 `throws` testProxy10Errors
      , testCase "(a <=? a) ~ False" $ testProxy11 `throws` testProxy11Errors
      , testCase "() => (a+b <= a+c)" $ testProxy12 `throws` testProxy12Errors
      , testCase "4a <= 2a" $ testProxy13 `throws` testProxy13Errors
      , testCase "2a <=? 4a ~ False" $ testProxy14 `throws` testProxy14Errors
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
