{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE TypeOperators     #-}
{-# LANGUAGE NoImplicitPrelude #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

import Data.Proxy
import GHC.TypeLits
import Unsafe.Coerce
import Prelude hiding (head,tail,init,(++),splitAt,concat,drop)
import qualified Prelude as P

import Test.Tasty
import Test.Tasty.HUnit

data Vec :: Nat -> * -> * where
  Nil  :: Vec 0 a
  (:>) :: a -> Vec n a -> Vec (n + 1) a

instance Show a => Show (Vec n a) where
  show vs = "<" P.++ punc vs P.++ ">"
    where
      punc :: Show a => Vec m a -> String
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
    ]
  ]
