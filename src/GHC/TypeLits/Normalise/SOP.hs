{-|
Copyright  :  (C) 2015-2016, University of Twente,
                  2017     , QBayLogic B.V.
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>

= SOP: Sum-of-Products, sorta

The arithmetic operation for 'GHC.TypeLits.Nat' are, addition
(@'GHC.TypeLits.+'@), subtraction (@'GHC.TypeLits.-'@), multiplication
(@'GHC.TypeLits.*'@), and exponentiation (@'GHC.TypeLits.^'@). This means we
cannot write expressions in a canonical SOP normal form. We can get rid of
subtraction by working with integers, and translating @a - b@ to @a + (-1)*b@.
Exponentation cannot be getten rid of that way. So we define the following
grammar for our canonical SOP-like normal form of arithmetic expressions:

@
SOP      ::= Product \'+\' SOP | Product
Product  ::= Symbol \'*\' Product | Symbol
Symbol   ::= Integer
          |  Var
          |  Var \'^\' Product
          |  SOP \'^\' ProductE

ProductE ::= SymbolE \'*\' ProductE | SymbolE
SymbolE  ::= Var
          |  Var \'^\' Product
          |  SOP \'^\' ProductE
@

So a valid SOP terms are:

@
x*y + y^2
(x+y)^(k*z)
@

, but,

@
(x*y)^2
@

is not, and should be:

@
x^2 * y^2
@

Exponents are thus not allowed to have products, so for example, the expression:

@
(x + 2)^(y + 2)
@

in valid SOP form is:

@
4*x*(2 + x)^y + 4*(2 + x)^y + (2 + x)^y*x^2
@

Also, exponents can only be integer values when the base is a variable. Although
not enforced by the grammar, the exponentials are flatted as far as possible in
SOP form. So:

@
(x^y)^z
@

is flattened to:

@
x^(y*z)
@
-}

{-# LANGUAGE CPP #-}

module GHC.TypeLits.Normalise.SOP
  ( -- * SOP types
    Symbol (..)
  , Product (..)
  , SOP (..)
    -- * Simplification
  , reduceExp
  , mergeS
  , mergeP
  , mergeSOPAdd
  , mergeSOPMul
  , normaliseExp
  , simplifySOP
  )
where

-- External
import Data.Either (partitionEithers)
import Data.List   (sort)

-- GHC API
#if MIN_VERSION_ghc(9,0,0)
import GHC.Utils.Outputable (Outputable (..), (<+>), text, hcat, integer, punctuate)
#else
import Outputable (Outputable (..), (<+>), text, hcat, integer, punctuate)
#endif

data Symbol v c
  = I Integer                 -- ^ Integer constant
  | C c                       -- ^ Non-integer constant
  | E (SOP v c) (Product v c) -- ^ Exponentiation
  | V v                       -- ^ Variable
  deriving (Eq,Ord)

newtype Product v c = P { unP :: [Symbol v c] }
  deriving (Eq)

instance (Ord v, Ord c) => Ord (Product v c) where
  compare (P [x])   (P [y])   = compare x y
  compare (P [_])   (P (_:_)) = LT
  compare (P (_:_)) (P [_])   = GT
  compare (P xs)    (P ys)    = compare xs ys

newtype SOP v c = S { unS :: [Product v c] }
  deriving (Ord)

instance (Eq v, Eq c) => Eq (SOP v c) where
  (S []) == (S [P [I 0]]) = True
  (S [P [I 0]]) == (S []) = True
  (S ps1) == (S ps2)      = ps1 == ps2

instance (Outputable v, Outputable c) => Outputable (SOP v c) where
  ppr = hcat . punctuate (text " + ") . map ppr . unS

instance (Outputable v, Outputable c) => Outputable (Product v c) where
  ppr = hcat . punctuate (text " * ") . map ppr . unP

instance (Outputable v, Outputable c) => Outputable (Symbol v c) where
  ppr (I i)   = integer i
  ppr (C c)   = ppr c
  ppr (V s)   = ppr s
  ppr (E b e) = case (pprSimple b, pprSimple (S [e])) of
                  (bS,eS) -> bS <+> text "^" <+> eS
    where
      pprSimple (S [P [I i]]) = integer i
      pprSimple (S [P [V v]]) = ppr v
      pprSimple sop           = text "(" <+> ppr sop <+> text ")"

mergeWith :: (a -> a -> Either a a) -> [a] -> [a]
mergeWith _ []      = []
mergeWith op (f:fs) = case partitionEithers $ map (`op` f) fs of
                        ([],_)              -> f : mergeWith op fs
                        (updated,untouched) -> mergeWith op (updated ++ untouched)

-- | reduce exponentials
--
-- Performs the following rewrites:
--
-- @
-- x^0          ==>  1
-- 0^x          ==>  0
-- 2^3          ==>  8
-- (k ^ i) ^ j  ==>  k ^ (i * j)
-- @
reduceExp :: (Ord v, Ord c) => Symbol v c -> Symbol v c
reduceExp (E _                 (P [(I 0)])) = I 1        -- x^0 ==> 1
reduceExp (E (S [P [I 0]])     _          ) = I 0        -- 0^x ==> 0
reduceExp (E (S [P [(I i)]])   (P [(I j)]))
  | j >= 0                                  = I (i ^ j)  -- 2^3 ==> 8

-- (k ^ i) ^ j ==> k ^ (i * j)
reduceExp (E (S [P [(E k i)]]) j) = case normaliseExp k (S [e]) of
    (S [P [s]]) -> s
    _           -> E k e
  where
    e = P . sort . map reduceExp $ mergeWith mergeS (unP i ++ unP j)

reduceExp s = s

-- | Merge two symbols of a Product term
--
-- Performs the following rewrites:
--
-- @
-- 8 * 7    ==>  56
-- 1 * x    ==>  x
-- x * 1    ==>  x
-- 0 * x    ==>  0
-- x * 0    ==>  0
-- x * x^4  ==>  x^5
-- x^4 * x  ==>  x^5
-- y*y      ==>  y^2
-- @
mergeS :: (Ord v, Ord c) => Symbol v c -> Symbol v c
       -> Either (Symbol v c) (Symbol v c)
mergeS (I i) (I j) = Left (I (i * j)) -- 8 * 7 ==> 56
mergeS (I 1) r     = Left r           -- 1 * x ==> x
mergeS l     (I 1) = Left l           -- x * 1 ==> x
mergeS (I 0) _     = Left (I 0)       -- 0 * x ==> 0
mergeS _     (I 0) = Left (I 0)       -- x * 0 ==> 0

-- x * x^4 ==> x^5
mergeS s (E (S [P [s']]) (P [I i]))
  | s == s'
  = Left (E (S [P [s']]) (P [I (i + 1)]))

-- x^4 * x ==> x^5
mergeS (E (S [P [s']]) (P [I i])) s
  | s == s'
  = Left (E (S [P [s']]) (P [I (i + 1)]))

-- 4^x * 2^x ==> 8^x
mergeS (E (S [P [I i]]) p) (E (S [P [I j]]) p')
  | p == p'
  = Left (E (S [P [I (i*j)]]) p)

-- y*y ==> y^2
mergeS l r
  | l == r
  = case normaliseExp (S [P [l]]) (S [P [I 2]]) of
      (S [P [e]]) -> Left  e
      _           -> Right l

-- x^y * x^(-y) ==> 1
mergeS (E s1 (P p1)) (E s2 (P (I i:p2)))
  | i == (-1)
  , s1 == s2
  , p1 == p2
  = Left (I 1)

-- x^(-y) * x^y ==> 1
mergeS (E s1 (P (I i:p1))) (E s2 (P p2))
  | i == (-1)
  , s1 == s2
  , p1 == p2
  = Left (I 1)

mergeS l _ = Right l

-- | Merge two products of a SOP term
--
-- Performs the following rewrites:
--
-- @
-- 2xy + 3xy  ==>  5xy
-- 2xy + xy   ==>  3xy
-- xy + 2xy   ==>  3xy
-- xy + xy    ==>  2xy
-- @
mergeP :: (Eq v, Eq c) => Product v c -> Product v c
       -> Either (Product v c) (Product v c)
-- 2xy + 3xy ==> 5xy
mergeP (P ((I i):is)) (P ((I j):js))
  | is == js = Left . P $ (I (i + j)) : is
-- 2xy + xy  ==> 3xy
mergeP (P ((I i):is)) (P js)
  | is == js = Left . P $ (I (i + 1)) : is
-- xy + 2xy  ==> 3xy
mergeP (P is) (P ((I j):js))
  | is == js = Left . P $ (I (j + 1)) : is
-- xy + xy ==> 2xy
mergeP (P is) (P js)
  | is == js  = Left . P $ (I 2) : is
  | otherwise = Right $ P is

-- | Expand or Simplify 'complex' exponentials
--
-- Performs the following rewrites:
--
-- @
-- b^1              ==>  b
-- 2^(y^2)          ==>  4^y
-- (x + 2)^2        ==>  x^2 + 4xy + 4
-- (x + 2)^(2x)     ==>  (x^2 + 4xy + 4)^x
-- (x + 2)^(y + 2)  ==>  4x(2 + x)^y + 4(2 + x)^y + (2 + x)^yx^2
-- @
normaliseExp :: (Ord v, Ord c) => SOP v c -> SOP v c -> SOP v c
-- b^1 ==> b
normaliseExp b (S [P [I 1]]) = b

-- x^(2xy) ==> x^(2xy)
normaliseExp b@(S [P [V _]]) (S [e]) = S [P [E b e]]

-- 2^(y^2) ==> 4^y
normaliseExp b@(S [P [_]]) (S [e@(P [_])]) = S [P [reduceExp (E b e)]]

-- (x + 2)^2 ==> x^2 + 4xy + 4
normaliseExp b (S [P [(I i)]]) | i > 0 =
  foldr1 mergeSOPMul (replicate (fromInteger i) b)

-- (x + 2)^(2x) ==> (x^2 + 4xy + 4)^x
normaliseExp b (S [P (e@(I i):es)]) | i >= 0 =
  -- Without the "| i >= 0" guard, normaliseExp can loop with itself
  -- for exponentials such as: 2^(n-k)
  normaliseExp (normaliseExp b (S [P [e]])) (S [P es])

-- (x + 2)^(xy) ==> (x+2)^(xy)
normaliseExp b (S [e]) = S [P [reduceExp (E b e)]]

-- (x + 2)^(y + 2) ==> 4x(2 + x)^y + 4(2 + x)^y + (2 + x)^yx^2
normaliseExp b (S e) = foldr1 mergeSOPMul (map (normaliseExp b . S . (:[])) e)

zeroP :: Product v c -> Bool
zeroP (P ((I 0):_)) = True
zeroP _             = False

mkNonEmpty :: SOP v c -> SOP v c
mkNonEmpty (S []) = S [P [(I 0)]]
mkNonEmpty s      = s

-- | Simplifies SOP terms using
--
-- * 'mergeS'
-- * 'mergeP'
-- * 'reduceExp'
simplifySOP :: (Ord v, Ord c) => SOP v c -> SOP v c
simplifySOP = repeatF go
  where
    go = mkNonEmpty
       . S
       . sort . filter (not . zeroP)
       . mergeWith mergeP
       . map (P . sort . map reduceExp . mergeWith mergeS . unP)
       . unS

    repeatF f x =
      let x' = f x
      in  if x' == x
             then x
             else repeatF f x'
{-# INLINEABLE simplifySOP #-}

-- | Merge two SOP terms by additions
mergeSOPAdd :: (Ord v, Ord c) => SOP v c -> SOP v c -> SOP v c
mergeSOPAdd (S sop1) (S sop2) = simplifySOP $ S (sop1 ++ sop2)
{-# INLINEABLE mergeSOPAdd #-}

-- | Merge two SOP terms by multiplication
mergeSOPMul :: (Ord v, Ord c) => SOP v c -> SOP v c -> SOP v c
mergeSOPMul (S sop1) (S sop2)
  = simplifySOP
  . S
  $ concatMap (zipWith (\p1 p2 -> P (unP p1 ++ unP p2)) sop1 . repeat) sop2
{-# INLINEABLE mergeSOPMul #-}
