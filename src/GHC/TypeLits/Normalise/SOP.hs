{-|
Copyright  :  (C) 2015, University of Twente
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>
-}
module GHC.TypeLits.Normalise.SOP where

-- External
import Data.Either (partitionEithers)
import Data.List   (sort)

-- GHC API
import Outputable  (Outputable (..), (<+>), text, hcat, integer, punctuate)

data Symbol a
  = I Integer
  | V a
  | E (SOP a) (Product a)
  deriving (Eq,Ord)

newtype Product a = P { unP :: [Symbol a] }
  deriving (Eq,Ord)

newtype SOP a = S { unS :: [Product a] }
  deriving (Eq,Ord)

instance Outputable a => Outputable (SOP a) where
  ppr = hcat . punctuate (text " + ") . map ppr . unS

instance Outputable a => Outputable (Product a) where
  ppr = hcat . punctuate (text " * ") . map ppr . unP

instance Outputable a => Outputable (Symbol a) where
  ppr (I i)   = integer i
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

-- | Simplify 'complex' exponentials
reduceExp :: (Eq a, Ord a) => Symbol a -> Symbol a
reduceExp (E _                 (P [(I 0)])) = I 1        -- x^0 ==> 1
reduceExp (E (S [P [I 0]])     _          ) = I 0        -- 0^x ==> 0
reduceExp (E (S [P [(I i)]])   (P [(I j)])) = I (i ^ j)  -- 2^3 ==> 8

-- (k ^ i) ^ j ==> k ^ (i * j)
reduceExp (E (S [P [(E k i)]]) j) = case normaliseExp k (S [e]) of
    (S [P [s]]) -> s
    _           -> E k e
  where
    e = (P . sort . map reduceExp $ mergeWith mergeS (unP i ++ unP j))

reduceExp s = s

-- | Merge two symbols of a Product term
mergeS :: (Eq a, Ord a) => Symbol a -> Symbol a -> Either (Symbol a) (Symbol a)
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

-- y*y ==> y^2
mergeS l r
  | l == r
  = case normaliseExp (S [P [l]]) (S [P [I 2]]) of
      (S [P [e]]) -> Left  e
      _           -> Right l

mergeS l _ = Right l

-- | Merge two products of a SOP term
mergeP :: (Eq a, Ord a) => Product a -> Product a
       -> Either (Product a) (Product a)
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
normaliseExp :: Ord a => SOP a -> SOP a -> SOP a
-- b^1 ==> b
normaliseExp b (S [P [I 1]]) = b

-- x^(2xy) ==> x^(2xy)
normaliseExp b@(S [P [V _]]) (S [e]) = S [P [E b e]]

-- 2^(y^2) ==> 4^y
normaliseExp b@(S [P [_]]) (S [e@(P [_])]) = S [P [reduceExp (E b e)]]

-- (x + 2)^2 ==> x^2 + 4xy + 4
normaliseExp b (S [P [(I i)]]) =
  foldr1 mergeSOPMul (replicate (fromInteger i) b)

-- (x + 2)^(2x) ==> (x^2 + 4xy + 4)^x
normaliseExp b (S [P (e@(I _):es)]) =
  normaliseExp (normaliseExp b (S [P [e]])) (S [P es])

-- (x + 2)^(xy) ==> (x+2)^(xy)
normaliseExp b (S [e]) = S [P [reduceExp (E b e)]]

-- (x + 2)^(y + 2) ==> 4x(2 + x)^y + 4(2 + x)^y + (2 + x)^yx^2
normaliseExp b (S e) = foldr1 mergeSOPMul (map (normaliseExp b . S . (:[])) e)

zeroP :: Product a -> Bool
zeroP (P ((I 0):_)) = True
zeroP _             = False

simplifySOP :: Ord a => SOP a -> SOP a
simplifySOP
  = S
  . sort . filter (not . zeroP)
  . mergeWith mergeP
  . map (P . sort . map reduceExp . mergeWith mergeS . unP)
  . unS

mergeSOPAdd :: Ord a => SOP a -> SOP a -> SOP a
mergeSOPAdd (S sop1) (S sop2) = simplifySOP $ S (sop1 ++ sop2)

mergeSOPMul :: Ord a =>  SOP a -> SOP a -> SOP a
mergeSOPMul (S sop1) (S sop2)
  = simplifySOP
  . S
  $ concatMap (zipWith (\p1 p2 -> P (unP p1 ++ unP p2)) sop1 . repeat) sop2
