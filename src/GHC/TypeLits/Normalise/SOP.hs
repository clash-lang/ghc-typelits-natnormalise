module GHC.TypeLits.Normalise.SOP where

-- External
import Data.Either (partitionEithers)
import Data.List   (sort)

-- GHC API
import Type
import Outputable
import TypeRep
import TysWiredIn
import TcTypeNats

data Symbol
  = I Integer
  | V TyVar
  | E SOP Product
  deriving (Eq,Ord)

newtype Product = P { unP :: [Symbol] }
  deriving (Eq,Ord)

newtype SOP = S { unS :: [Product] }
  deriving (Eq,Ord)

instance Outputable SOP where
  ppr = hcat . punctuate (text " + ") . map ppr . unS

instance Outputable Product where
  ppr = hcat . punctuate (text " * ") . map ppr . unP

instance Outputable Symbol where
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
reduceExp :: Symbol -> Symbol
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
mergeS :: Symbol -> Symbol -> Either Symbol Symbol
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
mergeP :: Product -> Product -> Either Product Product
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


-- expandExp :: SOP -> SOP -> SOP
-- expandExp b         [[(I 1)]]    = b
-- expandExp b@[[S _]] [e]          = [[E b e]]
-- expandExp b@([[_]]) [e@([_])]    = [[reduceExp (E b e)]]
-- expandExp b         e@[[(I i)]]  = foldr1 mergeSOPMul (replicate (fromInteger i) b)
-- expandExp b         [e@(I _):es] = expandExp (expandExp b [[e]]) [es]
-- expandExp b         [es]         = [[reduceExp (E b es)]]
-- expandExp b         e            = foldr1 mergeSOPMul (map (expandExp b . (:[])) e)

-- | Expand or Simplify 'complex' exponentials
normaliseExp :: SOP -> SOP -> SOP
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
normaliseExp b (S [P (e@(I i):es)]) =
  normaliseExp (normaliseExp b (S [P [e]])) (S [P es])

-- (x + 2)^(xy) ==> (x+2)^(xy)
normaliseExp b (S [e]) = S [P [reduceExp (E b e)]]

-- (x + 2)^(y + 2) ==> 4x(2 + x)^y + 4(2 + x)^y + (2 + x)^yx^2
normaliseExp b (S e) = foldr1 mergeSOPMul (map (normaliseExp b . S . (:[])) e)

normaliseNat :: Type -> Maybe SOP
normaliseNat ty | Just ty1 <- tcView ty = normaliseNat ty1
normaliseNat (TyVarTy v)          = pure (S [P [V v]])
normaliseNat (LitTy (NumTyLit i)) = pure (S [P [I i]])
normaliseNat (TyConApp tc tys)
  | tc == typeNatAddTyCon, [x,y] <- tys = mergeSOPAdd  <$> normaliseNat x <*> normaliseNat y
  | tc == typeNatSubTyCon, [x,y] <- tys = mergeSOPAdd  <$> normaliseNat x <*> (mergeSOPMul (S [P [I (-1)]]) <$> normaliseNat y)
  | tc == typeNatMulTyCon, [x,y] <- tys = mergeSOPMul  <$> normaliseNat x <*> normaliseNat y
  | tc == typeNatExpTyCon, [x,y] <- tys = normaliseExp <$> normaliseNat x <*> normaliseNat y
  | otherwise                           = Nothing

reifySOP :: SOP -> Type
reifySOP = combineP . map negateP . unS
  where
    negateP :: Product -> Either Product Product
    negateP (P ((I i):ps)) | i < 0 = Left  (P ps)
    negateP ps                     = Right ps

    combineP :: [Either Product Product] -> Type
    combineP [p]    = either (\p' -> mkTyConApp typeNatSubTyCon
                                                [mkNumLitTy 0, reifyProduct p'])
                             reifyProduct p
    combineP (p:ps) = let es = combineP ps
                      in  either (\x -> mkTyConApp typeNatSubTyCon [es, reifyProduct x])
                                 (\x -> mkTyConApp typeNatAddTyCon [reifyProduct x, es])
                                 p

reifyProduct :: Product -> Type
reifyProduct = foldr1 (\t1 t2 -> mkTyConApp typeNatMulTyCon [t1,t2]) . map reifySymbol . unP

reifySymbol :: Symbol -> Type
reifySymbol (I i)   = mkNumLitTy i
reifySymbol (V v)   = mkTyVarTy v
reifySymbol (E s p) = mkTyConApp typeNatExpTyCon [reifySOP s,reifyProduct p]

zeroP :: Product -> Bool
zeroP (P ((I 0):_)) = True
zeroP _             = False

simplifySOP :: SOP -> SOP
simplifySOP
  = S
  . sort . filter (not . zeroP)
  . mergeWith mergeP
  . map (P . sort . map reduceExp . mergeWith mergeS . unP)
  . unS

mergeSOPAdd :: SOP -> SOP -> SOP
mergeSOPAdd (S sop1) (S sop2) = simplifySOP $ S (sop1 ++ sop2)

mergeSOPMul :: SOP -> SOP -> SOP
mergeSOPMul (S sop1) (S sop2)
  = simplifySOP
  . S
  $ concatMap (zipWith (\p1 p2 -> P (unP p1 ++ unP p2)) sop1 . repeat) sop2
