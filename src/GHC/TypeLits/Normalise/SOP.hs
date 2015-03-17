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

data Op = Add | Sub | Mul | Exp
  deriving Eq

data Expr
  = Lit Integer
  | Var TyVar
  | Op Op Expr Expr
  deriving Eq

data Symbol
  = I Integer
  | V TyVar
  | E SOP Product
  deriving (Eq,Ord)

newtype Product = P { unP :: [Symbol] }
  deriving (Eq,Ord)

newtype SOP = S { unS :: [Product] }
  deriving (Eq,Ord)

instance Outputable Expr where
  ppr (Lit i) = integer i
  ppr (Var v) = ppr v
  ppr (Op op e1 e2) = parens (ppr e1) <+> parens (ppr e2)

instance Outputable Op where
  ppr Add = text "+"
  ppr Sub = text "-"
  ppr Mul = text "*"
  ppr Exp = text "^"

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


reifyUnit :: Expr -> Type
reifyUnit (Lit i)  = mkNumLitTy i
reifyUnit (Var tv) = mkTyVarTy  tv
reifyUnit (Op op e1 e2) = mkTyConApp (tc op) [reifyUnit e1, reifyUnit e2]
  where
    tc Add = typeNatAddTyCon
    tc Sub = typeNatSubTyCon
    tc Mul = typeNatMulTyCon
    tc Exp = typeNatExpTyCon

mergeWith :: (a -> a -> Either a a) -> [a] -> [a]
mergeWith _ []      = []
mergeWith op (f:fs) = case partitionEithers $ map (`op` f) fs of
                        ([],_)              -> f : mergeWith op fs
                        (updated,untouched) -> mergeWith op (updated ++ untouched)

isSimple :: Symbol -> Bool
isSimple (I _)             = True
isSimple (V _)             = True
isSimple (E (S [P [_]]) _) = True
isSimple _                 = False

-- | Simplify 'complex' symbols
reduceSymbol :: Symbol -> Symbol
reduceSymbol (E _                 (P [(I 0)])) = I 1        -- x^0 ==> 1
reduceSymbol (E (S [P [I 0]])     _          ) = I 0        -- 0^x ==> 0
reduceSymbol (E (S [P [(I i)]])   (P [(I j)])) = I (i ^ j)  -- 2^3 ==> 8

-- (k ^ i) ^ j ==> k ^ (i * j)
reduceSymbol (E (S [P [(E k i)]]) j          ) = E k (P . sort . map reduceSymbol
                                                        $ mergeWith mergeS (unP i ++ unP j))

reduceSymbol s                                 = s

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
  | l == r && isSimple l
  = Left (E (S [P [l]]) (P [I 2]))

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

-- | Expand or Simplify 'complex' exponentials
expandExp :: SOP -> SOP -> SOP
-- b^1 ==> b
expandExp b (S [P [(I 1)]]) = b

-- x^y ==> x^y
expandExp b@(S [P [_]]) (S [e@(P (_:_))]) = S [P [reduceSymbol (E b e)]]

-- (x + 2)^2 ==> x^2 + 4xy + 4
expandExp b (S [P [(I i)]]) = foldr1 mergeSOPMul (replicate (fromInteger i) b)

-- (x + 2)^x ==> (x+2)^x
expandExp b (S [e@(P [_])]) = S [P [reduceSymbol (E b e)]]

-- (x + 2)^(x + 2) ==> (x + y)^y + x^2 + 4xy + 4
expandExp b (S e) = foldr1 mergeSOPMul (map (expandExp b . S . (:[])) e)

toSOP :: Expr -> SOP
toSOP (Lit i)        = S [P [I i]]
toSOP (Var s)        = S [P [V s]]
toSOP (Op Add e1 e2) = mergeSOPAdd (toSOP e1) (toSOP e2)
toSOP (Op Sub e1 e2) = mergeSOPAdd (toSOP e1) (mergeSOPMul (S [P [I (-1)]]) (toSOP e2))
toSOP (Op Mul e1 e2) = mergeSOPMul (toSOP e1) (toSOP e2)
toSOP (Op Exp e1 e2) = expandExp   (toSOP e1) (toSOP e2)

zeroP :: Product -> Bool
zeroP (P ((I 0):_)) = True
zeroP _             = False

simplifySOP :: SOP -> SOP
simplifySOP
  = S
  . sort . filter (not . zeroP)
  . mergeWith mergeP
  . map (P . sort . map reduceSymbol . mergeWith mergeS . unP)
  . unS

mergeSOPAdd :: SOP -> SOP -> SOP
mergeSOPAdd (S sop1) (S sop2) = simplifySOP $ S (sop1 ++ sop2)

mergeSOPMul :: SOP -> SOP -> SOP
mergeSOPMul (S sop1) (S sop2)
  = simplifySOP
  . S
  $ concatMap (zipWith (\p1 p2 -> P (unP p1 ++ unP p2)) sop1 . repeat) sop2
