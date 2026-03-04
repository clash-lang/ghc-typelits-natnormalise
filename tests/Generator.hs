{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleInstances #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Generator where

import Prelude hiding (const, exponent)

import Control.Monad (replicateM)
import Data.Maybe (fromJust)

import Hedgehog hiding (eval, Var)
import Hedgehog.Gen
import Hedgehog.Range
import GHC.Utils.Outputable (Outputable(..), char, showPprUnsafe)

import GHC.TypeLits.Normalise.SOP

instance (Outputable v, Outputable c) => Show (SOP v c) where
  show = showPprUnsafe

class Evaluate a where
  eval :: (Model v) -> (Model c) -> a v c -> Maybe Integer

instance Evaluate Symbol where
  eval ev ec = \case
    V v -> getModel ev v
    C c -> getModel ec c
    I i -> Just i
    E b e -> do
      b' <- eval ev ec b
      e' <- eval ev ec e
      if e' < 0
        then Nothing
        else Just (b' ^ e')

instance Evaluate Product where
  eval ev ec (P ps) =
    foldr (*) 1 <$> mapM (eval ev ec) ps

instance Evaluate SOP where
  eval ev ec (S ss) =
    foldr (+) 0 <$> mapM (eval ev ec) ss

defaultSop :: MonadGen m => m (SOP Var Const)
defaultSop =
  sop
    var
    const
    (\d -> integral $ linear 0 (10 - d))
    4

sop :: MonadGen m => m v -> m c -> (Int -> m Int) -> Int -> m (SOP v c)
sop varGen cnstGen breadth depth = do
  sopLen <- case depth of
    0 -> pure 1
    _ -> breadth depth

  let depth' = if sopLen <= 1 then depth else depth - 1

  parts <- replicateM sopLen $ prod varGen cnstGen breadth depth'
  return $ S parts

prod :: MonadGen m => m v -> m c -> (Int -> m Int) -> Int -> m (Product v c)
prod varGen cnstGen breadth depth = do
  prodLen <- case depth of
    0 -> pure 1
    _ -> breadth depth

  let depth' = if prodLen <= 1 then depth else depth - 1

  parts <- replicateM prodLen $ sym varGen cnstGen breadth depth'
  return $ P parts

sym :: MonadGen m => m v -> m c -> (Int -> m Int) -> Int -> m (Symbol v c)
sym varGen cnstGen breadth = \case
  0 -> leaf
  d -> frequency [(1, leaf), (3, branch d)]
 where
  leaf = choice [i, v, c]

  i = I <$> someInt
  v = V <$> varGen
  c = C <$> cnstGen

  branch depth =
    E
      <$> sop varGen cnstGen breadth (depth - 1)
      <*> exponent depth

  exponent _depth =
    pure $ P [I 1]

  -- This becomes too large sometimes :(
  -- exponent depth =
  --   frequency
  --   [ (3, choice $ pure <$> [P [I 1], P [I 2]])
  --   , (1, prod varGen cnstGen breadth (depth - 1))
  --   ]

vars, consts :: [Char]
vars   = "abcde" -- "fghijklmnopqrstuvwxyz"
consts = "αβγδε" -- "ζηθικλμνξοπρστυφχψω"

data Var = Var Char deriving (Eq, Ord)
data Const = Const Char deriving (Eq, Ord)

instance Outputable Var where
  ppr (Var v) = char v

instance Outputable Const where
  ppr (Const c) = char c

showMaybeInt :: Maybe Integer -> String
showMaybeInt Nothing  = "⊥"
showMaybeInt (Just i) = show i

newtype Model k = Model { getModel :: k -> Maybe Integer }

instance Show (Model Var) where
  show (Model m) = "{" ++ foldr (\v acc -> [v] ++ " = " ++ showMaybeInt (m (Var v)) ++ "; " ++ acc) "" vars ++ "}"

instance Show (Model Const) where
  show (Model m) = "{" ++ foldr (\c acc -> [c] ++ " = " ++ showMaybeInt (m (Const c)) ++ "; " ++ acc) "" consts ++ "}"

var :: MonadGen m => m Var
var = choice $ pure . Var <$> vars

const :: MonadGen m => m Const
const = choice $ pure . Const <$> consts

varModel :: MonadGen m => m (Maybe Integer) -> m (Model Var)
varModel i = do
  model <- mapM (\v -> (v,) <$> i) vars
  return $ Model $ \(Var v) -> fromJust (lookup v model)

constModel :: MonadGen m => m (Maybe Integer) -> m (Model Const)
constModel i = do
  model <- mapM (\v -> (v,) <$> i) consts
  return $ Model $ \(Const c) -> fromJust (lookup c model)

maybeFail :: MonadGen m => m a -> m (Maybe a)
maybeFail g = frequency [(99, Just <$> g), (1, pure Nothing)]

someInt :: MonadGen m => m Integer
someInt =
  choice [smallInt, bigInt]
 where
  smallInt = choice $ pure <$> [0, 1, -1, 2]
  bigInt = integral $ linear (-10_000) (10_000)
