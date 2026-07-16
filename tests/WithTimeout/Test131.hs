-- Test for https://github.com/clash-lang/ghc-typelits-natnormalise/issues/131
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}

#if __GLASGOW_HASKELL__ >= 805
{-# LANGUAGE NoStarIsType              #-}
#endif

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Main where

import GHC.TypeLits
-- This file is compiled by a bare GHC invocation (see the unit-tests suite),
-- so Cabal's MIN_VERSION macros are not available: base-4.18 came with GHC 9.6.
#if __GLASGOW_HASKELL__ >= 906
  hiding (type SNat)
#endif

import Data.Singletons (Apply, TyFun, type (@@))
import Data.Proxy (Proxy (..))
import Data.Kind (Type)


data SNat (n :: Nat) = KnownNat n => SNat (Proxy n)

data Vec :: Nat -> Type -> Type where
  Nil  :: Vec 0 a
  (:>) :: a -> Vec n a -> Vec (n + 1) a

data RTree :: Nat -> Type -> Type where
  LR :: a -> RTree 0 a
  BR :: RTree d a -> RTree d a -> RTree (d+1) a

data PowT (k :: Nat) (a :: Type) (f :: TyFun Nat Type) :: Type
type instance Apply (PowT k a) d = Vec (k^(2^d)) (RTree d a)

instance Functor (Vec n) where
  fmap = undefined

tdfold :: forall p k a . KnownNat k
       => Proxy (p :: TyFun Nat Type -> Type)
       -> (a -> (p @@ 0))
       -> (forall l . SNat l -> (p @@ l) -> (p @@ l) -> (p @@ (l+1)))
       -> RTree k a
       -> (p @@ k)
tdfold _ _f _g = undefined

trepeat :: KnownNat d => a -> RTree d a
trepeat = undefined

vConcatMap :: (a -> Vec m b) -> Vec n a -> Vec (n * m) b
vConcatMap _f _xs = undefined

type family MyTF a :: Nat where
  MyTF Int = 3
  MyTF _   = 5

t131 :: forall d a. KnownNat d => Vec (MyTF a) a -> Vec (MyTF a^(2^d)) (RTree d a)
t131 v = tdfold
  (Proxy @(PowT (MyTF a) a))
  (const $ LR <$> v)
  (\(_ :: SNat m) l r -> vConcatMap ((<$> r) . BR) l)
  (trepeat @d ())

main :: IO ()
main = putStrLn "OK"
