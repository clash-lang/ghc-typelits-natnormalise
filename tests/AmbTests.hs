{-# LANGUAGE CPP #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
#if __GLASGOW_HASKELL__ >= 805
{-# LANGUAGE NoStarIsType #-}
#endif

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -dcore-lint #-}

module AmbTests where

import GHC.TypeLits

leToPlus2
  :: forall (k :: Nat) (n :: Nat) r
   . ( k <= n
     )
  => (forall m . (n ~ (k + m)) => r)
  -- ^ Context with the (k + m ~ n) constraint
  -> r
leToPlus2 r = r @(n - k)
{-# INLINE leToPlus2 #-}

newtype BitVector (n :: Nat) = BV Integer

class BitPack a where
  type BitSize a :: Nat

split :: forall a m n .
  (BitPack a, BitSize a ~ (m + n)) =>
  a ->
  (BitVector m, BitVector n)
split = split

lastBits
  :: forall n a
   . ( BitPack a
     , n <= BitSize a
     , KnownNat (BitSize a)
     , KnownNat n
     )
  => a
  -> BitVector n
lastBits = leToPlus2 @n @(BitSize a) $ snd . split @_ @_ @n
