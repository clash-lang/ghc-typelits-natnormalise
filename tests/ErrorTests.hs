{-# LANGUAGE DataKinds, KindSignatures, TypeFamilies, TypeOperators #-}

{-# OPTIONS_GHC -fdefer-type-errors #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module ErrorTests where

import Data.Proxy
import GHC.TypeLits

testProxy1 :: Proxy (x + 1) -> Proxy (2 + x)
testProxy1 = id

testProxy1Errors =
  ["Expected type: Proxy (x + 1) -> Proxy (2 + x)"
  ,"Actual type: Proxy (2 + x) -> Proxy (2 + x)"
  ]

type family GCD (x :: Nat) (y :: Nat) :: Nat
type instance GCD 6 8 = 2
type instance GCD 9 6 = 3

testProxy2 :: Proxy (GCD 6 8 + x) -> Proxy (x + GCD 9 6)
testProxy2 = id

testProxy2Errors =
  ["Expected type: Proxy (GCD 6 8 + x) -> Proxy (x + GCD 9 6)"
  ,"Actual type: Proxy (x + 3) -> Proxy (x + 3)"
  ]
