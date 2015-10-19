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

proxyFun3 :: Proxy (x + x + x) -> ()
proxyFun3 = const ()

testProxy3 :: Proxy 8 -> ()
testProxy3 = proxyFun3

testProxy3Errors =
  ["Expected type: Proxy 8 -> ()"
  ,"Actual type: Proxy ((x0 + x0) + x0) -> ()"
  ]

proxyFun4 :: Proxy ((2*y)+4) -> ()
proxyFun4 = const ()

testProxy4 :: Proxy 2 -> ()
testProxy4 = proxyFun4

testProxy4Errors =
  ["Expected type: Proxy 2 -> ()"
  ,"Actual type: Proxy ((2 * y0) + 4) -> ()"
  ]

testProxy5 :: Proxy 7 -> ()
testProxy5 = proxyFun4

testProxy5Errors =
  ["Expected type: Proxy 7 -> ()"
  ,"Actual type: Proxy ((2 * y1) + 4) -> ()"
  ]

proxyFun6 :: Proxy (2^k) -> Proxy (2^k)
proxyFun6 = const Proxy

testProxy6 :: Proxy 7
testProxy6 = proxyFun6 (Proxy :: Proxy 7)

testProxy6Errors =
  ["Expected type: Proxy (2 ^ k0)"
  ,"Actual type: Proxy 7"
  ]

proxyFun7 :: Proxy (2^k) -> Proxy k
proxyFun7 = const Proxy
