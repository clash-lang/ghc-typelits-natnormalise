{-# LANGUAGE DataKinds, KindSignatures, TemplateHaskell, TypeFamilies, TypeOperators #-}

{-# OPTIONS_GHC -fdefer-type-errors #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module ErrorTests where

import Data.Proxy
import GHC.TypeLits

import GHC.IO.Encoding            (getLocaleEncoding, textEncodingName, utf8)
import Language.Haskell.TH        (litE, stringL)
import Language.Haskell.TH.Syntax (runIO)

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

testProxy8 :: Proxy x -> Proxy (y + x)
testProxy8 = id

testProxy8Errors =
  ["Expected type: Proxy x -> Proxy (y + x)"
  ,"Actual type: Proxy x -> Proxy x"
  ]

proxyInEq :: (a <= b) => Proxy a -> Proxy b -> ()
proxyInEq _ _ = ()

proxyInEq' :: ((a <=? b) ~ 'False) => Proxy a -> Proxy b -> ()
proxyInEq' _ _ = ()

testProxy9 :: Proxy (a + 1) -> Proxy a -> ()
testProxy9 = proxyInEq

testProxy9Errors =
  [$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "Couldn't match type ‘(a + 1) <=? a’ with ‘'True’"
          else litE $ stringL "Couldn't match type `(a + 1) <=? a' with 'True"
    )]

testProxy10 :: Proxy (a :: Nat) -> Proxy (a + 2) -> ()
testProxy10 = proxyInEq'

testProxy10Errors =
  [$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "Couldn't match type ‘a <=? (a + 2)’ with ‘'False’"
          else litE $ stringL "Couldn't match type `a <=? (a + 2)' with 'False"
    )]

testProxy11 :: Proxy (a :: Nat) -> Proxy a -> ()
testProxy11 = proxyInEq'

testProxy11Errors =
  [$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "Couldn't match type ‘'True’ with ‘'False’"
          else litE $ stringL "Couldn't match type 'True with 'False"
    )]

testProxy12 :: Proxy (a + b) -> Proxy (a + c) -> ()
testProxy12 = proxyInEq

testProxy12Errors =
  [$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "Couldn't match type ‘(a + b) <=? (a + c)’ with ‘'True’"
          else litE $ stringL "Couldn't match type `(a + b) <=? (a + c)' with 'True"
    )]

testProxy13 :: Proxy (4*a) -> Proxy (2*a) ->()
testProxy13 = proxyInEq

testProxy13Errors =
  [$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "Couldn't match type ‘(4 * a) <=? (2 * a)’ with ‘'True’"
          else litE $ stringL "Couldn't match type `(4 * a) <=? (2 * a)' with 'True"
    )]

testProxy14 :: Proxy (2*a) -> Proxy (4*a) -> ()
testProxy14 = proxyInEq'

testProxy14Errors =
  [$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "Couldn't match type ‘(2 * a) <=? (4 * a)’ with ‘'False’"
          else litE $ stringL "Couldn't match type `(2 * a) <=? (4 * a)' with 'False"
    )]

type family CLog (b :: Nat) (x :: Nat) :: Nat
type instance CLog 2 2 = 1

testProxy15 :: (CLog 2 (2 ^ n) ~ n, (1 <=? n) ~ True) => Proxy n -> Proxy (n+d)
testProxy15 = id

testProxy15Errors =
  ["Expected type: Proxy n -> Proxy (n + d)"
  ,"Actual type: Proxy n -> Proxy n"
  ]
