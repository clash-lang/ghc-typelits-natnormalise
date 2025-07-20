{-# LANGUAGE CPP                 #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

#if __GLASGOW_HASKELL__ >= 805
{-# LANGUAGE NoStarIsType        #-}
#endif

{-# OPTIONS_GHC -fdefer-type-errors #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module ErrorTests where

import Data.Proxy
import GHC.TypeLits
#if __GLASGOW_HASKELL__ >= 904
import GHC.Types
#endif

import GHC.IO.Encoding            (getLocaleEncoding, textEncodingName, utf8)
import Language.Haskell.TH        (litE, stringL)
import Language.Haskell.TH.Syntax (runIO)

#if __GLASGOW_HASKELL__ >= 901
import qualified Data.Type.Ord
#endif

testProxy1 :: Proxy (x + 1) -> Proxy (2 + x)
testProxy1 = id

testProxy1Errors =
#if __GLASGOW_HASKELL__ >= 900
  ["Expected: Proxy (x + 1) -> Proxy (2 + x)"
  ,"  Actual: Proxy (x + 1) -> Proxy (x + 1)"
  ]
#else
  ["Expected type: Proxy (x + 1) -> Proxy (2 + x)"
  ,"Actual type: Proxy (2 + x) -> Proxy (2 + x)"
  ]
#endif

type family GCD (x :: Nat) (y :: Nat) :: Nat
type instance GCD 6 8 = 2
type instance GCD 9 6 = 3

testProxy2 :: Proxy (GCD 6 8 + x) -> Proxy (x + GCD 9 6)
testProxy2 = id

testProxy2Errors =
#if __GLASGOW_HASKELL__ >= 900
  ["Expected: Proxy (GCD 6 8 + x) -> Proxy (x + GCD 9 6)"
  ,"  Actual: Proxy (2 + x) -> Proxy (2 + x)"
  ]
#else
  ["Expected type: Proxy (GCD 6 8 + x) -> Proxy (x + GCD 9 6)"
  ,"Actual type: Proxy (x + 3) -> Proxy (x + 3)"
  ]
#endif

proxyFun3 :: Proxy (x + x + x) -> ()
proxyFun3 = const ()

testProxy3 :: Proxy 8 -> ()
testProxy3 = proxyFun3

testProxy3Errors =
#if __GLASGOW_HASKELL__ >= 900
  ["Expected: Proxy 8 -> ()"
  ,"  Actual: Proxy ((x0 + x0) + x0) -> ()"
  ]
#else
  ["Expected type: Proxy 8 -> ()"
  ,"Actual type: Proxy ((x0 + x0) + x0) -> ()"
  ]
#endif

proxyFun4 :: Proxy ((2*y)+4) -> ()
proxyFun4 = const ()

testProxy4 :: Proxy 2 -> ()
testProxy4 = proxyFun4

testProxy4Errors =
#if __GLASGOW_HASKELL__ >= 900
  ["Expected: Proxy 2 -> ()"
  ,"  Actual: Proxy ((2 * y0) + 4) -> ()"
  ]
#else
  ["Expected type: Proxy 2 -> ()"
  ,"Actual type: Proxy ((2 * y0) + 4) -> ()"
  ]
#endif

testProxy5 :: Proxy 7 -> ()
testProxy5 = proxyFun4

testProxy5Errors =
#if __GLASGOW_HASKELL__ >= 900
  ["Expected: Proxy 7 -> ()"
  ,"  Actual: Proxy ((2 * y1) + 4) -> ()"
  ]
#else
  ["Expected type: Proxy 7 -> ()"
  ,"Actual type: Proxy ((2 * y1) + 4) -> ()"
  ]
#endif

proxyFun6 :: Proxy (2^k) -> Proxy (2^k)
proxyFun6 = const Proxy

testProxy6 :: Proxy 7
testProxy6 = proxyFun6 (Proxy :: Proxy 7)

testProxy6Errors =
#if __GLASGOW_HASKELL__ >= 902
  ["Expected: Proxy 7"
  ,"  Actual: Proxy (2 ^ k0)"
  ]
#elif __GLASGOW_HASKELL__ >= 900
  ["Expected: Proxy (2 ^ k0)"
  ,"  Actual: Proxy 7"
  ]
#else
  ["Expected type: Proxy (2 ^ k0)"
  ,"Actual type: Proxy 7"
  ]
#endif

proxyFun7 :: Proxy (2^k) -> Proxy k
proxyFun7 = const Proxy

testProxy8 :: Proxy x -> Proxy (y + x)
testProxy8 = id

testProxy8Errors =
#if __GLASGOW_HASKELL__ >= 900
  ["Expected: Proxy x -> Proxy (y + x)"
  ,"  Actual: Proxy x -> Proxy x"
  ]
#else
  ["Expected type: Proxy x -> Proxy (y + x)"
  ,"Actual type: Proxy x -> Proxy x"
  ]
#endif

#if __GLASGOW_HASKELL__ >= 904
proxyInEq :: ((a <= b) ~ (() :: Constraint)) => Proxy (a :: Nat) -> Proxy b -> ()
#else
proxyInEq :: (a <= b) => Proxy (a :: Nat) -> Proxy b -> ()
#endif
proxyInEq _ _ = ()

proxyInEq' :: ((a <=? b) ~ 'False) => Proxy (a :: Nat) -> Proxy b -> ()
proxyInEq' _ _ = ()

testProxy9 :: Proxy (a + 1) -> Proxy a -> ()
testProxy9 = proxyInEq

testProxy9Errors =
#if __GLASGOW_HASKELL__ >= 904
  ["Cannot satisfy: a + 1 <= a"]
#elif __GLASGOW_HASKELL__ >= 902
  [$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "Couldn't match type ‘Data.Type.Ord.OrdCond"
          else litE $ stringL "Couldn't match type `Data.Type.Ord.OrdCond"
    )
  ,$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "(CmpNat (a + 1) a) 'True 'True 'False’"
          else litE $ stringL "(CmpNat (a + 1) a) 'True 'True 'False'"
    )
  ,$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "with ‘'True’"
          else litE $ stringL "with 'True"
    )
  ]
#else
  [$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "Couldn't match type ‘(a + 1) <=? a’ with ‘'True’"
          else litE $ stringL "Couldn't match type `(a + 1) <=? a' with 'True"
    )]
#endif

testProxy10 :: Proxy (a :: Nat) -> Proxy (a + 2) -> ()
testProxy10 = proxyInEq'

testProxy10Errors =
#if __GLASGOW_HASKELL__ >= 912
  [$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "Couldn't match type ‘Data.Type.Ord.OrdCond"
          else litE $ stringL "Couldn't match type `Data.Type.Ord.OrdCond"
    )
  ,$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "(CmpNat a (a + 2)) True True False’"
          else litE $ stringL "(CmpNat a (a + 2)) True True False'"
    )
  ,$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "with ‘False"
          else litE $ stringL "with `False"
    )
  ]
#elif __GLASGOW_HASKELL__ >= 910
  [$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "Couldn't match type ‘Data.Type.Ord.OrdCond"
          else litE $ stringL "Couldn't match type `Data.Type.Ord.OrdCond"
    )
  ,$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "(CmpNat a (a + 2)) True True False’"
          else litE $ stringL "(CmpNat a (a + 2)) True True False'"
    )
  ,$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "with ‘False"
          else litE $ stringL "with `False"
    )
  ]
#elif __GLASGOW_HASKELL__ >= 906
  [$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "Couldn't match type ‘Data.Type.Ord.OrdCond"
          else litE $ stringL "Couldn't match type `Data.Type.Ord.OrdCond"
    )
  ,$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "(CmpNat a (a + 2)) True True False’"
          else litE $ stringL "(CmpNat a (a + 2)) True True False'"
    )
  ,$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "with ‘False"
          else litE $ stringL "with False"
    )
  ]
#elif __GLASGOW_HASKELL__ >= 902
  [$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "Couldn't match type ‘Data.Type.Ord.OrdCond"
          else litE $ stringL "Couldn't match type `Data.Type.Ord.OrdCond"
    )
  ,$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "(CmpNat a (a + 2)) 'True 'True 'False’"
          else litE $ stringL "(CmpNat a (a + 2)) 'True 'True 'False'"
    )
  ,$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "with ‘'False"
          else litE $ stringL "with 'False"
    )
  ]
#else
  [$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "Couldn't match type ‘a <=? (a + 2)’ with ‘'False’"
          else litE $ stringL "Couldn't match type `a <=? (a + 2)' with 'False"
    )]
#endif

testProxy11 :: Proxy (a :: Nat) -> Proxy a -> ()
testProxy11 = proxyInEq'

testProxy11Errors =
  [$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
#if __GLASGOW_HASKELL__ >= 910
          then litE $ stringL "Couldn't match type ‘True’ with ‘False’"
          else litE $ stringL "Couldn't match type `True' with `False'"
#elif __GLASGOW_HASKELL__ >= 906
          then litE $ stringL "Couldn't match type ‘True’ with ‘False’"
          else litE $ stringL "Couldn't match type True with False"
#else
          then litE $ stringL "Couldn't match type ‘'True’ with ‘'False’"
          else litE $ stringL "Couldn't match type 'True with 'False"
#endif
    )]

testProxy12 :: Proxy (a + b) -> Proxy (a + c) -> ()
testProxy12 = proxyInEq

testProxy12Errors =
#if __GLASGOW_HASKELL__ >= 904
  ["Cannot satisfy: a + b <= a + c"]
#elif __GLASGOW_HASKELL__ >= 902
  [$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "Couldn't match type ‘Data.Type.Ord.OrdCond"
          else litE $ stringL "Couldn't match type `Data.Type.Ord.OrdCond"
    )
  ,$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "(CmpNat (a + b) (a + c)) 'True 'True 'False’"
          else litE $ stringL "(CmpNat (a + b) (a + c)) 'True 'True 'False'"
    )
  ,$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "with ‘'True’"
          else litE $ stringL "with 'True"
    )
  ]
#else
  [$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "Couldn't match type ‘(a + b) <=? (a + c)’ with ‘'True’"
          else litE $ stringL "Couldn't match type `(a + b) <=? (a + c)' with 'True"
    )]
#endif

testProxy13 :: Proxy (4*a) -> Proxy (2*a) ->()
testProxy13 = proxyInEq

testProxy13Errors =
#if __GLASGOW_HASKELL__ >= 904
  ["Cannot satisfy: 4 * a <= 2 * a"]
#elif __GLASGOW_HASKELL__ >= 902
  [$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "Couldn't match type ‘Data.Type.Ord.OrdCond"
          else litE $ stringL "Couldn't match type `Data.Type.Ord.OrdCond"
    )
  ,$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "(CmpNat (4 * a) (2 * a)) 'True 'True 'False’"
          else litE $ stringL "(CmpNat (4 * a) (2 * a)) 'True 'True 'False'"
    )
  ,$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "with ‘'True’"
          else litE $ stringL "with 'True"
    )
  ]
#else
  [$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "Couldn't match type ‘(4 * a) <=? (2 * a)’ with ‘'True’"
          else litE $ stringL "Couldn't match type `(4 * a) <=? (2 * a)' with 'True"
    )]
#endif

testProxy14 :: Proxy (2*a) -> Proxy (4*a) -> ()
testProxy14 = proxyInEq'

testProxy14Errors =
#if __GLASGOW_HASKELL__ >= 912
  [$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "Couldn't match type ‘Data.Type.Ord.OrdCond"
          else litE $ stringL "Couldn't match type `Data.Type.Ord.OrdCond"
    )
  ,$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "(CmpNat (2 * a) (4 * a)) True True False’"
          else litE $ stringL "(CmpNat (2 * a) (4 * a)) True True False'"
    )
  ,$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "with ‘False"
          else litE $ stringL "with `False"
    )
  ]
#elif __GLASGOW_HASKELL__ >= 910
  [$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "Couldn't match type ‘Data.Type.Ord.OrdCond"
          else litE $ stringL "Couldn't match type `Data.Type.Ord.OrdCond"
    )
  ,$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "(CmpNat (2 * a) (4 * a)) True True False’"
          else litE $ stringL "(CmpNat (2 * a) (4 * a)) True True False'"
    )
  ,$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "with ‘False"
          else litE $ stringL "with `False"
    )
  ]
#elif __GLASGOW_HASKELL__ >= 906
  [$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "Couldn't match type ‘Data.Type.Ord.OrdCond"
          else litE $ stringL "Couldn't match type `Data.Type.Ord.OrdCond"
    )
  ,$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "(CmpNat (2 * a) (4 * a)) True True False’"
          else litE $ stringL "(CmpNat (2 * a) (4 * a)) True True False'"
    )
  ,$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "with ‘False"
          else litE $ stringL "with False"
    )
  ]
#elif __GLASGOW_HASKELL__ >= 902
  [$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "Couldn't match type ‘Data.Type.Ord.OrdCond"
          else litE $ stringL "Couldn't match type `Data.Type.Ord.OrdCond"
    )
  ,$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "(CmpNat (2 * a) (4 * a)) 'True 'True 'False’"
          else litE $ stringL "(CmpNat (2 * a) (4 * a)) 'True 'True 'False'"
    )
  ,$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "with ‘'False"
          else litE $ stringL "with 'False"
    )
  ]
#else
  [$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "Couldn't match type ‘(2 * a) <=? (4 * a)’ with ‘'False’"
          else litE $ stringL "Couldn't match type `(2 * a) <=? (4 * a)' with 'False"
    )]
#endif

type family CLog (b :: Nat) (x :: Nat) :: Nat
type instance CLog 2 2 = 1

testProxy15 :: (CLog 2 (2 ^ n) ~ n, (1 <=? n) ~ True) => Proxy n -> Proxy (n+d)
testProxy15 = id

testProxy15Errors =
#if __GLASGOW_HASKELL__ >= 900
  ["Expected: Proxy n -> Proxy (n + d)"
  ,"  Actual: Proxy n -> Proxy n"
  ]
#else
  ["Expected type: Proxy n -> Proxy (n + d)"
  ,"Actual type: Proxy n -> Proxy n"
  ]
#endif

data Fin (n :: Nat) where
  FZ :: Fin (n + 1)
  FS :: Fin n -> Fin (n + 1)

test16 :: forall n . Integer -> Fin n
test16 n = case n of
  0 -> FZ
  x -> FS (test16 @(n-1) (x-1))

test16Errors =
#if __GLASGOW_HASKELL__ >= 904
  ["Cannot satisfy: 1 <= n"]
#elif __GLASGOW_HASKELL__ >= 902
  [$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "Couldn't match type ‘Data.Type.Ord.OrdCond"
          else litE $ stringL "Couldn't match type `Data.Type.Ord.OrdCond"
    )
  ,$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "(CmpNat 1 n) 'True 'True 'False’"
          else litE $ stringL "(CmpNat 1 n) 'True 'True 'False'"
    )
  ,$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "with ‘'True’"
          else litE $ stringL "with 'True"
    )
  ]
#else
  [$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "Couldn't match type ‘1 <=? n’ with ‘'True’"
          else litE $ stringL "Couldn't match type `1 <=? n' with 'True"
    )]
#endif

data Dict c where
  Dict :: c => Dict c
deriving instance Show (Dict c)
data Boo (n :: Nat) = Boo

test17 :: Show (Boo n) => Proxy n -> Boo (n - 1 + 1) -> String
test17 = const show

testProxy17 :: String

testProxy17 = test17 (Proxy :: Proxy 17) Boo
test17Errors = test16Errors

#if __GLASGOW_HASKELL__ >= 904
test19f :: ((1 <= n) ~ (() :: Constraint))
#else
test19f :: (1 <= n)
#endif
  => Proxy n -> Proxy n
test19f = id

testProxy19 :: (1 <= m, m <= rp)
  => Proxy m
  -> Proxy rp
  -> Proxy (rp - m)
  -> Proxy (rp - m)
testProxy19 _ _ = test19f

test19Errors =
#if __GLASGOW_HASKELL__ >= 904
  [ "Cannot satisfy: 1 <= rp - m" ]
#elif __GLASGOW_HASKELL__ >= 902
  [ "Could not deduce: Data.Type.Ord.OrdCond"
  , "(CmpNat 1 (rp - m)) 'True 'True 'False"
  , "~ 'True"
  ]
#else
  ["Could not deduce: (1 <=? (rp - m)) ~ 'True"]
#endif

testProxy20 :: Proxy 1 -> Proxy (m ^ 2) -> ()
testProxy20 = proxyInEq

testProxy20Errors =
#if __GLASGOW_HASKELL__ >= 904
  ["Cannot satisfy: 1 <= m ^ 2"]
#elif __GLASGOW_HASKELL__ >= 902
  [$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "Couldn't match type ‘Data.Type.Ord.OrdCond"
          else litE $ stringL "Couldn't match type `Data.Type.Ord.OrdCond"
    )
  ,$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "(CmpNat 1 (m ^ 2)) 'True 'True 'False’"
          else litE $ stringL "(CmpNat 1 (m ^ 2)) 'True 'True 'False'"
    )
  ,$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "with ‘'True’"
          else litE $ stringL "with 'True"
    )
  ]
#else
  [$(do localeEncoding <- runIO (getLocaleEncoding)
        if textEncodingName localeEncoding == textEncodingName utf8
          then litE $ stringL "Couldn't match type ‘1 <=? (m ^ 2)’ with ‘'True’"
          else litE $ stringL "Couldn't match type `1 <=? (m ^ 2)' with 'True"
    )]
#endif
