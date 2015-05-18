{-# LANGUAGE DataKinds, TypeOperators #-}

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
