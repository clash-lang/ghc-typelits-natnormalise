{-# LANGUAGE CPP #-}
{-# LANGUAGE QuasiQuotes #-}

module ShouldError (tests) where

import Data.String.Interpolate (i)
import ShouldError.Tasty (assertCompileError)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase)

tests :: TestTree
tests = testGroup "ShouldError"
    [ test1
    , test2
    , test3
    , test4
    , test5
    , test6
    , test7
    , test8
    , test9
    , test10
    , test11
    , testIssue126
    , inequalityTests
    , branchKnownNatTest
    ]

preamble :: String
preamble = [i|
import Data.Kind (Constraint)
import Data.Proxy
import GHC.TypeLits
|] <> "\n"

source1 :: String
source1 = preamble <> [i|
test :: Proxy (x + 1) -> Proxy (2 + x)
test = id
|]

expected1 :: [String]
expected1 =
#if __GLASGOW_HASKELL__ >= 914
  ["Expected: Proxy (2 + x)"
  ,"  Actual: Proxy (x + 1)"
  ]
#elif __GLASGOW_HASKELL__ >= 900
  ["Expected: Proxy (x + 1) -> Proxy (2 + x)"
  ,"  Actual: Proxy (x + 1) -> Proxy (x + 1)"
  ]
#else
  ["Expected type: Proxy (x + 1) -> Proxy (2 + x)"
  ,"Actual type: Proxy (2 + x) -> Proxy (2 + x)"
  ]
#endif

test1 :: TestTree
test1 = testCase "x + 1 /~ 2 + x" $ assertCompileError source1 expected1

source2 :: String
source2 = preamble <> [i|
type family GCD (x :: Nat) (y :: Nat) :: Nat
type instance GCD 6 8 = 2
type instance GCD 9 6 = 3

test :: Proxy (GCD 6 8 + x) -> Proxy (x + GCD 9 6)
test = id
|]

expected2 :: [String]
expected2 =
#if __GLASGOW_HASKELL__ >= 914
  ["Expected: Proxy (x + GCD 9 6)"
  ,"  Actual: Proxy (2 + x)"
  ]
#elif __GLASGOW_HASKELL__ >= 900
  ["Expected: Proxy (GCD 6 8 + x) -> Proxy (x + GCD 9 6)"
  ,"  Actual: Proxy (2 + x) -> Proxy (2 + x)"
  ]
#else
  ["Expected type: Proxy (GCD 6 8 + x) -> Proxy (x + GCD 9 6)"
  ,"Actual type: Proxy (x + 3) -> Proxy (x + 3)"
  ]
#endif

test2 :: TestTree
test2 = testCase "GCD 6 8 + x /~ x + GCD 9 6" $ assertCompileError source2 expected2

source3 :: String
source3 = preamble <> [i|
proxyFun :: Proxy (x + x + x) -> ()
proxyFun = const ()

test :: Proxy 8 -> ()
test = proxyFun
|]

expected3 :: [String]
expected3 =
#if __GLASGOW_HASKELL__ >= 914
  ["Expected: Proxy ((x0 + x0) + x0)"
  ,"  Actual: Proxy 8"
  ]
#elif __GLASGOW_HASKELL__ >= 900
  ["Expected: Proxy 8 -> ()"
  ,"  Actual: Proxy ((x0 + x0) + x0) -> ()"
  ]
#else
  ["Expected type: Proxy 8 -> ()"
  ,"Actual type: Proxy ((x0 + x0) + x0) -> ()"
  ]
#endif

test3 :: TestTree
test3 = testCase "Unify \"x + x + x\" with \"8\"" $ assertCompileError source3 expected3

source4 :: String
source4 = preamble <> [i|
proxyFun :: Proxy ((2*y)+4) -> ()
proxyFun = const ()

test :: Proxy 2 -> ()
test = proxyFun
|]

expected4 :: [String]
expected4 =
#if __GLASGOW_HASKELL__ >= 914
  ["Expected: Proxy ((2 * y0) + 4)"
  ,"  Actual: Proxy 2"
  ]
#elif __GLASGOW_HASKELL__ >= 900
  ["Expected: Proxy 2 -> ()"
  ,"  Actual: Proxy ((2 * y0) + 4) -> ()"
  ]
#else
  ["Expected type: Proxy 2 -> ()"
  ,"Actual type: Proxy ((2 * y0) + 4) -> ()"
  ]
#endif

test4 :: TestTree
test4 = testCase "Unify \"(2*x)+4\" with \"2\"" $ assertCompileError source4 expected4

source5 :: String
source5 = preamble <> [i|
proxyFun :: Proxy ((2*y)+4) -> ()
proxyFun = const ()

test :: Proxy 7 -> ()
test = proxyFun
|]

expected5 :: [String]
expected5 =
#if __GLASGOW_HASKELL__ >= 914
  ["Expected: Proxy ((2 * y"
  ,"Actual: Proxy 7"
  ]
#elif __GLASGOW_HASKELL__ >= 900
  ["Expected: Proxy 7 -> ()"
  ,"Actual: Proxy ((2 * y"
  ]
#else
  ["Expected type: Proxy 7 -> ()"
  ,"Actual type: Proxy ((2 * y"
  ]
#endif

test5 :: TestTree
test5 = testCase "Unify \"(2*x)+4\" with \"7\"" $ assertCompileError source5 expected5

source6 :: String
source6 = preamble <> [i|
proxyFun :: Proxy (2^k) -> Proxy (2^k)
proxyFun = const Proxy

test :: Proxy 7
test = proxyFun (Proxy :: Proxy 7)
|]

expected6 :: [String]
expected6 =
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

test6 :: TestTree
test6 = testCase "Unify \"2^k\" with \"7\"" $ assertCompileError source6 expected6

source7 :: String
source7 = preamble <> [i|
test :: Proxy x -> Proxy (y + x)
test = id
|]

expected7 :: [String]
expected7 =
#if __GLASGOW_HASKELL__ >= 914
  ["Expected: Proxy (y + x)"
  ,"  Actual: Proxy x"
  ]
#elif __GLASGOW_HASKELL__ >= 900
  ["Expected: Proxy x -> Proxy (y + x)"
  ,"  Actual: Proxy x -> Proxy x"
  ]
#else
  ["Expected type: Proxy x -> Proxy (y + x)"
  ,"Actual type: Proxy x -> Proxy x"
  ]
#endif

test7 :: TestTree
test7 = testCase "x /~ y + x" $ assertCompileError source7 expected7

source8 :: String
source8 = preamble <> [i|
type family CLog (b :: Nat) (x :: Nat) :: Nat
type instance CLog 2 2 = 1

test :: (CLog 2 (2 ^ n) ~ n, (1 <=? n) ~ True) => Proxy n -> Proxy (n+d)
test = id
|]

expected8 :: [String]
expected8 =
#if __GLASGOW_HASKELL__ >= 914
  ["Expected: Proxy (n + d)"
  ,"  Actual: Proxy n"
  ]
#elif __GLASGOW_HASKELL__ >= 900
  ["Expected: Proxy n -> Proxy (n + d)"
  ,"  Actual: Proxy n -> Proxy n"
  ]
#else
  ["Expected type: Proxy n -> Proxy (n + d)"
  ,"Actual type: Proxy n -> Proxy n"
  ]
#endif

test8 :: TestTree
test8 = testCase "(CLog 2 (2 ^ n) ~ n, (1 <=? n) ~ True) => n /~ n + d" $
  assertCompileError source8 expected8

source9 :: String
source9 = preamble <> [i|
data Fin (n :: Nat) where
  FZ :: Fin (n + 1)
  FS :: Fin n -> Fin (n + 1)

test :: forall n . Integer -> Fin n
test n = case n of
  0 -> FZ
  x -> FS (test @(n-1) (x-1))
|]

expected9 :: [String]
expected9 =
#if __GLASGOW_HASKELL__ >= 904
  ["Cannot satisfy: 1 <= n"]
#elif __GLASGOW_HASKELL__ >= 902
  [ "Couldn't match type Data.Type.Ord.OrdCond"
  , "(CmpNat 1 n) True True False"
  , "with True"
  ]
#else
  [ "Couldn't match type 1 <=? n with True" ]
#endif

test9 :: TestTree
test9 = testCase "(n - 1) + 1 ~ n implies (1 <= n)" $ assertCompileError source9 expected9

source10 :: String
source10 = preamble <> [i|
type family Drop (n :: Nat) (xs :: [Nat]) :: [Nat] where
  Drop 0 xs = xs
  Drop n (x ': xs) = Drop (n-1) xs
  Drop n '[] = '[]

test :: Proxy ns -> Proxy (Drop 1 ns) -> Proxy (Drop 2 ns)
test _ px = px
|]

expected10 :: [String]
expected10 =
#if __GLASGOW_HASKELL__ >= 811
  [ "Couldn't match type: Drop 1 ns"
  , "               with: Drop 2 ns"
  , "Expected: Proxy (Drop 2 ns)"
  , "  Actual: Proxy (Drop 1 ns)"
  , "Drop is a non-injective type family"
  ]
#else
  [ "Couldn't match type Drop 1 ns with Drop 2 ns"
  , "Expected type: Proxy (Drop 2 ns)"
  , "  Actual type: Proxy (Drop 1 ns)"
  , "Drop is a non-injective type family"
  ]
#endif

test10 :: TestTree
test10 = testCase "Do not unify in non-injective positions" $ assertCompileError source10 expected10

source11 :: String
source11 = preamble <> [i|
test :: Proxy a -> Proxy b -> Proxy ((2 * a) + b) -> Proxy 5
test _ _ = id
|]

expected11 :: [String]
expected11 =
#if __GLASGOW_HASKELL__ >= 914
  ["Expected: Proxy 5"
  ,"  Actual: Proxy ((2 * a) + b)"
  ]
#elif __GLASGOW_HASKELL__ >= 900
  ["Expected: Proxy ((2 * a) + b) -> Proxy 5"
  ,"  Actual: Proxy 5 -> Proxy 5"
  ]
#else
  ["Expected type: Proxy ((2 * a) + b) -> Proxy 5"
  ,"Actual type: Proxy 5 -> Proxy 5"
  ]
#endif

test11 :: TestTree
test11 = testCase "Do not rewrite constraint to itself" $ assertCompileError source11 expected11

-- ((3 * (n - 1)) + 1) simplifies to (3 * n - 2), so
-- the equality would require b0 ~ -2, which is impossible at kind Nat.
sourceIssue126 :: String
sourceIssue126 = preamble <> [i|
data Index (n :: Nat) = Index

truncateB :: Index (a + b) -> Index a
truncateB = undefined

mul :: Index 4 -> Index n -> Index ((3 * (n - 1)) + 1)
mul _ _ = Index

zeroExtendTimesThree :: (1 <= n) => Index n -> Index (n * 3)
zeroExtendTimesThree = truncateB . (mul Index)
|]

expectedIssue126 :: [String]
expectedIssue126 =
#if __GLASGOW_HASKELL__ >= 906
  [ "Could not deduce ((n * 3) + b0) ~ ((3 * (n - 1)) + 1)"
#elif __GLASGOW_HASKELL__ >= 904
  [ "Could not deduce (((n * 3) + b0) ~ ((3 * (n - 1)) + 1))"
#elif __GLASGOW_HASKELL__ >= 902
  [ "Could not deduce: ((n * 3) + b0) ~ ((3 * (n - 1)) + 1)"
#else
  [ "Could not deduce: ((3 * (n - 1)) + 1) ~ ((n * 3) + b0)"
#endif
  , "from the context: 1 <= n"
  ]



testIssue126 :: TestTree
testIssue126 =
  testCase "Issue 126 regression reproducer" $
    assertCompileError sourceIssue126 expectedIssue126

proxyInEqDef :: String
proxyInEqDef =
#if __GLASGOW_HASKELL__ >= 904
  [i|
proxyInEq :: ((a <= b) ~ (() :: Constraint)) => Proxy (a :: Nat) -> Proxy b -> ()
proxyInEq _ _ = ()
|]
#else
  [i|
proxyInEq :: (a <= b) => Proxy (a :: Nat) -> Proxy b -> ()
proxyInEq _ _ = ()
|]
#endif

proxyInEq'Def :: String
proxyInEq'Def = [i|
proxyInEq' :: ((a <=? b) ~ 'False) => Proxy (a :: Nat) -> Proxy b -> ()
proxyInEq' _ _ = ()
|]

source12 :: String
source12 = preamble <> proxyInEqDef <> proxyInEq'Def <> [i|
test :: Proxy (a + 1) -> Proxy a -> ()
test = proxyInEq
|]

expected12 :: [String]
expected12 =
#if __GLASGOW_HASKELL__ >= 904
  ["Cannot satisfy: a + 1 <= a"]
#elif __GLASGOW_HASKELL__ >= 902
  [ "Couldn't match type Data.Type.Ord.OrdCond"
  , "(CmpNat (a + 1) a) True True False"
  , "with True"
  ]
#else
  [ "Couldn't match type (a + 1) <=? a with True" ]
#endif

test12 :: TestTree
test12 = testCase "a+1 <= a" $ assertCompileError source12 expected12

source13 :: String
source13 = preamble <> proxyInEqDef <> proxyInEq'Def <> [i|
test :: Proxy (a :: Nat) -> Proxy (a + 2) -> ()
test = proxyInEq'
|]

expected13 :: [String]
expected13 =
#if __GLASGOW_HASKELL__ >= 902
  [ "Data.Type.Ord.OrdCond"
  , "(CmpNat a (a + 2)) True True False"
  , "with False"
  ]
#else
  [ "Couldn't match type a <=? (a + 2) with False" ]
#endif

test13 :: TestTree
test13 = testCase "(a <=? a+1) ~ False" $ assertCompileError source13 expected13

source14 :: String
source14 = preamble <> proxyInEqDef <> proxyInEq'Def <> [i|
test :: Proxy (a :: Nat) -> Proxy a -> ()
test = proxyInEq'
|]

expected14 :: [String]
expected14 = [ "Couldn't match type True with False" ]

test14 :: TestTree
test14 = testCase "(a <=? a) ~ False" $ assertCompileError source14 expected14

source15 :: String
source15 = preamble <> proxyInEqDef <> proxyInEq'Def <> [i|
test :: Proxy (a + b) -> Proxy (a + c) -> ()
test = proxyInEq
|]

expected15 :: [String]
expected15 =
#if __GLASGOW_HASKELL__ >= 904
  ["Cannot satisfy: a + b <= a + c"]
#elif __GLASGOW_HASKELL__ >= 902
  [ "Couldn't match type Data.Type.Ord.OrdCond"
  , "(CmpNat (a + b) (a + c)) True True False"
  , "with True"
  ]
#else
  [ "Couldn't match type (a + b) <=? (a + c) with True" ]
#endif

test15 :: TestTree
test15 = testCase "() => (a+b <= a+c)" $ assertCompileError source15 expected15

source16 :: String
source16 = preamble <> proxyInEqDef <> proxyInEq'Def <> [i|
test :: Proxy (4*a) -> Proxy (2*a) -> ()
test = proxyInEq
|]

expected16 :: [String]
expected16 =
#if __GLASGOW_HASKELL__ >= 904
  ["Cannot satisfy: 4 * a <= 2 * a"]
#elif __GLASGOW_HASKELL__ >= 902
  [ "Couldn't match type Data.Type.Ord.OrdCond"
  , "(CmpNat (4 * a) (2 * a)) True True False"
  , "with True"
  ]
#else
  [ "Couldn't match type (4 * a) <=? (2 * a) with True" ]
#endif

test16 :: TestTree
test16 = testCase "4a <= 2a" $ assertCompileError source16 expected16

source17 :: String
source17 = preamble <> proxyInEqDef <> proxyInEq'Def <> [i|
test :: Proxy (2*a) -> Proxy (4*a) -> ()
test = proxyInEq'
|]

expected17 :: [String]
expected17 =
#if __GLASGOW_HASKELL__ >= 902
  [ "Data.Type.Ord.OrdCond"
  , "(CmpNat (2 * a) (4 * a)) True True False"
  , "with False"
  ]
#else
  [ "Couldn't match type (2 * a) <=? (4 * a) with False" ]
#endif

test17 :: TestTree
test17 = testCase "2a <=? 4a ~ False" $ assertCompileError source17 expected17

source18 :: String
source18 = preamble <> [i|
data Boo (n :: Nat) = Boo

test :: Show (Boo n) => Proxy n -> Boo (n - 1 + 1) -> String
test = const show
|]

expected18 :: [String]
expected18 = expected9

test18 :: TestTree
test18 = testCase "Show (Boo n) => Show (Boo (n - 1 + 1))" $ assertCompileError source18 expected18

test19fDef :: String
test19fDef =
#if __GLASGOW_HASKELL__ >= 904
  [i|
test19f :: ((1 <= n) ~ (() :: Constraint)) => Proxy n -> Proxy n
test19f = id
|]
#else
  [i|
test19f :: (1 <= n) => Proxy n -> Proxy n
test19f = id
|]
#endif

source19 :: String
source19 = preamble <> test19fDef <> [i|
test :: (1 <= m, m <= rp) => Proxy m -> Proxy rp -> Proxy (rp - m) -> Proxy (rp - m)
test _ _ = test19f
|]

expected19 :: [String]
expected19 =
#if __GLASGOW_HASKELL__ >= 904
  [ "Cannot satisfy: 1 <= rp - m" ]
#elif __GLASGOW_HASKELL__ >= 902
  [ "Could not deduce: Data.Type.Ord.OrdCond"
  , "(CmpNat 1 (rp - m)) True True False"
  , "~ True"
  ]
#else
  [ "Could not deduce: (1 <=? (rp - m)) ~ True" ]
#endif

test19 :: TestTree
test19 = testCase "1 <= m, m <= rp implies 1 <= rp - m" $ assertCompileError source19 expected19

source20 :: String
source20 = preamble <> proxyInEqDef <> [i|
test :: Proxy 1 -> Proxy (m ^ 2) -> ()
test = proxyInEq
|]

expected20 :: [String]
expected20 =
#if __GLASGOW_HASKELL__ >= 904
  ["Cannot satisfy: 1 <= m ^ 2"]
#elif __GLASGOW_HASKELL__ >= 902
  [ "Couldn't match type Data.Type.Ord.OrdCond"
  , "(CmpNat 1 (m ^ 2)) True True False"
  , "with True"
  ]
#else
  [ "Couldn't match type 1 <=? (m ^ 2) with True" ]
#endif

test20 :: TestTree
test20 = testCase "Vacuously: 1 <= m ^ 2 ~ True" $ assertCompileError source20 expected20

inequalityTests :: TestTree
inequalityTests = testGroup "Inequality"
  [ test12
  , test13
  , test14
  , test15
  , test16
  , test17
  , test18
  , test19
  , test20
  ]

branchKnownNatSource :: String
branchKnownNatSource = preamble <> [i|
type family FBranch (n :: Nat) :: Nat

data KNBranch (n :: Nat) where
  KNGiven :: KnownNat (FBranch n) => KNBranch n
  KNPlain :: KNBranch n

needsFNonNeg :: (1 <= (1 + FBranch n)) => KNBranch n -> ()
needsFNonNeg _ = ()

test :: forall n. KNBranch n -> ()
test b = case b of
  KNGiven -> needsFNonNeg b
  KNPlain -> needsFNonNeg b
|]

branchKnownNatExpected :: [String]
branchKnownNatExpected =
  ["KnownNat (FBranch"]

branchKnownNatTest :: TestTree
branchKnownNatTest =
  testCase "GADT branches require fresh KnownNat evidence" $
    assertCompileError branchKnownNatSource branchKnownNatExpected
