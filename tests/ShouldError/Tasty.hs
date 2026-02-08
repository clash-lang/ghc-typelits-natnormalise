{-# LANGUAGE CPP #-}

module ShouldError.Tasty where

import Data.List (isInfixOf)
import Data.Maybe (fromMaybe)
import System.Environment (lookupEnv)
import System.Exit
import System.IO
import System.IO.Temp
import System.Process
import Test.Tasty.HUnit

-- | Assert that a Haskell code snippet fails to compile with expected error messages
assertCompileError :: String -> [String] -> Assertion
assertCompileError source expectedErrors = do
  -- XXX: This will pick the wrong GHC if the HC environment variable (as seen on CI)
  --      isn't set and the test suite is compiled with a GHC compiler other than the
  --      system's default.
  hc <- fromMaybe "ghc" <$> lookupEnv "HC"
  withSystemTempFile "ShouldError.hs" $ \tempFile tempHandle -> do
    hPutStr tempHandle source
    hClose tempHandle
    (exitCode, _, stderrOutput) <- readProcessWithExitCode hc
      [ "-XCPP"
      , "-XAllowAmbiguousTypes"
      , "-XConstraintKinds"
      , "-XDataKinds"
      , "-XFlexibleContexts"
      , "-XGADTs"
      , "-XScopedTypeVariables"
      , "-XStandaloneDeriving"
      , "-XTypeApplications"
      , "-XTypeFamilies"
      , "-XTypeOperators"
      , "-XUndecidableInstances"
      , "-XNoStarIsType"
      , "-fno-code"
      , "-fplugin", "GHC.TypeLits.Normalise"
      , tempFile
      ] ""
    case exitCode of
      ExitSuccess -> assertFailure "Expected compilation to fail but it succeeded"
      ExitFailure _ ->
        let cleanedStderr = removeProblemChars stderrOutput
            cleanedExpected = map removeProblemChars expectedErrors
        in if all (`isInfixOf` cleanedStderr) cleanedExpected
           then return ()
           else assertFailure $ "Error message mismatch:\n" ++
                               "Expected substrings: " ++ show expectedErrors ++ "\n" ++
                               "Actual output:\n" ++ stderrOutput

-- | Remove problematic characters that vary depending on locale
-- The kind and amount of quotes in GHC error messages changes depending on
-- whether or not our locale supports unicode.
removeProblemChars :: String -> String
removeProblemChars = filter (`notElem` problemChars)
  where problemChars = "‘’`'"
