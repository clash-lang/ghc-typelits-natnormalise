{-# LANGUAGE CPP #-}

module ShouldError.Tasty where

import Data.List (isInfixOf)
import Data.Maybe (fromMaybe)
import System.Environment (lookupEnv)
import System.Exit
import System.IO
import System.IO.Temp
import System.Process
import System.Timeout (timeout)
import Test.Tasty.HUnit

-- | Compile a Haskell code snippet with the plugin enabled, with an optional
-- timeout in seconds. Returns 'Nothing' if the timeout expired, otherwise the
-- exit code and stderr output of GHC.
runGhc :: Maybe Int -> String -> IO (Maybe (ExitCode, String))
runGhc timeLimit source = do
  -- XXX: This will pick the wrong GHC if the HC environment variable (as seen on CI)
  --      isn't set and the test suite is compiled with a GHC compiler other than the
  --      system's default.
  hc <- fromMaybe "ghc" <$> lookupEnv "HC"
  withSystemTempFile "ShouldError.hs" $ \tempFile tempHandle -> do
    hPutStr tempHandle source
    hClose tempHandle
    let compile = readProcessWithExitCode hc
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
    result <- case timeLimit of
      Nothing -> Just <$> compile
      -- 'timeout' interrupts 'readProcessWithExitCode' with an asynchronous
      -- exception, upon which it kills the GHC process before returning.
      Just seconds -> timeout (seconds * 1000000) compile
    return (fmap (\(exitCode, _, stderrOutput) -> (exitCode, stderrOutput)) result)

-- | Assert that a Haskell code snippet compiles successfully within the given
-- number of seconds
assertCompileSuccessWithin :: Int -> String -> Assertion
assertCompileSuccessWithin seconds source = do
  result <- runGhc (Just seconds) source
  case result of
    Nothing -> assertFailure $
      "Compilation did not finish within " ++ show seconds ++ " seconds"
    Just (ExitFailure _, stderrOutput) -> assertFailure $
      "Expected compilation to succeed but it failed:\n" ++ stderrOutput
    Just (ExitSuccess, _) -> return ()

-- | Assert that a Haskell code snippet fails to compile with expected error messages
assertCompileError :: String -> [String] -> Assertion
assertCompileError source expectedErrors = do
  Just (exitCode, stderrOutput) <- runGhc Nothing source
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
