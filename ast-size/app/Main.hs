{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE UnicodeSyntax #-}

module Main where

import GHC (
  HsExpr (..), GhcPs, HsModule (..), LoadHowMuch (..),
  load, getModuleGraph, mgModSummaries, parseModule, parsedSource, unLoc,
  setTargets, guessTarget, getSessionDynFlags, setSessionDynFlags, runGhc)
import GHC.Paths (libdir)
import Control.Monad.IO.Class (liftIO)
import System.Environment (getArgs)
import Data.Generics (listify)

isExpr ∷ HsExpr GhcPs → Bool
isExpr (HsPar {}) = False
isExpr (HsApp {}) = False
isExpr _ = True

main ∷ IO ()
main = do
  args ← getArgs
  case args of
    [file] → runGhc (Just libdir) do
      dflags ← getSessionDynFlags
      setSessionDynFlags dflags
      target ← guessTarget file Nothing Nothing
      setTargets [target]
      _ ← load LoadAllTargets
      modGraph ← getModuleGraph
      case mgModSummaries modGraph of
          m:_ → do
              p ← parseModule m
              liftIO (putStrLn ("AST node count: " ++ show (length (listify isExpr (hsmodDecls (unLoc (parsedSource p)))))))
          _ → liftIO (putStrLn "No modules found.")
    _ → putStrLn "Usage: ast-size <filename>"
