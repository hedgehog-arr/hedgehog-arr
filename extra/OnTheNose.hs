{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UnicodeSyntax #-}

-- Execution Instructions:
-- > cabal repl --build-depends=containers,random,transformers
-- ghci> :l OnTheNose.hs
-- ghci> :main

module OnTheNose where

import Control.Monad (ap, liftM)
import Control.Monad.Trans.Class (MonadTrans (..))
import Control.Monad.Trans.State (StateT (..), evalStateT, gets, put)
import Data.Foldable (toList)
import Data.Set (Set, fromList)
import Data.Tree (Tree (..), drawTree)
import System.Random (StdGen, initStdGen, uniform)

-- | This is a generator monad (with integrated shrinking) that satisfies the
-- monad laws "on the nose" by using the StateT monad to manage the random seed.
newtype Gen a = Gen (StateT StdGen Tree a)
 deriving (Functor, Applicative, Monad)

-- | Samples a random tree from a generator.
run ∷ Gen a → IO (Tree a)
run (Gen m) = evalStateT m <$> initStdGen

-- | The coin generator returns a random boolean and does not shrink.
coin ∷ Gen Bool
coin = Gen do
  (b, σ) ← gets uniform
  put σ
  pure b

-- | `shrink x xs` always generates `x`, but shrinks to any of `xs`. See also
-- https://hackage.haskell.org/package/falsify-0.2.0/docs/Test-Falsify-Generator.html#v:shrinkToOneOf
shrink ∷ a → [a] → Gen a
shrink x = Gen . lift . Node x . map (`Node` [])

-- | A somewhat contrived boolean generator that shrinks to False. This example
-- works with any generator that performs a number of coin flips dependent on
-- the amount of shrinking being done.
blackBox ∷ Gen Bool
blackBox = do
  x ← shrink True [False]
  if x then coin else pure False

main ∷ IO ()
main = do
  -- Expectation: since we discard the result of blackBox, the result of coin
  -- should never change during shrinking (since coin has no shrinking
  -- behaviour). Hence, every label in t should be the same.
  --
  -- Reality: blackBox's behaviour affects coin's output. Some labels in t can
  -- be different.
  t ← run (blackBox >> coin)
  if length (fromList (toList t)) == 1
    then main
    else do
      putStrLn "Detected change during shrinking:\n"
      let indent '\n' = "\n  "
          indent c = [c]
      putStrLn ("  " ++ concatMap indent (drawTree (fmap show t)))
