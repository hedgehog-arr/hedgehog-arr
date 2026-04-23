{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UnicodeSyntax #-}

module Hedgehog.Arrow (
  module X,
  ArrowGen,
  Gen,
  forAll,
  forAllWith,
) where

import Control.Arrow as X
import Hedgehog as X hiding (MonadGen, Gen, GenT, forAll, forAllWith)
import qualified Hedgehog
import Hedgehog.Arrow.Gen (Gen (..), ArrowGen)
import Hedgehog.Arrow.Prelude as X

forAll ∷ (Monad m, Show a) ⇒ Gen b a → b → PropertyT m a
forAll m = Hedgehog.forAll <<< toGen m

forAllWith ∷ Monad m ⇒ (a → String) → Gen b a → b → PropertyT m a
forAllWith f g = Hedgehog.forAllWith f . toGen g
