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
import Hedgehog as X hiding (Gen, GenT, MonadGen, forAll, forAllWith)
import qualified Hedgehog
import Hedgehog.Arrow.Gen (ArrowGen, Gen (..))
import Hedgehog.Arrow.Prelude as X

-- | Generates a random input for the test by running the provided generator.
forAll :: (Monad m, Show a) => Gen b a -> b -> PropertyT m a
forAll m = Hedgehog.forAll <<< toGen m

-- | Generates a random input for the test by running the provided generator.
--
--   /This is a the same as 'forAll' but allows the user to provide a custom/
--   /rendering function. This is useful for values which don't have a/
--   /'Show' instance./
forAllWith :: Monad m => (a -> String) -> Gen b a -> b -> PropertyT m a
forAllWith f g = Hedgehog.forAllWith f . toGen g
