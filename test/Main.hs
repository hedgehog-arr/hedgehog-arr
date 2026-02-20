{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE UnicodeSyntax #-}

{- HLINT ignore "Use camelCase" -}

module Main where

import System.IO (BufferMode (..), hSetBuffering, stderr, stdout)
import qualified Test.Example.Basic
import qualified Test.Example.Confidence
import qualified Test.Example.Coverage
import qualified Test.Example.Exception
import qualified Test.Example.QuasiShow
import qualified Test.Example.Resource
import qualified Test.Example.Roundtrip
import qualified Test.Example.STLC
import Prelude hiding (filter, id, (.))

main ∷ IO ()
main = do
  hSetBuffering stdout LineBuffering
  hSetBuffering stderr LineBuffering

  sequence_
    [ Test.Example.Basic.tests
    , Test.Example.Confidence.tests
    , Test.Example.Coverage.tests
    , Test.Example.Exception.tests
    , Test.Example.QuasiShow.tests
    , Test.Example.Resource.tests
    , Test.Example.Roundtrip.tests
    , Test.Example.STLC.tests
    ]
