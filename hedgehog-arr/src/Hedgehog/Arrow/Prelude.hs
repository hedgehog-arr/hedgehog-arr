{-# LANGUAGE Arrows #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE UnicodeSyntax #-}

module Hedgehog.Arrow.Prelude where

import Control.Arrow (Arrow (..), ArrowChoice, ArrowZero (..), returnA)
import Data.Foldable (Foldable (toList))
import Data.Traversable (mapAccumL)

guard ∷ (ArrowChoice f, ArrowZero f) ⇒ f Bool ()
guard = proc b → if b then returnA ⤙ () else zeroArrow ⤙ ()

traverseA ∷ (ArrowChoice g, Traversable f) ⇒ g (a, b) c → g (f a, b) (f c)
traverseA m = proc ~(xs, b) → do
  ys ← traverseA' m ⤙ (toList xs, b)
  returnA ⤙ assign ys xs

traverseA' ∷ ArrowChoice f ⇒ f (a, b) c → f ([a], b) [c]
traverseA' m = proc ~(xs, b) → do
  case xs of
    [] → returnA ⤙ []
    x : xs' → do
      y ← m ⤙ (x, b)
      ys ← traverseA' m ⤙ (xs', b)
      returnA ⤙ y : ys

assign ∷ Traversable f ⇒ [b] → f a → f b
assign xs ys = snd (mapAccumL (\zs _ → go zs) xs ys)
 where
  go (z : zs) = (zs, z)
  go [] = error "IMPOSSIBLE"

replicateA ∷ ArrowChoice f ⇒ f a b → f (Int, a) [b]
replicateA g = proc (n, x) → do
  if n == 0
    then
      returnA ⤙ []
    else do
      y ← g ⤙ x
      ys ← replicateA g ⤙ (n - 1, x)
      returnA ⤙ (y : ys)

filterA ∷ ArrowChoice f ⇒ f a Bool → f [a] [a]
filterA h = proc xs → do
  case xs of
    [] → returnA ⤙ []
    y : ys → do
      b ← h ⤙ y
      zs ← filterA h ⤙ ys
      returnA ⤙ if b then y : zs else zs

($$) ∷ Arrow f ⇒ f a b → a → f c b
($$) m x = proc _ → m ⤙ x

($<) ∷ Arrow f ⇒ f (a, b) c → a → f b c
($<) m x = proc y → m ⤙ (x, y)

newtype Ap f a b = Ap {getAp ∷ f a b}

instance Arrow f ⇒ Functor (Ap f a) where
  fmap f (Ap x) = Ap proc y → do
    z ← x ⤙ y
    returnA ⤙ f z

instance Arrow f ⇒ Applicative (Ap f a) where
  pure x = Ap (returnA $$ x)
  Ap f <*> Ap x = Ap proc y → do
    g ← f ⤙ y
    z ← x ⤙ y
    returnA ⤙ g z
