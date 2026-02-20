{-# LANGUAGE Arrows #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ViewPatterns #-}

module Hedgehog.Arrow.Gen (
  Gen (..),
  ArrowGen (..),
  prune,
  shrink,
  sized,
  scale,
  small,
  integral_,
  int,
  int8,
  int16,
  int32,
  int64,
  word,
  word8,
  word16,
  word32,
  word64,
  float,
  double,
  enum,
  enumBounded,
  bool,
  bool_,
  binit,
  octit,
  digit,
  hexit,
  element,
  lower,
  upper,
  alpha,
  alphaNum,
  ascii,
  latin1,
  choice,
  frequency,
  unicode,
  unicodeAll,
  list,
  text,
  string,
  uft8,
  bytes,
  constant,
  element_,
  recursive,
  ensure,
  filter,
  just,
  maybe,
  either,
  nonEmpty,
  unfreeze,
  seq,
  uniqueByKey,
  map,
  set,
  subsequence,
  subset,
  shuffleSeq,
  shuffle,
  subtermA,
  subterm,
  subtermA2,
  subterm2,
  subtermA3,
  subterm3,
) where

import Control.Applicative (Alternative (..))
import Control.Arrow (Arrow (..), ArrowChoice (..), ArrowPlus (..), ArrowZero (..), returnA)
import Control.Arrow.Operations (ArrowReader (readState))
import Control.Arrow.Transformer.Reader (ReaderArrow (..))
import Control.Category (Category (..))
import Control.Monad ((<=<))
import Control.Monad.Trans.Maybe (MaybeT (..))
import Data.ByteString (ByteString)
import qualified Data.ByteString as ByteString
import qualified Data.Char as Char
import Data.Foldable (Foldable (..))
import Data.Functor.Identity (Identity (..))
import Data.Int (Int16, Int32, Int64, Int8)
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NonEmpty
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromJust, isJust)
import qualified Data.Maybe as Maybe
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import Data.Word (Word16, Word32, Word64, Word8)
import Hedgehog (Range, Size)
import qualified Hedgehog as HH
import Hedgehog.Arrow.Prelude
import qualified Hedgehog.Gen as HH.Gen
import Hedgehog.Internal.Gen (Vec (..), atLeast, golden, mapGenT)
import qualified Hedgehog.Internal.Gen as HH
import qualified Hedgehog.Internal.Shrink as Shrink
import Hedgehog.Internal.Tree (NodeT (NodeT), Tree, TreeT (..), runTree, treeChildren, treeValue, pattern Node, pattern Tree)
import qualified Hedgehog.Internal.Tree as Tree
import qualified Hedgehog.Range as Range
import Prelude hiding (either, filter, id, map, maybe, seq, (.))
import qualified Prelude
import Control.Arrow.Transformer (ArrowTransformer(..))

class (ArrowChoice f, ArrowPlus f, ArrowZero f) ⇒ ArrowGen f where
  integral ∷ Integral a ⇒ f (Range a) a
  realFloat ∷ RealFloat a ⇒ f (Range a) a
  realFrac ∷ RealFrac a ⇒ f (Range a) a
  resize ∷ f a b → f (Size, a) b
  getSize ∷ f a Size
  shrinkTo ∷ f (NonEmpty a) a
  freeze ∷ f a b → f a (Tree b)

instance ArrowGen f ⇒ ArrowGen (ReaderArrow a f) where
  integral = lift integral
  realFloat = lift realFloat
  realFrac = lift realFrac
  resize (ReaderArrow m) = ReaderArrow (resize m . arr \((x, y), z) -> (x, (y, z)))
  getSize = lift getSize
  shrinkTo = lift shrinkTo
  freeze (ReaderArrow m) = ReaderArrow (freeze m)

newtype Gen a b = Gen {toGen ∷ a → HH.Gen b}

-- Distributions:
-- ⦇-⦈ : Gen a b → Dist (a → Tree b)
-- ⦇id⦈ = pure pure
-- ⦇f . g⦈ = do f' ← ⦇f⦈; g' ← ⦇g⦈; pure (f' <=< g')
-- ⦇arr f⦈ = pure (pure . f)
-- ⦇first f⦈ = (\f' (x, y) → (,y) <$> f' y) <$> ⦇f⦈
-- ⦇left f⦈ = (\f' → either (fmap Left . f') (pure . Right)) <$> ⦇f⦈
-- ⦇zeroArrow⦈ = 0
-- ⦇f <+> g⦈ = ⦇f⦈ + |⦇f⦈|⁻¹ ∙ ⦇g⦈
-- ⦇shrinkTo (x :| xs)⦈ = pure \x → Node x (map pure xs)
-- ⦇integral [m..n)⦈ = sum [ (n - m)⁻¹ ∙ pure i | i ← [m..n) ]
-- ⦇realFrac [m, n]⦈ = (\i → m + (n - m) * i) <$> λ
-- ⦇freeze f⦈ = (\f x → pure (f x)) <$> ⦇f⦈

-- Not (quite) expressible generators:
-- > choice
-- > frequency

-- Relies on non-expressible generators:
-- > bytes
-- > either
-- > unicode
-- > maybe

instance Category Gen where
  id = Gen pure
  Gen f . Gen g = Gen (f <=< g)

instance Arrow Gen where
  arr f = Gen (pure . f)
  first (Gen f) = Gen \x → fmap (,snd x) (f (fst x))

instance ArrowChoice Gen where
  left (Gen f) = Gen (Prelude.either (fmap Left . f) (pure . Right))

instance ArrowZero Gen where
  zeroArrow = Gen (const HH.Gen.discard)

instance ArrowPlus Gen where
  Gen f <+> Gen g = Gen \x → f x <|> g x

instance ArrowGen Gen where
  integral = Gen HH.Gen.integral
  realFloat = Gen HH.Gen.realFloat
  realFrac = Gen HH.Gen.realFrac_
  shrinkTo = Gen \ ~(x :| xs) → HH.fromTree (Tree (Node x (fmap pure xs)))
  resize (Gen f) = Gen \ ~(n, x) → HH.Gen.resize n (f x)
  getSize = Gen \_ → HH.Gen.sized pure
  freeze (Gen f) = Gen (mapGenT (TreeT . fmap pure . MaybeT . Identity . go) . f)
   where
    go (TreeT (MaybeT (Identity Nothing))) = Nothing
    go (TreeT (MaybeT (Identity (Just (NodeT x xs))))) = Just (Tree (Node x (Maybe.mapMaybe go xs)))

instance Functor (Gen a) where
  fmap f x = arr f . x

instance Applicative (Gen a) where
  pure x = arr (const x)
  f <*> x = proc y → do
    g ← f ⤙ y
    z ← x ⤙ y
    returnA ⤙ g z

instance Alternative (Gen a) where
  empty = zeroArrow
  (<|>) = (<+>)

shrink ∷ ArrowGen f ⇒ f a b → f (b → [b], a) b
shrink m = proc ~(f, x) → do
  y ← m ⤙ x
  go ⤙ (f, y)
 where
  go = proc ~(f, x) → do
    y ← shrinkTo ⤙ (Right x :| fmap Left (f x))
    case y of
      Right z → returnA ⤙ z
      Left z → go ⤙ (f, z)

prune ∷ ArrowGen f ⇒ f a b → f a b
prune m = arr treeValue . freeze m

sized ∷ ArrowGen f ⇒ f (Size, a) b → f a b
sized m = proc x → do
  n ← getSize ⤙ ()
  m ⤙ (n, x)

scale ∷ ArrowGen f ⇒ f a b → f (Size → Size, a) b
scale m = proc ~(f, x) → do
  n ← getSize ⤙ ()
  resize m ⤙ (f n, x)

small ∷ ArrowGen f ⇒ f a b → f a b
small m = proc x → do
  scale m ⤙ (golden, x)

integral_ ∷ ArrowGen f ⇒ Integral a ⇒ f (Range a) a
integral_ = prune integral

int ∷ ArrowGen f ⇒ f (Range Int) Int
int = integral

int8 ∷ ArrowGen f ⇒ f (Range Int8) Int8
int8 = integral

int16 ∷ ArrowGen f ⇒ f (Range Int16) Int16
int16 = integral

int32 ∷ ArrowGen f ⇒ f (Range Int32) Int32
int32 = integral

int64 ∷ ArrowGen f ⇒ f (Range Int64) Int64
int64 = integral

word ∷ ArrowGen f ⇒ f (Range Word) Word
word = integral

word8 ∷ ArrowGen f ⇒ f (Range Word8) Word8
word8 = integral

word16 ∷ ArrowGen f ⇒ f (Range Word16) Word16
word16 = integral

word32 ∷ ArrowGen f ⇒ f (Range Word32) Word32
word32 = integral

word64 ∷ ArrowGen f ⇒ f (Range Word64) Word64
word64 = integral

float ∷ ArrowGen f ⇒ f (Range Float) Float
float = realFloat

double ∷ ArrowGen f ⇒ f (Range Double) Double
double = realFloat

enum ∷ (ArrowGen f, Enum a) ⇒ f (a, a) a
enum = proc ~(lo, hi) → do
  x ← integral ⤙ Range.constant (fromEnum lo) (fromEnum hi)
  returnA ⤙ toEnum x

enumBounded ∷ (ArrowGen f, Bounded a, Enum a) ⇒ f b a
enumBounded = proc _ → enum ⤙ (minBound, maxBound)

bool ∷ ArrowGen f ⇒ f a Bool
bool = enumBounded

bool_ ∷ ArrowGen f ⇒ f a Bool
bool_ = prune bool

binit ∷ ArrowGen f ⇒ f a Char
binit = proc _ → enum ⤙ ('0', '1')

octit ∷ ArrowGen f ⇒ f a Char
octit = proc _ → enum ⤙ ('0', '7')

digit ∷ ArrowGen f ⇒ f a Char
digit = proc _ → enum ⤙ ('0', '9')

hexit ∷ ArrowGen f ⇒ f a Char
hexit = proc _ → element ⤙ "0123456789aAbBcCdDeEfF"

lower ∷ ArrowGen f ⇒ f a Char
lower = proc _ → enum ⤙ ('a', 'z')

upper ∷ ArrowGen f ⇒ f a Char
upper = proc _ → enum ⤙ ('A', 'Z')

alpha ∷ ArrowGen f ⇒ f a Char
alpha = proc _ → element ⤙ "abcdefghiklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"

alphaNum ∷ ArrowGen f ⇒ f a Char
alphaNum = proc _ → element ⤙ "abcdefghiklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"

ascii ∷ ArrowGen f ⇒ f a Char
ascii = proc _ → enum ⤙ ('\0', '\127')

latin1 ∷ ArrowGen f ⇒ f a Char
latin1 = proc _ → enum ⤙ ('\0', '\255')

unicode ∷ ArrowGen f ⇒ f a Char
unicode = proc a → frequency [s1, s2, s3] ⤙ ([55296, 8190, 1048576], a)
 where
  s1 = proc _ → enum ⤙ ('\0', '\55295')
  s2 = proc _ → enum ⤙ ('\57344', '\65533')
  s3 = proc _ → enum ⤙ ('\65536', '\1114111')

unicodeAll ∷ ArrowGen f ⇒ f a Char
unicodeAll = enumBounded

string ∷ ArrowGen f ⇒ f a Char → f (Range Int, a) String
string = list

text ∷ ArrowGen f ⇒ f a Char → f (Range Int, a) Text
text m = arr Text.pack . string m

uft8 ∷ ArrowGen f ⇒ f a Char → f (Range Int, a) ByteString
uft8 m = arr Text.encodeUtf8 . text m

bytes ∷ ArrowGen f ⇒ f (Range Int) ByteString
bytes =
  arr ByteString.pack
    . choice
      [ proc r →
          list word8
            ⤙
              (,) r $
                Range.constant
                  (fromIntegral (Char.ord 'a'))
                  (fromIntegral (Char.ord 'z'))
      , proc r → list word8 ⤙ (r, Range.constant minBound maxBound)
      ]

constant ∷ ArrowGen f ⇒ f a a
constant = id

element ∷ (ArrowGen f, Foldable g) ⇒ f (g a) a
element = proc xs → do
  case toList xs of
    [] → returnA ⤙ error "Hedgehog.Arrow.element: used with empty Foldable"
    ys → do
      n ← integral ⤙ Range.constant 0 (length ys - 1)
      returnA ⤙ ys !! n

element_ ∷ (ArrowGen f, Foldable g) ⇒ f (g a) a
element_ = proc xs → do
  case toList xs of
    [] → returnA ⤙ error "Hedgehog.Arrow.element_: used with empty Foldable"
    ys → do
      n ← integral_ ⤙ Range.constant 0 (length ys - 1)
      returnA ⤙ ys !! n

-- NOTE: not faithful to original
choice ∷ ArrowGen f ⇒ [f a b] → f a b
choice [] = error "Hedgehog.Arrow.choice: used with empty list"
choice ms = proc x → do
  n ← integral ⤙ Range.constant 0 (length ms - 1)
  index ms ⤙ (n, x)

index ∷ ArrowChoice f ⇒ [f b c] → f (Int, b) c
index [] = proc ~(n, _) → do
  returnA ⤙ error ("IMPOSSIBLE: tried to get the " ++ show n ++ "th element of []")
index (m : ms) = proc ~(n, x) → do
  if n <= 0
    then
      m ⤙ x
    else
      index ms ⤙ (n - 1, x)

-- NOTE: not faithful to original
frequency ∷ ArrowGen f ⇒ [f a b] → f ([Int], a) b
frequency [] = proc _ → returnA ⤙ error "Hedgehog.Arrow.frequency: used with empty list"
frequency xs0 = proc (ks, a) → do
  let iis = scanl1 (+) ks
      total = sum ks
  n ← shrink integral_ ⤙ (\n → takeWhile (< n) iis, Range.constant 1 total)
  pick xs0 ⤙ (ks, n, a)
 where
  pick [] = proc _ → returnA ⤙ error "Hedgehog.Arrow.frequency/pick: used with empty list"
  pick (x : xs) = proc ~(ks, n, a) → do
    case ks of
      [] → returnA ⤙ error "Hedgehog.Arrow.frequency/pick: not enough weights"
      k : ks' → do
        if n <= k
          then x ⤙ a
          else pick xs ⤙ (ks', n - k, a)

recursive ∷ ArrowGen f ⇒ ([f a b] → f a b) → [f a b] → [f a b] → f a b
recursive f nr r = sized proc (n, x) → do
  if n <= 1
    then f nr ⤙ x
    else f (nr ++ fmap small r) ⤙ x

ensure ∷ ArrowGen f ⇒ f a b → f (b → Bool, a) b
ensure gen = proc (p, a) → do
  x ← gen ⤙ a
  if p x
    then returnA ⤙ x
    else zeroArrow ⤙ ()

fromPred ∷ (a → Bool) → a → Maybe a
fromPred p a
  | p a = Just a
  | otherwise = Nothing

filter ∷ ArrowGen f ⇒ f a b → f (b → Bool, a) b
filter m = mapMaybe m . arr (first fromPred)

-- NOTE: we have not implemented non-Identity effects, so this is redundant
-- filterT ∷ f a b → f (b → Bool, a) b

mapMaybe ∷ ArrowGen f ⇒ f a b → f (b → Maybe c, a) c
mapMaybe m = try 0
 where
  try k = proc ~(p, x) → do
    if k > 100
      then zeroArrow ⤙ ()
      else do
        ~gen@(treeValue → y) ← freeze (scale m) ⤙ ((2 * k +), x)
        case p y of
          Nothing → try (k + 1) ⤙ (p, x)
          Just _ → do
            z ← unfreeze ⤙ gen
            case p z of
              Just w → returnA ⤙ w
              Nothing → zeroArrow ⤙ ()

-- NOTE: we have not implemented non-Identity effects, so this is redundant
-- mapMaybeT ∷ f a b → f (b → Maybe c, a) c

just ∷ ArrowGen f ⇒ f a (Maybe b) → f a b
just m = proc x → do
  mx ← filter m ⤙ (isJust, x)
  returnA ⤙ fromJust mx

-- just ∷ ArrowGen f ⇒ f a (Maybe b) → f a b
-- just m = proc x → do
--   mx ← ⦇ filter (m ⤙ x) ⦈ isJust
--   returnA ⤙ fromJust mx

-- NOTE: we have not implemented non-Identity effects, so this is redundant
-- justT ∷ f a (Maybe b) → f a b

maybe ∷ ArrowGen f ⇒ f a b → f a (Maybe b)
maybe m = sized proc (n, x) →
  frequency [arr (const Nothing), arr Just . m] ⤙ ([2, 1 + fromIntegral n], x)

either ∷ ArrowGen f ⇒ f a b → f a c → f a (Either b c)
either m₁ m₂ = choice [arr Left . m₁, arr Right . m₂]

list ∷ ArrowGen f ⇒ f a b → f (Range Int, a) [b]
list gen = sized proc ~(size, (range, x)) → do
  n ← integral_ ⤙ range
  xs ← replicateA (freeze gen) ⤙ (n, x)
  ys ← unfreeze ⤙ (Tree (Tree.interleave (fmap runTree xs)))
  if atLeast (Range.lowerBound size range) ys
    then returnA ⤙ ys
    else zeroArrow ⤙ ()

seq ∷ ArrowGen f ⇒ f a b → f (Range Int, a) (Seq b)
seq gen = arr Seq.fromList . list gen

set ∷ (ArrowGen f, Ord k) ⇒ f a k → f (Range Int, a) (Set k)
set gen = proc ~(range, x) → do
  xs ← map (arr (,()) . gen) ⤙ (range, x)
  returnA ⤙ Map.keysSet xs

map ∷ (ArrowGen f, Ord k) ⇒ f a (k, v) → f (Range Int, a) (Map k v)
map gen = sized proc ~(size, ~(range, x)) → do
  xs ← shrink (uniqueByKey gen . first integral_) ⤙ (Shrink.list, (range, x))
  ys ← traverseA (unfreeze . arr fst) ⤙ (xs, ())
  let zs = Map.fromList ys
  guard ⤙ Map.size zs >= Range.lowerBound size range
  returnA ⤙ Map.fromList ys

uniqueByKey ∷ (ArrowGen f, Ord k) ⇒ f a (k, v) → f (Int, a) [Tree (k, v)]
uniqueByKey gen = proc (n, x) → try (0 ∷ Int) ⤙ (n, x, Map.empty)
 where
  try k
    | k > 100 = zeroArrow
    | otherwise = proc (n, x, xs0) → do
        kvs ← replicateA (freeze gen) ⤙ (n, x)
        case uniqueInsert n xs0 (fmap (\t → (fst (treeValue t), t)) kvs) of
          Left xs → returnA ⤙ Map.elems xs
          Right xs → try (k + 1) ⤙ (n, x, xs)

uniqueInsert ∷ Ord k ⇒ Int → Map k v → [(k, v)] → Either (Map k v) (Map k v)
uniqueInsert n xs kvs0 =
  if Map.size xs >= n
    then Left xs
    else case kvs0 of
      [] → Right xs
      (k, v) : kvs → uniqueInsert n (Map.insertWith const k v xs) kvs

nonEmpty ∷ ArrowGen f ⇒ f a b → f (Range Int, a) (NonEmpty b)
nonEmpty gen = proc ~(range, x) → do
  xs ← list gen ⤙ (fmap (max 1) range, x)
  case xs of
    [] → returnA ⤙ error "Hedgehog.Arrow.nonEmpty: internal error, generated empty list"
    _ → returnA ⤙ NonEmpty.fromList xs

unfreeze ∷ ArrowGen f ⇒ f (Tree a) a
unfreeze = arr treeValue . shrink id . arr (treeChildren,)

data Subterms n a
  = One a
  | All (Vec n a)
  deriving (Foldable, Functor, Traversable)

shrinkSubterms ∷ Subterms n a → [Subterms n a]
shrinkSubterms (One _) = []
shrinkSubterms (All xs) = fmap One (toList xs)

genSubterms ∷ ArrowGen f ⇒ Vec n (f a b) → f a (Subterms n b)
genSubterms =
  ((traverseA (unfreeze . arr fst) . arr (,())) .)
    . ($< shrinkSubterms)
    . shrink
    . getAp
    . fmap All
    . traverse (Ap . freeze)

fromSubterms ∷ ArrowChoice f ⇒ f (Vec n a, b) a → f (Subterms n a, b) a
fromSubterms f = proc (xs, y) → do
  case xs of
    One x → returnA ⤙ x
    All ys → f ⤙ (ys, y)

subtermMVec ∷ ArrowGen f ⇒ Vec n (f a b) → f (Vec n b, a) b → f a b
subtermMVec gs f = proc x → do
  y ← genSubterms gs ⤙ x
  fromSubterms f ⤙ (y, x)

subterm ∷ ArrowGen f ⇒ f a b → (b → b) → f a b
subterm f g = subtermA f (arr (g . fst))

subtermA ∷ ArrowGen f ⇒ f a b → f (b, a) b → f a b
subtermA gx f = subtermMVec (gx :. Nil) (f . arr \(x :. Nil, y) → (x, y))

subterm2 ∷ ArrowGen f ⇒ f a b → f a b → (b → b → b) → f a b
subterm2 f g h = subtermA2 f g (arr \(x, y, _) → h x y)

subtermA2 ∷ ArrowGen f ⇒ f a b → f a b → f (b, b, a) b → f a b
subtermA2 gx gy f = subtermMVec (gx :. gy :. Nil) (f . arr \(x :. y :. Nil, z) → (x, y, z))

subterm3 ∷ ArrowGen f ⇒ f a b → f a b → f a b → (b → b → b → b) → f a b
subterm3 f g h i = subtermA3 f g h (arr \(x, y, z, _) → i x y z)

subtermA3 ∷ ArrowGen f ⇒ f a b → f a b → f a b → f (b, b, b, a) b → f a b
subtermA3 gx gy gz f = subtermMVec (gx :. gy :. gz :. Nil) (f . arr \(x :. y :. z :. Nil, w) → (x, y, z, w))

subsequence ∷ ArrowGen f ⇒ f [a] [a]
subsequence = shrink (filterA bool_) $< Shrink.list

subset ∷ ArrowGen f ⇒ f (Set a) (Set a)
subset = arr Set.fromDistinctAscList . subsequence . arr Set.toList

shuffle ∷ ArrowGen f ⇒ f [a] [a]
shuffle = arr toList . shuffleSeq . arr Seq.fromList

shuffleSeq ∷ ArrowGen f ⇒ f (Seq a) (Seq a)
shuffleSeq = proc xs → do
  if null xs
    then
      returnA ⤙ Seq.empty
    else do
      n ← integral ⤙ Range.constant 0 (length xs - 1)
      case Seq.lookup n xs of
        Just y → do
          ys ← shuffleSeq ⤙ Seq.deleteAt n xs
          returnA ⤙ y Seq.<| ys
        Nothing → do
          returnA ⤙ error "Hedgehog.Arrow.shuffleSeq: internal error, lookup in empty sequence"
