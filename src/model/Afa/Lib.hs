{-# LANGUAGE ViewPatterns #-}

module Afa.Lib where

import Data.Either
import Data.Monoid (Any(..))
import Data.Hashable.Lifted
import Data.List.NonEmpty (NonEmpty(..), toList)
import qualified Data.List.NonEmpty as NE
import Data.Array
import Data.Array.Base (unsafeAccumArray)

instance Hashable1 NonEmpty where
  liftHashWithSalt h salt (a :| as) = liftHashWithSalt h (h salt a) as

nonEmptyConcatMap :: (a -> NonEmpty b) -> NonEmpty a -> NonEmpty b
nonEmptyConcatMap f ((f -> h:|hs):|xs) = h :| hs ++ concatMap (toList . f) xs

listArray' :: [a] -> Array Int a
listArray' as = listArray (0, length as - 1) as

(>&>) :: Functor f => (a -> f b) -> (b -> c) -> a -> f c
ff >&> f = fmap f . ff
infixr 1 >&>

-- PERF: use hashmap? radix grouping?
nonemptyCanonicalizeWith :: (Eq r, Ord r) => (t -> r) -> NonEmpty t -> NonEmpty t
nonemptyCanonicalizeWith f = NE.map NE.head . NE.groupWith1 f . NE.sortWith f

-- We don't use view patterns for the first element of the tuple because we
-- need to check Any True pattern first, otherwise there might be an error in
-- ixMap!i0.
eixMappedGs
  :: Array Int a -> Array Int (Either Bool Int) -> Array Int Any -> Array Int Any
eixMappedGs arr ixMap gs = unsafeAccumArray (\_ _ -> Any True) mempty (bounds arr)
  [ (i, ())
  | (i0, Any True) <- assocs gs
  , let ei = ixMap!i0
  , isRight ei
  , let Right i = ei
  ]

eixMappedGs2
  :: Array Int a -> Array Int (Either Bool Int) -> Array Int Any -> Array Int DumbCount
eixMappedGs2 arr ixMap gs = unsafeAccumArray (\_ _ -> Many) mempty (bounds arr)
  [ (i, ())
  | (i0, Any True) <- assocs gs
  , let ei = ixMap!i0
  , isRight ei
  , let Right i = ei
  ]


data DumbCount = Zero | One | Many deriving (Show)
instance Semigroup DumbCount where
  Zero <> x = x
  x <> Zero = x
  _ <> _ = Many
instance Monoid DumbCount where
  mempty = Zero
