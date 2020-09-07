{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module Afa.StatePositiveness where

import Control.Monad (foldM)
import Data.Maybe (isJust)

import Data.Functor.Foldable (cata, embed, Corecursive, Recursive, Base)

import Afa.Functor (Term(..))
import qualified Afa.Prism as P

statesArePositive :: (Recursive t, Term ~ Base t) => t -> Bool
statesArePositive = isJust . cata statesArePositive_alg

statesArePositive_alg :: Term (Maybe Bool) -> Maybe Bool
statesArePositive_alg LTrue = Just False
statesArePositive_alg LFalse = Just False
statesArePositive_alg (Var _) = Just False
statesArePositive_alg (State _) = Just True
statesArePositive_alg (Not x) = x >>= \case True -> Nothing; False -> Just False
statesArePositive_alg (And xs) = or <$> sequence xs
statesArePositive_alg (Or xs) = or <$> sequence xs

data StateSignum = Positive | Negative | None

statesCanBePositive :: (Recursive t, Term ~ Base t) => t -> Bool
statesCanBePositive t = case cata statesCanBePositive_alg t of
  Just Positive -> True
  Just None -> True
  _ -> False

statesCanBePositive_alg :: Term (Maybe StateSignum) -> Maybe StateSignum
statesCanBePositive_alg LTrue = Just None
statesCanBePositive_alg LFalse = Just None
statesCanBePositive_alg (Var _) = Just None
statesCanBePositive_alg (State _) = Just Positive
statesCanBePositive_alg (Not x) = x >>= \case
  Positive -> Just Negative
  Negative -> Just Positive
  None -> Just None
statesCanBePositive_alg (And xs) = sequence xs >>= foldM statesCanBePositive_merge None
statesCanBePositive_alg (Or xs) = sequence xs >>= foldM statesCanBePositive_merge None

statesCanBePositive_merge :: StateSignum -> StateSignum -> Maybe StateSignum
statesCanBePositive_merge x None = Just x
statesCanBePositive_merge None x = Just x
statesCanBePositive_merge Positive Positive = Just Positive
statesCanBePositive_merge Negative Negative = Just Negative
statesCanBePositive_merge _ _ = Nothing

makeStatesPositive
  :: forall t. (Corecursive t, Recursive t, Term ~ Base t)
  => t -> Maybe t
makeStatesPositive t = cata makeStatesPositive_alg t >>= \case
  (Negative, t) -> Nothing
  (_, t) -> Just t

makeStatesPositive_alg
  :: (P.Term f, Corecursive t, f ~ Base t)
  => Term (Maybe (StateSignum, t)) -> Maybe (StateSignum, t)
makeStatesPositive_alg LTrue = Just (None, embed P.LTrue)
makeStatesPositive_alg LFalse = Just (None, embed P.LFalse)
makeStatesPositive_alg (Var x) = Just (None, embed$ P.Var x)
makeStatesPositive_alg (State x) = Just (Positive, embed$ P.State x)
makeStatesPositive_alg (Not x) = x >>= \case
  (Positive, t) -> Just (Negative, t)
  (Negative, t) -> Just (Positive, t)
  (None, t) -> Just (None, embed$ P.Not t)
makeStatesPositive_alg (And xs) = sequence xs >>= foldM merge (None, []) >>= \case
  (Negative, xs) -> Just (Negative, embed$ P.Or xs)
  (sig, xs) -> Just (sig, embed$ P.And xs)
makeStatesPositive_alg (Or xs) = sequence xs >>= foldM merge (None, []) >>= \case
  (Negative, xs) -> Just (Negative, embed$ P.And xs)
  (sig, xs) -> Just (sig, embed$ P.Or xs)

merge
  :: (P.Term f, Corecursive t, f ~ Base t)
  => (StateSignum, [t]) -> (StateSignum, t) -> Maybe (StateSignum, [t])
merge (None, ts) (None, t) = Just (None, t : ts)
merge (Positive, ts) (None, t) = Just (Positive, t : ts)
merge (Negative, ts) (None, t) = Just (Negative, embed (P.Not t) : ts)
merge (None, ts) (Positive, t) = Just (Positive, t : ts)
merge (Positive, ts) (Positive, t) = Just (Positive, t : ts)
merge (Negative, ts) (Positive, t) = Nothing
merge (None, ts) (Negative, t) = Just (Negative, t : map (embed . P.Not) ts)
merge (Positive, ts) (Negative, t) = Nothing
merge (Negative, ts) (Negative, t) = Just (Negative, t : ts)


complement_alg :: (P.Term f, Corecursive t, f ~ Base t) => Term t -> t
complement_alg LTrue = embed P.LFalse
complement_alg LFalse = embed P.LTrue
complement_alg (Var x) = embed$ P.Not$ embed$ P.Var x
complement_alg (State x) = embed$ P.State x
complement_alg (Not x) = embed$ P.Not x
complement_alg (And xs) = embed$ P.Or xs
complement_alg (Or xs) = embed$ P.And xs
