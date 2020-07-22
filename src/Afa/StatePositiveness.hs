{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module Afa.StatePositiveness where

import Control.Monad (foldM)
import Data.Maybe (isJust)

import Data.Functor.Foldable (cata, embed, Corecursive, Recursive, Base)

import Afa.Functor (Term(..))

statesArePositive :: (Recursive t, Term ~ Base t) => t -> Bool
statesArePositive = isJust . cata alg
  where
    alg :: Term (Maybe Bool) -> Maybe Bool
    alg LTrue = Just False
    alg LFalse = Just False
    alg (Var _) = Just False
    alg (State _) = Just True
    alg (Not x) = x >>= \case True -> Nothing; False -> Just False
    alg (And xs) = or <$> sequence xs
    alg (Or xs) = or <$> sequence xs

data StateSignum = Positive | Negative | None

statesCanBePositive :: (Recursive t, Term ~ Base t) => t -> Bool
statesCanBePositive t = case cata alg t of
  Just Positive -> True
  Just None -> True
  _ -> False
  where
    alg :: Term (Maybe StateSignum) -> Maybe StateSignum
    alg LTrue = Just None
    alg LFalse = Just None
    alg (Var _) = Just None
    alg (State _) = Just Positive
    alg (Not x) = x >>= \case
      Positive -> Just Negative
      Negative -> Just Positive
      None -> Just None
    alg (And xs) = sequence xs >>= foldM merge None
    alg (Or xs) = sequence xs >>= foldM merge None

    merge :: StateSignum -> StateSignum -> Maybe StateSignum
    merge x None = Just x
    merge None x = Just x
    merge Positive Positive = Just Positive
    merge Negative Negative = Just Negative
    merge _ _ = Nothing

makeStatesPositive
  :: forall t. (Corecursive t, Recursive t, Term ~ Base t)
  => t -> Maybe t
makeStatesPositive t = cata alg t >>= \case
  (Negative, t) -> Nothing
  (_, t) -> Just t
  where
    alg :: Term (Maybe (StateSignum, t)) -> Maybe (StateSignum, t)
    alg LTrue = Just (None, embed LTrue)
    alg LFalse = Just (None, embed LFalse)
    alg (Var x) = Just (None, embed$ Var x)
    alg (State x) = Just (Positive, embed$ State x)
    alg (Not x) = x >>= \case
      (Positive, t) -> Just (Negative, t)
      (Negative, t) -> Just (Positive, t)
      (None, t) -> Just (None, embed$ Not t)
    alg (And xs) = sequence xs >>= foldM merge (None, []) >>= \case
      (Negative, xs) -> Just (Negative, embed$ Or xs)
      (sig, xs) -> Just (sig, embed$ And xs)
    alg (Or xs) = sequence xs >>= foldM merge (None, []) >>= \case
      (Negative, xs) -> Just (Negative, embed$ And xs)
      (sig, xs) -> Just (sig, embed$ Or xs)

    merge :: (StateSignum, [t]) -> (StateSignum, t) -> Maybe (StateSignum, [t])
    merge (None, ts) (None, t) = Just (None, t : ts)
    merge (Positive, ts) (None, t) = Just (Positive, t : ts)
    merge (Negative, ts) (None, t) = Just (Negative, embed (Not t) : ts)
    merge (None, ts) (Positive, t) = Just (Positive, t : ts)
    merge (Positive, ts) (Positive, t) = Just (Positive, t : ts)
    merge (Negative, ts) (Positive, t) = Nothing
    merge (None, ts) (Negative, t) = Just (Negative, t : map (embed . Not) ts)
    merge (Positive, ts) (Negative, t) = Nothing
    merge (Negative, ts) (Negative, t) = Just (Negative, t : ts)
