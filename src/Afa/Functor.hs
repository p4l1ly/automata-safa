{-# LANGUAGE LambdaCase #-}
module Afa.Functor where

data Term rec
  = LTrue
  | LFalse
  | Var Int
  | State Int
  | Not rec
  | And [rec]
  | Or [rec]

statesArePositive_alg :: Term (Maybe Bool) -> Maybe Bool
statesArePositive_alg LTrue = Just False
statesArePositive_alg LFalse = Just False
statesArePositive_alg (Var _) = Just False
statesArePositive_alg (State _) = Just True
statesArePositive_alg (Not x) = x >>= \case True -> Nothing; False -> Just False
statesArePositive_alg (And xs) = or <$> sequence xs
statesArePositive_alg (Or xs) = or <$> sequence xs
