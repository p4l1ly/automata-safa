{-# LANGUAGE LambdaCase #-}

module Afa.Term.Mix.Simplify where

import Control.Category ((>>>))
import Data.Monoid (Endo(..))
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
import Afa.Lib (nonEmptyConcatMap, (>&>))
import Data.Hashable
import qualified Data.HashSet as S

import Afa.Term.Mix

deLit :: Term p q (Either Bool a) -> Either Bool (Term p q a)
deLit LTrue = Left True
deLit (Predicate p) = Right$ Predicate p
deLit (State q) = Right$ State q
deLit (And xs) = case xs' of
  Nothing -> Left False
  Just [] -> Left True
  Just (x:xs) -> Right$ And$ x :| xs
  where
  xs' = (`appEndo` Just [])$ flip foldMap xs$ \case
    Left True -> Endo id
    Left False -> Endo (const Nothing)
    Right a -> Endo ((a:) <$>)
deLit (Or xs) = case xs' of
  Nothing -> Left True
  Just [] -> Left False
  Just (x:xs) -> Right$ Or$ x :| xs
  where
  xs' = (`appEndo` Just [])$ flip foldMap xs$ \case
    Left False -> Endo id
    Left True -> Endo (const Nothing)
    Right a -> Endo ((a:) <$>)

deUnary :: Term p q t -> Either t (Term p q t)
deUnary = \case
  And (t :| []) -> Left t
  Or (t :| []) -> Left t
  bt -> Right bt

flatten :: (t -> Term p q t) -> Term p q t -> Term p q t
flatten project = \case
  And ts -> And$ flip nonEmptyConcatMap ts$ \t ->
    case project t of
      And ts2 -> ts2
      _ -> t :| []
  Or ts -> Or$ flip nonEmptyConcatMap ts$ \t ->
    case project t of
      Or ts2 -> ts2
      _ -> t :| []
  bt -> bt

absorb :: (Eq r, Hashable r) => (t -> Term p q t) -> (t -> r)
  -> Term p q t -> Either Bool (Term p q t)
absorb project getR = \case
  And ts ->
    let tsHash = foldl (flip S.insert) S.empty (getR <$> ts)
        ts3 = flip NE.filter ts$ project >>> \case
          Or ts2 -> not$ any (\t -> S.member (getR t) tsHash) ts2
          _ -> True
    in maybe (Left True) (Right . And)$ NE.nonEmpty ts3
  Or ts ->
    let tsHash = foldl (flip S.insert) S.empty (getR <$> ts)
        ts3 = flip NE.filter ts$ project >>> \case
          And ts2 -> not$ any (\t -> S.member (getR t) tsHash) ts2
          _ -> True
    in maybe (Left True) (Right . Or)$ NE.nonEmpty ts3
  bt -> Right bt

simplify :: (Eq r, Hashable r)
  => (t -> Term p q t)
  -> (t -> r)
  -> Term p q (Either Bool t) -> Either Bool (Either t (Term p q t))
simplify project getR =
  (deLit >&> deUnary >&> flatten project >>> absorb project getR) >>> join2
  where
  join2 (Right (Right (Left b))) = Left b
  join2 (Right (Right (Right t))) = Right (Right t)
  join2 (Left b) = Left b
  join2 (Right (Left t)) = Right (Left t)
