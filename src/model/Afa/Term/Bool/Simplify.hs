{-# LANGUAGE LambdaCase #-}

module Afa.Term.Bool.Simplify where

import Control.Monad
import Control.Category ((>>>))
import Data.Monoid (Endo(..))
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
import Afa.Lib (nonEmptyConcatMap, (>&>))
import Data.Hashable
import qualified Data.HashSet as S

import Afa.Term.Bool


deLit :: Term p (Either Bool a) -> Either Bool (Term p a)
deLit LTrue = Left True
deLit LFalse = Left False
deLit (Predicate p) = Right$ Predicate p
deLit (Not (Left b)) = Left$ not b
deLit (Not (Right x)) = Right$ Not x
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

deUnary :: Term p t -> Either t (Term p t)
deUnary = \case
  And (t :| []) -> Left t
  Or (t :| []) -> Left t
  bt -> Right bt

deNotNot :: (t' -> Term p t) -> Term p t' -> Either t (Term p t')
deNotNot project = \case
  bt@(Not t) -> case project t of
    Not t -> Left t
    _ -> Right bt
  bt -> Right bt

flatten :: (t -> Term p t) -> Term p t -> Term p t
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

absorb :: (Eq r, Hashable r) => (t -> Term p t) -> (t -> r) -> Term p t -> Term p t
absorb project getR = \case
  And ts ->
    let tsHash = foldl (flip S.insert) S.empty (getR <$> ts)
        ts3 = flip NE.filter ts$ project >>> \case
          Or ts2 -> not$ any (\t -> S.member (getR t) tsHash) ts2
          _ -> True
    in maybe LTrue And$ NE.nonEmpty ts3
  Or ts ->
    let tsHash = foldl (flip S.insert) S.empty (getR <$> ts)
        ts3 = flip NE.filter ts$ project >>> \case
          And ts2 -> not$ any (\t -> S.member (getR t) tsHash) ts2
          _ -> True
    in maybe LFalse Or$ NE.nonEmpty ts3
  bt -> bt

simplify :: (Eq r, Hashable r)
  => (t -> Term p t)
  -> (t -> r)
  -> Term p (Either Bool t) -> Either Bool (Either t (Term p t))
simplify project getR =
  deLit >&> deUnary >=> deNotNot project >&> flatten project >>> absorb project getR
