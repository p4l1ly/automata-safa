{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Afa.Term.Simplify where

import Control.Lens

import qualified Afa.Term.Mix as MTerm

class HasIdentity way s where
  isIdentity :: s -> Bool

class ReducibleVia way r i where
  partitionVia :: Applicative f => (i -> f Int) -> r -> Maybe (f [r])
  permuteVia :: Applicative f => (i -> f Int) -> r -> Maybe (f [r])

class TraversableVia way r r' i i' where
  traversalVia :: Traversal r r' i i'

removeIdentities ::
  forall way1 way2 s s' i.
  ( HasIdentity way1 s
  , HasIdentity way2 s
  , ReducibleVia way1 s (Either Bool i)
  , ReducibleVia way2 s (Either Bool i)
  , TraversableVia way1 s s' (Either Bool i) i
  , TraversableVia way2 s s' (Either Bool i) i
  ) =>
  s ->
  Either Bool s'
removeIdentities t
  | isIdentity @way1 t = Left True
  | isIdentity @way2 t = Left False
  | otherwise = case xs1 of
    Nothing -> case xs2 of
      Nothing -> undefined
      Just Nothing -> Left True
      Just (Just (kept : _)) ->
        Right $
          kept & traversalVia @way2 @s @s' @(Either Bool i) %~ \case Right a -> a
    Just Nothing -> Left False
    Just (Just (kept : _)) ->
      Right $
        kept & traversalVia @way1 @s @s' @(Either Bool i) %~ \case Right a -> a
  where
    xs1 = ($ t) $
      partitionVia @way1 $ \case
        Left True -> Just 1
        Left False -> Nothing
        Right (a :: i) -> Just 0
    xs2 = ($ t) $
      partitionVia @way2 $ \case
        Left True -> Just 1
        Left False -> Nothing
        Right (a :: i) -> Just 0
