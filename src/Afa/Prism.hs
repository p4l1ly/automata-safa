{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}

module Afa.Prism where

import Prelude hiding (not, or, and)

import Control.Lens.Prism
import Control.Lens.Fold (preview)
import Control.Lens.Review (review)
import Data.Functor.Compose

import qualified Afa.Functor as T
import qualified Afa.TreeDag.Patterns as TD

class Term f where
  lfalse :: Prism' (f a) ()
  ltrue :: Prism' (f a) ()
  var :: Prism' (f a) Int
  state :: Prism' (f a) Int
  not :: Prism' (f a) a
  or :: Prism' (f a) [a]
  and :: Prism' (f a) [a]

pattern LFalse :: Term f => f a
pattern LFalse <- (preview lfalse -> Just ()) where LFalse = review lfalse ()

pattern LTrue :: Term f => f a
pattern LTrue <- (preview ltrue -> Just ()) where LTrue = review ltrue ()

pattern Var :: Term f => Int -> f a
pattern Var a <- (preview var -> Just a) where Var a = review var a

pattern State :: Term f => Int -> f a
pattern State a <- (preview state -> Just a) where State a = review state a

pattern Not :: Term f => a -> f a
pattern Not a <- (preview not -> Just a) where Not a = review not a

pattern Or :: Term f => [a] -> f a
pattern Or a <- (preview or -> Just a) where Or a = review or a

pattern And :: Term f => [a] -> f a
pattern And a <- (preview and -> Just a) where And a = review and a

instance Term T.Term where
  lfalse = prism (const T.LFalse)$ \case T.LFalse -> Right (); x -> Left x
  ltrue = prism (const T.LTrue)$ \case T.LTrue -> Right (); x -> Left x
  var = prism T.Var$ \case T.Var a -> Right a; x -> Left x
  state = prism T.State$ \case T.State a -> Right a; x -> Left x
  not = prism T.Not$ \case T.Not a -> Right a; x -> Left x
  or = prism T.Or$ \case T.Or a -> Right a; x -> Left x
  and = prism T.And$ \case T.And a -> Right a; x -> Left x

instance Term TD.Term where
  lfalse = prism (const TD.LFalse)$ \case TD.LFalse -> Right (); x -> Left x
  ltrue = prism (const TD.LTrue)$ \case TD.LTrue -> Right (); x -> Left x
  var = prism TD.Var$ \case TD.Var a -> Right a; x -> Left x
  state = prism TD.State$ \case TD.State a -> Right a; x -> Left x
  not = prism TD.Not$ \case TD.Not a -> Right a; x -> Left x
  or = prism TD.Or$ \case TD.Or a -> Right a; x -> Left x
  and = prism TD.And$ \case TD.And a -> Right a; x -> Left x

isRecursive :: Term f => f a -> Bool
isRecursive (Not _) = True
isRecursive (And _) = True
isRecursive (Or _) = True
isRecursive _ = False
