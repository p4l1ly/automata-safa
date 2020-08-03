{-# LANGUAGE PatternSynonyms #-}

module Afa.TreeDag.Patterns where

import Data.Functor.Compose

import qualified Afa.Functor as T

type Term = Compose (Either Int) T.Term

pattern And ts = (Compose (Right (T.And ts)))
pattern Or ts = (Compose (Right (T.Or ts)))
pattern Not t = (Compose (Right (T.Not t)))
pattern LFalse = (Compose (Right T.LFalse))
pattern LTrue = (Compose (Right T.LTrue))
pattern Var x = (Compose (Right (T.Var x)))
pattern State x = (Compose (Right (T.State x)))
