{-# LANGUAGE PatternSynonyms #-}

module Afa.TreeDag.Patterns where

import Data.Functor.Compose
import Data.Functor.Foldable.Dag.TreeHybrid (pattern BNRef, pattern BRef, MyBase)

import qualified Afa.Functor as T

type Term = MyBase T.Term Int

pattern NRef x = BNRef x
pattern Ref x = BRef x

pattern And ts = NRef (T.And ts)
pattern Or ts = NRef (T.Or ts)
pattern Not t = NRef (T.Not t)
pattern LFalse = NRef T.LFalse
pattern LTrue = NRef T.LTrue
pattern Var x = NRef (T.Var x)
pattern State x = NRef (T.State x)
