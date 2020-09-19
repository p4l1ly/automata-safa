{-# LANGUAGE PatternSynonyms #-}

module Afa.TreeDag.Patterns.Builder where

import qualified Data.Functor.Foldable.Dag.TreeHybrid as TD

import qualified Afa.Functor as T

type Term = TD.TreeHybrid T.Term Int

pattern NRef ix = TD.NRef ix
pattern Ref ix = TD.Ref ix

pattern And ts = TD.NRef (T.And ts)
pattern Or ts = TD.NRef (T.Or ts)
pattern Not t = TD.NRef (T.Not t)
pattern LFalse = TD.NRef T.LFalse
pattern LTrue = TD.NRef T.LTrue
pattern Var x = TD.NRef (T.Var x)
pattern State x = TD.NRef (T.State x)
