{-# LANGUAGE PatternSynonyms #-}

module Afa.TreeDag.Patterns.Builder where

import Data.Functor.Foldable.Dag.TreeHybrid (TreeHybrid(..))

import qualified Afa.Functor as T

type Term = TreeHybrid T.Term Int

pattern And ts = (TreeHybrid (Right (T.And ts)))
pattern Or ts = (TreeHybrid (Right (T.Or ts)))
pattern Not t = (TreeHybrid (Right (T.Not t)))
pattern LFalse = (TreeHybrid (Right T.LFalse))
pattern LTrue = (TreeHybrid (Right T.LTrue))
pattern Var x = (TreeHybrid (Right (T.Var x)))
pattern State x = (TreeHybrid (Right (T.State x)))
pattern Ref ix = (TreeHybrid (Left ix))
