{-# LANGUAGE PatternSynonyms #-}

module Afa.Term.TreeFBase where

import Data.Functor.Compose
import Data.Functor.Tree (pattern BNode, pattern BLeaf, TreeBase)

import qualified Afa.Term as T

type Term = TreeBase T.Term Int

pattern NRef x = BNode x
pattern Ref x = BLeaf x

pattern And ts = NRef (T.And ts)
pattern Or ts = NRef (T.Or ts)
pattern Not t = NRef (T.Not t)
pattern LFalse = NRef T.LFalse
pattern LTrue = NRef T.LTrue
pattern Var x = NRef (T.Var x)
pattern State x = NRef (T.State x)
