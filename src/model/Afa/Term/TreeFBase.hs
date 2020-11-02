{-# LANGUAGE PatternSynonyms #-}

module Afa.Term.TreeFBase where

import Data.Functor.Compose
import Data.Functor.Tree (pattern BNode, pattern BLeaf, TreeBase)

import qualified Afa.Term as T

type Term p = TreeBase (T.Term p) Int

pattern NRef x = BNode x
pattern Ref x = BLeaf x

pattern And ts = NRef (T.And ts)
pattern Or ts = NRef (T.Or ts)
pattern LTrue = NRef T.LTrue
pattern Predicate x = NRef (T.Predicate x)
pattern State x = NRef (T.State x)
