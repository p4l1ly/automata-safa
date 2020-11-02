{-# LANGUAGE PatternSynonyms #-}

module Afa.Term.TreeF where

import Data.Functor.Tree
import qualified Afa.Term as T

type Term p = TreeF (T.Term p) Int

pattern NRef ix = Node ix
pattern Ref ix = Leaf ix

pattern And ts = NRef (T.And ts)
pattern Or ts = NRef (T.Or ts)
pattern LTrue = NRef T.LTrue
pattern Predicate x = NRef (T.Predicate x)
pattern State x = NRef (T.State x)
