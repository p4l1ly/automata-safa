{-# LANGUAGE PatternSynonyms #-}

module Afa.Term.TreeF where

import Data.Functor.Tree
import qualified Afa.Term as T

type Term = TreeF T.Term Int

pattern NRef ix = Node ix
pattern Ref ix = Leaf ix

pattern And ts = NRef (T.And ts)
pattern Or ts = NRef (T.Or ts)
pattern Not t = NRef (T.Not t)
pattern LFalse = NRef T.LFalse
pattern LTrue = NRef T.LTrue
pattern Var x = NRef (T.Var x)
pattern State x = NRef (T.State x)
