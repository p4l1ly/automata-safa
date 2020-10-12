{-# LANGUAGE PatternSynonyms #-}

module Afa.Term.Fix where

import Data.Functor.Foldable
import qualified Afa.Term as T

type Term = Fix T.Term

pattern LTrue = Fix T.LTrue
pattern LFalse = Fix T.LFalse
pattern Var x = Fix (T.Var x)
pattern State x = Fix (T.State x)
pattern Not x = Fix (T.Not x)
pattern And x = Fix (T.And x)
pattern Or x = Fix (T.Or x)
