{-# LANGUAGE PatternSynonyms #-}

module Afa.Term.Fix where

import Data.Functor.Foldable
import qualified Afa.Term as T

type Term p = Fix (T.Term p)

pattern LTrue = Fix T.LTrue
pattern Predicate x = Fix (T.Predicate x)
pattern State x = Fix (T.State x)
pattern And x = Fix (T.And x)
pattern Or x = Fix (T.Or x)
