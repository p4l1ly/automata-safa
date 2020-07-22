{-# LANGUAGE PatternSynonyms #-}

module Afa.Functor.Fix where

import Data.Functor.Foldable
import qualified Afa.Functor as A

pattern LTrue = Fix A.LTrue
pattern LFalse = Fix A.LFalse
pattern Var x = Fix (A.Var x)
pattern State x = Fix (A.State x)
pattern Not x = Fix (A.Not x)
pattern And x = Fix (A.And x)
pattern Or x = Fix (A.Or x)
