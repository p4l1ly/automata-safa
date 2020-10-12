{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DeriveAnyClass #-}

module Afa.Term where

import GHC.Generics
import Data.Functor.Classes
import Generic.Data (Generically1(..))
import Generic.Data.Orphans ()
import Data.Hashable
import Data.Hashable.Lifted

data Term rec
  = LTrue
  | LFalse
  | Var Int
  | State Int
  | Not rec
  | And [rec]
  | Or [rec]
  deriving
    (Functor, Foldable, Traversable, Eq, Generic, Generic1, Hashable, Hashable1, Show)
  deriving Eq1 via (Generically1 Term)
  deriving Show1 via (Generically1 Term)
