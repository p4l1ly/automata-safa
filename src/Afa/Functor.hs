{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}

module Afa.Functor where

import GHC.Generics
import Data.Functor.Classes
import Generic.Data (Generically1(..))
import Generic.Data.Orphans ()

data Term rec
  = LTrue
  | LFalse
  | Var Int
  | State Int
  | Not rec
  | And [rec]
  | Or [rec]
  deriving (Functor, Foldable, Traversable, Eq, Generic, Generic1)
  deriving Eq1 via (Generically1 Term)
  deriving Show1 via (Generically1 Term)
