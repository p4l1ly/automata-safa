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

data Term p q rec
  = LTrue
  | Predicate p
  | State q
  | And [rec]
  | Or [rec]
  deriving
    (Functor, Foldable, Traversable, Eq, Generic, Generic1, Hashable, Hashable1, Show)
  deriving Eq1 via (Generically1 (Term p q))
  deriving Show1 via (Generically1 (Term p q))

newtype Term_p q rec p = Term_p {unTerm_p :: Term p q rec}
instance Functor (Term_p q rec) where
  fmap fn (Term_p x) = Term_p$ case x of
    Predicate p -> Predicate (fn p);
    LTrue -> LTrue
    State q -> State q
    And xs -> And xs
    Or xs -> Or xs

newtype Term_q p rec q = Term_q {unTerm_q :: Term p q rec}
instance Functor (Term_q p rec) where
  fmap fn (Term_q x) = Term_q$ case x of
    LTrue -> LTrue
    State q -> State (fn q)
    Predicate p -> Predicate p;
    And xs -> And xs
    Or xs -> Or xs
