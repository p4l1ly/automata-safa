{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}

module Afa.Term.Bool where

import GHC.Generics
import Data.Functor.Classes
import Generic.Data (Generically1(..))
import Generic.Data.Orphans ()
import Data.Hashable
import Data.Hashable.Lifted
import Data.List.NonEmpty (NonEmpty(..))

import Afa.Lib ()

data Term p rec
  = LTrue
  | LFalse
  | Predicate p
  | And (NonEmpty rec)
  | Or (NonEmpty rec)
  | Not rec
  deriving
    (Functor, Foldable, Traversable, Eq, Generic, Generic1, Hashable, Hashable1, Show)
  deriving Eq1 via (Generically1 (Term p))
  deriving Show1 via (Generically1 (Term p))

data Plate p t p' t' f = Plate
  { pLTrue :: forall p' t'. f (Term p' t')
  , pLFalse :: forall p' t'. f (Term p' t')
  , pPredicate :: forall t'. p -> f (Term p' t')
  , pAnd :: forall p'. NonEmpty t -> f (Term p' t')
  , pOr :: forall p'. NonEmpty t -> f (Term p' t')
  , pNot :: forall p'. t -> f (Term p' t')
  }

plateBase :: Applicative f => Plate p t p t f
plateBase = Plate
  { pLTrue = pure LTrue
  , pLFalse = pure LFalse
  , pPredicate = pure . Predicate
  , pAnd = pure . And
  , pOr = pure . Or
  , pNot = pure . Not
  }

applyPlate :: Plate p t p' t' f -> Term p t -> f (Term p' t')
applyPlate Plate{pLTrue, pLFalse, pPredicate, pAnd, pOr, pNot} = \case
  LTrue -> pLTrue
  LFalse -> pLFalse
  Predicate p -> pPredicate p
  And ts -> pAnd ts
  Or ts -> pOr ts
  Not ts -> pNot ts

data ChildMod p t p' t' f = ChildMod
  { lP :: p -> f p'
  , lT :: t -> f t'
  }

pureChildMod :: Applicative f => ChildMod p t p t f
pureChildMod = ChildMod{ lP = pure, lT = pure }

childModToPlate :: Applicative f => ChildMod p t p' t' f -> Plate p t p' t' f
childModToPlate ChildMod{lP, lT} = plateBase
  { pPredicate = fmap Predicate . lP
  , pAnd = fmap And . traverse lT
  , pOr = fmap Or . traverse lT
  , pNot = fmap Not . lT
  }

modChilds :: Applicative f => ChildMod p t p' t' f -> Term p t -> f (Term p' t')
modChilds = applyPlate . childModToPlate
