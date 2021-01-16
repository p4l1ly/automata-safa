{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE BangPatterns #-}

module Afa.Term.Mix where

import GHC.Generics
import Data.Functor.Classes
import Generic.Data (Generically1(..))
import Generic.Data.Orphans ()
import Data.Hashable
import Data.Hashable.Lifted
import Data.List.NonEmpty (NonEmpty(..))

import Afa.Lib ()

data Term p q rec
  = LTrue
  | Predicate !p
  | State !q
  | And !(NonEmpty rec)
  | Or !(NonEmpty rec)
  deriving
    (Functor, Foldable, Traversable, Eq, Generic, Generic1, Hashable, Hashable1, Show)
  deriving Eq1 via (Generically1 (Term p q))
  deriving Show1 via (Generically1 (Term p q))

data Plate p q t p' q' t' f = Plate
  { pLTrue :: forall p' q' t'. f (Term p' q' t')
  , pPredicate :: forall q' t'. p -> f (Term p' q' t')
  , pState :: forall p' t'. q -> f (Term p' q' t')
  , pAnd :: forall p' q'. NonEmpty t -> f (Term p' q' t')
  , pOr :: forall p' q'. NonEmpty t -> f (Term p' q' t')
  }

plateBase :: Applicative f => Plate p q t p q t f
plateBase = Plate
  { pLTrue = pure LTrue
  , pPredicate = pure . Predicate
  , pState = pure . State
  , pAnd = pure . And
  , pOr = pure . Or
  }

applyPlate :: Plate p q t p' q' t' f -> Term p q t -> f (Term p' q' t')
applyPlate Plate{pLTrue, pPredicate, pState, pAnd, pOr} = \case
  LTrue -> pLTrue
  Predicate p -> pPredicate p
  State q -> pState q
  And ts -> pAnd ts
  Or ts -> pOr ts

data ChildMod p q t p' q' t' f = ChildMod
  { lP :: p -> f p'
  , lQ :: q -> f q'
  , lT :: t -> f t'
  }

pureChildMod :: forall f p q t p' q' t'. Applicative f => ChildMod p q t p q t f
pureChildMod = ChildMod{ lP = pure, lQ = pure, lT = pure }

childModToPlate :: Applicative f => ChildMod p q t p' q' t' f -> Plate p q t p' q' t' f
childModToPlate ChildMod{lP, lQ, lT} = plateBase
  { pPredicate = fmap Predicate . lP
  , pState = fmap State . lQ
  , pAnd = fmap And . traverse lT
  , pOr = fmap Or . traverse lT
  }

modChilds :: forall f p q t p' q' t'. Applicative f
  => ChildMod p q t p' q' t' f -> Term p q t -> f (Term p' q' t')
modChilds = applyPlate . childModToPlate
