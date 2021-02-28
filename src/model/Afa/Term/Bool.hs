{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE BangPatterns #-}

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
  | Predicate !p
  | And !(NonEmpty rec)
  | Or !(NonEmpty rec)
  | Not !rec
  deriving
    (Functor, Foldable, Traversable, Eq, Generic, Generic1, Hashable, Hashable1, Show)
  deriving Eq1 via (Generically1 (Term p))
  deriving Show1 via (Generically1 (Term p))

-- TODO Plate === MTra, I've left it here for naming backward compatibility.
-- TODO study profunctor optics, I have a feeling that the following is related.
-- Plate -------------------------------------------------------------------------------

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

-- MFun --------------------------------------------------------------------------------

data MFun p t p' t' = MFun
  { mfunLTrue :: forall p' t'. Term p' t'
  , mfunPredicate :: forall t'. p -> Term p' t'
  , mfunAnd :: forall p'. NonEmpty t -> Term p' t'
  , mfunOr :: forall p'. NonEmpty t -> Term p' t'
  , mfunNot :: forall p'. t -> Term p' t'
  }

mfun0 :: MFun p t p t
mfun0 = MFun
  { mfunLTrue = LTrue
  , mfunPredicate = Predicate
  , mfunAnd = And
  , mfunOr = Or
  , mfunNot = Not
  }

appMFun :: MFun p t p' t' -> Term p t -> Term p' t'
appMFun MFun{mfunLTrue, mfunPredicate, mfunAnd, mfunOr, mfunNot} = \case
  LTrue -> mfunLTrue
  Predicate p -> mfunPredicate p
  And ts -> mfunAnd ts
  Or ts -> mfunOr ts
  Not t -> mfunNot t

data MTFun p t p' t' = MTFun
  { mtfunP :: p -> p'
  , mtfunT :: t -> t'
  }

mtfun0 :: MTFun p t p t
mtfun0 = MTFun id id

fromMTFun :: MTFun p t p' t' -> MFun p t p' t'
fromMTFun MTFun{mtfunP, mtfunT} = mfun0
  { mfunPredicate = Predicate . mtfunP
  , mfunAnd = And . fmap mtfunT
  , mfunOr = Or . fmap mtfunT
  , mfunNot = Not . mtfunT
  }

appMTFun :: MTFun p t p' t' -> Term p t -> Term p' t'
appMTFun = appMFun . fromMTFun

-- MFol --------------------------------------------------------------------------------

data MFol p t m = MFol
  { mfolLTrue :: m
  , mfolPredicate :: p -> m
  , mfolAnd :: NonEmpty t -> m
  , mfolOr :: NonEmpty t -> m
  , mfolNot :: t -> m
  }

mfol0 :: Monoid m => MFol p t m
mfol0 = MFol
  { mfolLTrue = mempty
  , mfolPredicate = const mempty
  , mfolAnd = const mempty
  , mfolOr = const mempty
  , mfolNot = const mempty
  }

appMFol :: MFol p t m -> Term p t -> m
appMFol MFol{mfolLTrue, mfolPredicate, mfolAnd, mfolOr, mfolNot} = \case
  LTrue -> mfolLTrue
  Predicate p -> mfolPredicate p
  And ts -> mfolAnd ts
  Or ts -> mfolOr ts
  Not t -> mfolNot t

data MTFol p t m = MTFol
  { mtfolP :: p -> m
  , mtfolT :: t -> m
  }

mtfol0 :: Monoid m => MTFol p t m
mtfol0 = MTFol (const mempty) (const mempty)

fromMTFol :: Monoid m => MTFol p t m -> MFol p t m
fromMTFol MTFol{mtfolP, mtfolT} = mfol0
  { mfolPredicate = mtfolP
  , mfolAnd = foldMap mtfolT
  , mfolOr = foldMap mtfolT
  , mfolNot = mtfolT
  }

appMTFol :: Monoid m => MTFol p t m -> Term p t -> m
appMTFol = appMFol . fromMTFol

-- MTra --------------------------------------------------------------------------------

data MTra p t p' t' f = MTra
  { mtraLTrue :: forall p' t'. f (Term p' t')
  , mtraPredicate :: forall t'. p -> f (Term p' t')
  , mtraAnd :: forall p'. NonEmpty t -> f (Term p' t')
  , mtraOr :: forall p'. NonEmpty t -> f (Term p' t')
  , mtraNot :: forall p'. t -> f (Term p' t')
  }

mtra0 :: Applicative f => MTra p t p t f
mtra0 = MTra
  { mtraLTrue = pure LTrue
  , mtraPredicate = pure . Predicate
  , mtraAnd = pure . And
  , mtraOr = pure . Or
  , mtraNot = pure . Not
  }

appMTra :: MTra p t p' t' f -> Term p t -> f (Term p' t')
appMTra MTra{mtraLTrue, mtraPredicate, mtraAnd, mtraOr, mtraNot} = \case
  LTrue -> mtraLTrue
  Predicate p -> mtraPredicate p
  And ts -> mtraAnd ts
  Or ts -> mtraOr ts
  Not t -> mtraNot t

data MTTra p t p' t' f = MTTra
  { mttraP :: p -> f p'
  , mttraT :: t -> f t'
  }

mttra0 :: forall f p t p' t'. Applicative f => MTTra p t p t f
mttra0 = MTTra pure pure

fromMTTra :: Applicative f => MTTra p t p' t' f -> MTra p t p' t' f
fromMTTra MTTra{mttraP, mttraT} = mtra0
  { mtraPredicate = fmap Predicate . mttraP
  , mtraAnd = fmap And . traverse mttraT
  , mtraOr = fmap Or . traverse mttraT
  , mtraNot = fmap Not . mttraT
  }

appMTTra :: forall f p t p' t'. Applicative f
  => MTTra p t p' t' f -> Term p t -> f (Term p' t')
appMTTra = appMTra . fromMTTra
