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

-- TODO Plate === MTra, I've left it here for naming backward compatibility.
-- TODO study profunctor optics, I have a feeling that the following is related.
-- Plate -------------------------------------------------------------------------------

data Plate p q t p' q' t' f = Plate
  { pLTrue :: forall p' q' t'. f (Term p' q' t')
  , pPredicate :: forall q' t'. p -> f (Term p' q' t')
  , pState :: forall p' t'. q -> f (Term p' q' t')
  , pAnd :: forall p' q'. NonEmpty t -> f (Term p' q' t')
  , pOr :: forall p' q'. NonEmpty t -> f (Term p' q' t')
  }

{-# INLINE plateBase #-}
plateBase :: Applicative f => Plate p q t p q t f
plateBase = Plate
  { pLTrue = pure LTrue
  , pPredicate = pure . Predicate
  , pState = pure . State
  , pAnd = pure . And
  , pOr = pure . Or
  }

{-# INLINE applyPlate #-}
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

{-# INLINE pureChildMod #-}
pureChildMod :: forall f p q t p' q' t'. Applicative f => ChildMod p q t p q t f
pureChildMod = ChildMod{ lP = pure, lQ = pure, lT = pure }

{-# INLINE childModToPlate #-}
childModToPlate :: Applicative f => ChildMod p q t p' q' t' f -> Plate p q t p' q' t' f
childModToPlate ChildMod{lP, lQ, lT} = plateBase
  { pPredicate = fmap Predicate . lP
  , pState = fmap State . lQ
  , pAnd = fmap And . traverse lT
  , pOr = fmap Or . traverse lT
  }

{-# INLINE modChilds #-}
modChilds :: forall f p q t p' q' t'. Applicative f
  => ChildMod p q t p' q' t' f -> Term p q t -> f (Term p' q' t')
modChilds = applyPlate . childModToPlate

-- MFun --------------------------------------------------------------------------------

data MFun p q t p' q' t' = MFun
  { mfunLTrue :: forall p' q' t'. Term p' q' t'
  , mfunPredicate :: forall q' t'. p -> Term p' q' t'
  , mfunState :: forall p' t'. q -> Term p' q' t'
  , mfunAnd :: forall p' q'. NonEmpty t -> Term p' q' t'
  , mfunOr :: forall p' q'. NonEmpty t -> Term p' q' t'
  }

{-# INLINE mfun0 #-}
mfun0 :: MFun p q t p q t
mfun0 = MFun
  { mfunLTrue = LTrue
  , mfunPredicate = Predicate
  , mfunState = State
  , mfunAnd = And
  , mfunOr = Or
  }

{-# INLINE appMFun #-}
appMFun :: MFun p q t p' q' t' -> Term p q t -> Term p' q' t'
appMFun MFun{mfunLTrue, mfunPredicate, mfunState, mfunAnd, mfunOr} = \case
  LTrue -> mfunLTrue
  Predicate p -> mfunPredicate p
  State q -> mfunState q
  And ts -> mfunAnd ts
  Or ts -> mfunOr ts

data MTFun p q t p' q' t' = MTFun
  { mtfunP :: p -> p'
  , mtfunQ :: q -> q'
  , mtfunT :: t -> t'
  }

{-# INLINE mtfun0 #-}
mtfun0 :: MTFun p q t p q t
mtfun0 = MTFun id id id

{-# INLINE fromMTFun #-}
fromMTFun :: MTFun p q t p' q' t' -> MFun p q t p' q' t'
fromMTFun MTFun{mtfunP, mtfunQ, mtfunT} = mfun0
  { mfunPredicate = Predicate . mtfunP
  , mfunState = State . mtfunQ
  , mfunAnd = And . fmap mtfunT
  , mfunOr = Or . fmap mtfunT
  }

{-# INLINE appMTFun #-}
appMTFun :: MTFun p q t p' q' t' -> Term p q t -> Term p' q' t'
appMTFun = appMFun . fromMTFun

-- MFol --------------------------------------------------------------------------------

data MFol p q t m = MFol
  { mfolLTrue :: m
  , mfolPredicate :: p -> m
  , mfolState :: q -> m
  , mfolAnd :: NonEmpty t -> m
  , mfolOr :: NonEmpty t -> m
  }

{-# INLINE mfol0 #-}
mfol0 :: Monoid m => MFol p q t m
mfol0 = MFol
  { mfolLTrue = mempty
  , mfolPredicate = const mempty
  , mfolState = const mempty
  , mfolAnd = const mempty
  , mfolOr = const mempty
  }

{-# INLINE appMFol #-}
appMFol :: MFol p q t m -> Term p q t -> m
appMFol MFol{mfolLTrue, mfolPredicate, mfolState, mfolAnd, mfolOr} = \case
  LTrue -> mfolLTrue
  Predicate p -> mfolPredicate p
  State q -> mfolState q
  And ts -> mfolAnd ts
  Or ts -> mfolOr ts

data MTFol p q t m = MTFol
  { mtfolP :: p -> m
  , mtfolQ :: q -> m
  , mtfolT :: t -> m
  }

{-# INLINE mtfol0 #-}
mtfol0 :: Monoid m => MTFol p q t m
mtfol0 = MTFol (const mempty) (const mempty) (const mempty)

{-# INLINE fromMTFol #-}
fromMTFol :: Monoid m => MTFol p q t m -> MFol p q t m
fromMTFol MTFol{mtfolP, mtfolQ, mtfolT} = mfol0
  { mfolPredicate = mtfolP
  , mfolState = mtfolQ
  , mfolAnd = foldMap mtfolT
  , mfolOr = foldMap mtfolT
  }

{-# INLINE appMTFol #-}
appMTFol :: Monoid m => MTFol p q t m -> Term p q t -> m
appMTFol = appMFol . fromMTFol

-- MTra --------------------------------------------------------------------------------

data MTra p q t p' q' t' f = MTra
  { mtraLTrue :: forall p' q' t'. f (Term p' q' t')
  , mtraPredicate :: forall q' t'. p -> f (Term p' q' t')
  , mtraState :: forall p' t'. q -> f (Term p' q' t')
  , mtraAnd :: forall p' q'. NonEmpty t -> f (Term p' q' t')
  , mtraOr :: forall p' q'. NonEmpty t -> f (Term p' q' t')
  }

{-# INLINE mtra0 #-}
mtra0 :: Applicative f => MTra p q t p q t f
mtra0 = MTra
  { mtraLTrue = pure LTrue
  , mtraPredicate = pure . Predicate
  , mtraState = pure . State
  , mtraAnd = pure . And
  , mtraOr = pure . Or
  }

{-# INLINE appMTra #-}
appMTra :: MTra p q t p' q' t' f -> Term p q t -> f (Term p' q' t')
appMTra MTra{mtraLTrue, mtraPredicate, mtraState, mtraAnd, mtraOr} = \case
  LTrue -> mtraLTrue
  Predicate p -> mtraPredicate p
  State q -> mtraState q
  And ts -> mtraAnd ts
  Or ts -> mtraOr ts

data MTTra p q t p' q' t' f = MTTra
  { mttraP :: p -> f p'
  , mttraQ :: q -> f q'
  , mttraT :: t -> f t'
  }

{-# INLINE mttra0 #-}
mttra0 :: forall f p q t p' q' t'. Applicative f => MTTra p q t p q t f
mttra0 = MTTra pure pure pure

{-# INLINE fromMTTra #-}
fromMTTra :: Applicative f => MTTra p q t p' q' t' f -> MTra p q t p' q' t' f
fromMTTra MTTra{mttraP, mttraQ, mttraT} = mtra0
  { mtraPredicate = fmap Predicate . mttraP
  , mtraState = fmap State . mttraQ
  , mtraAnd = fmap And . traverse mttraT
  , mtraOr = fmap Or . traverse mttraT
  }

{-# INLINE appMTTra #-}
appMTTra :: forall f p q t p' q' t'. Applicative f
  => MTTra p q t p' q' t' f -> Term p q t -> f (Term p' q' t')
appMTTra = appMTra . fromMTTra
