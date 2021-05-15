{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleInstances #-}

module Afa.Convert.Ltle where

import Data.Array
import Data.Array.ST
import Control.Monad.Trans
import Control.Monad.State.Strict
import Control.Monad.Writer.Strict
import Control.Monad.ST
import Control.Lens
import Data.Fix
import Control.Monad.Free
import Afa
import qualified Afa.Term.Mix as MTerm
import qualified Afa.Term.Bool as BTerm
import Afa.Lib (listArray')
import Afa.Lib.LiftArray
import Afa.Bool
import Control.RecursionSchemes.Lens
import Control.RecursionSchemes.Utils.NoCons
import Control.RecursionSchemes.Utils.HashCons
import Data.List.NonEmpty (NonEmpty(..))

import Ltl (Ltl, preprocessCoRecursive, canonicalize)
import qualified Ltl


newtype BuilderT m a = BuilderT
  { fromBuilderT ::
      StateT Int
        ( WriterT (Endo [Int])
            ( NoConsT (MTerm.Term Int Int Int)
                (NoConsT (BTerm.Term Int Int) m)
            )
        )
        a
  }
  deriving (Functor, Applicative, Monad)

runBuilderT (BuilderT action) =
  runNoConsT$ runNoConsT$ do
    (a, w) <- runWriterT$ evalStateT action 0
    return (a, w `appEndo` [])

instance MonadTrans BuilderT where
  lift = BuilderT . lift . lift . lift . lift

addBTerm0 :: Monad m => BTerm.Term Int Int -> BuilderT m Int
addBTerm0 = BuilderT . lift . lift . lift . nocons

addBTerm :: Monad m => BTerm.Term Int Int -> BuilderT m (Int, Bool)
addBTerm = fmap (, False) . addBTerm0

addMTerm0 :: Monad m => MTerm.Term Int Int Int -> BuilderT m Int
addMTerm0 = BuilderT . lift . lift . nocons

addMTerm :: Monad m => MTerm.Term Int Int Int -> BuilderT m (Int, Bool)
addMTerm = fmap (, True) . addMTerm0

instance Monad m => AfaBuilder (BuilderT m) (Int, Bool) where
  addTerm = iterM$ sequence >=> \case
    LTrue -> addBTerm BTerm.LTrue
    LFalse -> addBTerm BTerm.LFalse
    Var i -> addBTerm$ BTerm.Predicate i
    Not (i, False) -> addBTerm$ BTerm.Not i
    Not _ -> error "stateful not"
    And [] -> addBTerm BTerm.LTrue
    Or [] -> addBTerm BTerm.LFalse
    And xs@(unzip -> (t:ts, statefuls))
      | not$ or statefuls -> addBTerm$ BTerm.And$ t :| ts
      | otherwise -> do
          ts' <- forM xs$ \case
            (t, True) -> return t
            (t, _) -> addMTerm0$ MTerm.Predicate t
          let t2:ts2 = ts'
          addMTerm$ MTerm.And$ t2 :| ts2
    Or xs@(unzip -> (t:ts, statefuls))
      | not$ or statefuls -> addBTerm$ BTerm.Or$ t :| ts
      | otherwise -> do
          ts' <- forM xs$ \case
            (t, True) -> return t
            (t, _) -> addMTerm0$ MTerm.Predicate t
          let t2:ts2 = ts'
          addMTerm$ MTerm.Or$ t2 :| ts2

  withNewState fn = BuilderT$ do
    nextIx <- get
    mref <- fromBuilderT$ addMTerm0$ MTerm.State nextIx
    let BuilderT (StateT action) = fn (mref, True)
        WriterT getATSW = action (nextIx + 1)
    (((a, t), nextIx'), w) <- lift$ lift getATSW
    (ref, b) <- fromBuilderT$ addTerm t
    ref' <- if b then return ref else fromBuilderT$ addMTerm0$ MTerm.Predicate ref
    lift$ tell$ Endo (ref':)
    put nextIx'
    lift$ tell w
    return a


ltleToUnswallowedAfa :: Fix Ltl -> BoolAfaUnswallowed Int
ltleToUnswallowedAfa ltl = BoolAfa
  { boolTerms = listArray' bterms
  , afa = Afa
    { terms = listArray' mterms'
    , states = listArray' states'
    , initState = init'
    }
  }
  where
  (mterms', states', init') = case ixMap!rootIx of
    (ref, True) -> case mterms!!ref of
      MTerm.State q -> (mterms, states, q)
      _ -> (mterms, states ++ [ref], length states)
    (ref, _) ->
      ( mterms ++ [MTerm.Predicate ref]
      , states ++ [length mterms]
      , length states
      )

  (((ixMap, states), mterms), bterms) = runST$ runBuilderT action

  action :: forall s. BuilderT (ST s) (Array Int (Int, Bool))
  action = cataScanT' @(LiftArray (STArray s)) traversed (toAfa >=> addTerm) consedLtl

  ltl' = preprocessCoRecursive ltl
  (rootIx, listArray' -> consedLtl) = runIdentity$ runHashConsT$
    cataT recursiveTraversal (hashCons' . canonicalize) ltl'


data Term t
  = LTrue
  | LFalse
  | Var Int
  | Not t
  | And [t]
  | Or [t]
  deriving (Functor, Foldable, Traversable)

pattern LTrueF = Free LTrue
pattern LFalseF = Free LFalse
pattern VarF i = Free (Var i)
pattern NotF t = Free (Not t)
pattern AndF ts = Free (And ts)
pattern OrF ts = Free (Or ts)

class Monad m => AfaBuilder m t where
  addTerm :: Free Term t -> m t
  withNewState :: (t -> m (a, Free Term t)) -> m a

  addState :: Free Term t -> m t
  addState t = withNewState$ \q -> return (q, t)

toAfa :: AfaBuilder m t => Ltl t -> m (Free Term t)
toAfa Ltl.LTrue = return LTrueF
toAfa Ltl.LFalse = return LFalseF
toAfa (Ltl.Var i) = return$ VarF$ i + 1
toAfa (Ltl.Not afa) = return$ NotF$ Pure afa
toAfa (Ltl.And afas) = return$ AndF$ fmap Pure afas
toAfa (Ltl.Or afas) = return$ OrF$ fmap Pure afas
toAfa (Ltl.Next afa) = do
  q <- addState$ Pure afa
  return$ AndF [Pure q, NotF$ VarF 0]
toAfa (Ltl.Until predicate end) = do
  withNewState$ \q -> do
    return (Pure q, OrF [Pure end, AndF [Pure predicate, NotF$ VarF 0, Pure q]])
toAfa (Ltl.WeakUntil predicate end) =
  withNewState$ \q1 -> do
    result <- withNewState$ \q2 -> do
      predicate' <- addTerm$ AndF [Pure predicate, NotF$ VarF 0]
      globx <- addTerm$ AndF [Pure predicate', Pure q2]
      result <- addTerm$ OrF [Pure globx, Pure end, AndF [Pure predicate', Pure q1]]
      return (Pure result, OrF [VarF 0, Pure globx])
    return (result, result)
toAfa (Ltl.Globally afa) =
  withNewState$ \q -> do
    (Pure -> result) <- addTerm$ AndF [Pure afa, OrF [VarF 0, Pure q]]
    return (result, result)
toAfa (Ltl.Finally afa) =
  withNewState$ \q -> do
    (Pure -> result) <- addTerm$ OrF [Pure afa, AndF [NotF$ VarF 0, Pure q]]
    return (result, result)
toAfa _release = error "Release not supported here! Use deRelease before."
