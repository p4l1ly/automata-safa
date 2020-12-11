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
import Control.Monad.State
import Control.Monad.Writer.Lazy
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
import Data.List.NonEmpty (NonEmpty(..))

import Ltl (Ltl, preprocessCoRecursive, canonicalize)
import qualified Ltl


newtype UnswallowedAfaBuilderT m a = UnswallowedAfaBuilderT
  { fromUnswallowedAfaBuilderT ::
      NoConsT Int
        ( HashConsT' (MTerm.Term Int Int Int)
            (HashConsT' (BTerm.Term Int Int) m)
        )
        a
  }
  deriving (Functor, Applicative, Monad)

runUnswallowedAfaBuilderT (UnswallowedAfaBuilderT action) =
  runHashConsT$ runHashConsT$ runNoConsT action

instance MonadTrans UnswallowedAfaBuilderT where
  lift = UnswallowedAfaBuilderT . lift . lift . lift

addBTerm :: Monad m => BTerm.Term Int Int -> UnswallowedAfaBuilderT m (Int, Bool)
addBTerm t = UnswallowedAfaBuilderT$ fmap (, False)$ lift$ lift$ hashCons' t

addMTerm :: Monad m => MTerm.Term Int Int Int -> UnswallowedAfaBuilderT m (Int, Bool)
addMTerm t = UnswallowedAfaBuilderT$ fmap (, True)$ lift$ hashCons' t

instance Monad m => AfaBuilder (UnswallowedAfaBuilderT m) (Int, Bool) where
  addTerm = iterM$ sequence >=> \case
    LTrue -> addBTerm BTerm.LTrue
    LFalse -> addBTerm BTerm.LFalse
    Var i -> addBTerm$ BTerm.Predicate i
    Not (i, False) -> addBTerm$ BTerm.Not i
    Not _ -> error "stateful not"
    And [] -> addBTerm BTerm.LTrue
    Or [] -> addBTerm BTerm.LFalse
    And (unzip -> (t:ts, statefuls))
      | or statefuls -> addMTerm$ MTerm.And$ t :| ts
      | otherwise -> addBTerm$ BTerm.And$ t :| ts
    Or (unzip -> (t:ts, statefuls))
      | or statefuls -> addMTerm$ MTerm.Or$ t :| ts
      | otherwise -> addBTerm$ BTerm.Or$ t :| ts

  withNewState fn = UnswallowedAfaBuilderT$ do
    nextIx <- NoConsT get
    mref <- lift$ hashCons'$ MTerm.State nextIx
    let UnswallowedAfaBuilderT (NoConsT (StateT action)) = fn (mref, True)
        WriterT getATSW = action (nextIx + 1)
    (((a, t), nextIx'), w) <- lift getATSW
    (ref, b) <- fromUnswallowedAfaBuilderT$ addTerm t
    ref' <- if b then return ref else lift$ hashCons'$ MTerm.Predicate ref
    nocons ref'
    NoConsT$ put nextIx'
    NoConsT$ lift$ tell w
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

  (((ixMap, states), mterms), bterms) = runST$ runUnswallowedAfaBuilderT action

  action :: forall s. UnswallowedAfaBuilderT (ST s) (Array Int (Int, Bool))
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
toAfa Ltl.LFalse = return LTrueF
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
