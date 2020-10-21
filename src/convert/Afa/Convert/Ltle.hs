{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}

module Afa.Convert.Ltle where

import Control.Monad.ST
import Control.Monad.State
import Control.Monad.Identity
import Control.Monad.Writer
import Data.Array
import Data.Array.MArray (readArray)
import Data.Bifunctor (second)
import Data.List (sort, group)
import Data.Monoid
import Data.Functor.Foldable
import Data.Functor.Foldable.Utils (algMToAlg)
import Data.Functor.Foldable.Coco (consu)
import Data.Functor.Foldable.Dag.Consing (hashCons', runHashConsMonadT)
import Data.Functor.Foldable.Dag.Monadic (cataScanM)

import Ltl (Ltl, deRelease_alg, pushNeg_cocoalg)
import qualified Ltl
import Afa
import Afa.Term.TreeF
  ( Term, pattern And, pattern Or, pattern Not, pattern State, pattern Var
  , pattern LTrue , pattern LFalse
  )


newtype StateAdderT m a = StateAdderT (StateT Int (WriterT (Endo [Term]) m) a)
  deriving (Functor, Applicative, Monad)
instance MonadTrans StateAdderT where
  lift = StateAdderT . lift . lift
runStateAdderT (StateAdderT action) =
  fmap (second (`appEndo` []))$ runWriterT$ runStateT action 1

peekNextState :: Monad m => StateAdderT m Int
peekNextState = StateAdderT get

addState :: Monad m => Term -> StateAdderT m Int
addState q = StateAdderT$ do
  stateCnt <- get
  put$ succ stateCnt
  lift$ tell$ Endo (q:)
  return stateCnt

prehash :: Ltl Int -> Ltl Int
prehash (Ltl.And xs) = Ltl.And$ map head$ group$ sort xs
prehash (Ltl.Or xs) = Ltl.And$ map head$ group$ sort xs

toArr :: [a] -> Array Int a
toArr list = listArray (0, length list - 1) list

ltleToAfa :: Fix Ltl -> (Int, Afa)
ltleToAfa ltl = (maximum (cata Ltl.allVars_alg ltl) + 2,)$ Afa
  { terms = listArray (0, stateCnt - 1)$ initTerm:terms
  , states = listArray (0, stateCnt - 1) [0..]
  }
  where
    ltl' = consu pushNeg_cocoalg deRelease_alg (True, ltl) :: Fix Ltl

    (ltlNodeCount, toArr -> ltlDag) = runIdentity$ runHashConsMonadT$
      cata (algMToAlg$ hashCons' . prehash) ltl'

    ((initTerm, stateCnt), terms) = runST$ runStateAdderT$ do
      arr <- cataScanM mixedAlg ltlDag
      lift$ readArray arr (ltlNodeCount - 1)


mixedAlg :: Monad m => Ltl Term -> StateAdderT m Term
mixedAlg Ltl.LTrue = return LTrue
mixedAlg Ltl.LFalse = return LFalse
mixedAlg (Ltl.Var i) = return$ Var$ i + 1
mixedAlg (Ltl.Not afa) = return$ Not afa
mixedAlg (Ltl.And afas) = return$ And afas
mixedAlg (Ltl.Or afas) = return$ Or afas

mixedAlg (Ltl.Next afa) = do
  q <- addState afa
  return$ And [State q, Not$ Var 0]

mixedAlg (Ltl.Until predicate end) = do
  q <- peekNextState
  let result = Or [end, And [predicate, Not$ Var 0, State q]]
  addState result
  return result

mixedAlg (Ltl.WeakUntil predicate end) = do
  q1 <- peekNextState
  let q2 = succ q1
  let globx = And [predicate, Not$ Var 0, State q2]
  let result = Or [globx, And [predicate, Not$ Var 0, State q1]]
  addState result -- q1
  addState$ Or [Var 0, globx] -- q2
  return result

mixedAlg (Ltl.Globally afa) = do
  q <- peekNextState
  let result = And [afa, Or [Var 0, State q]]
  addState result
  return result

mixedAlg (Ltl.Finally afa) = do
  q <- peekNextState
  let result = Or [afa, And [Not$ Var 0, State q]]
  addState result
  return result

mixedAlg _release = error "Release not supported here! Use deRelease_alg before."
