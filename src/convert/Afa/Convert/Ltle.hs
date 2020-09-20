{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}

module Afa.Convert.Ltle where

import Control.Monad.State
import Control.Monad.Writer
import Data.Array
import Data.Monoid

import Ltl (Ltl)
import qualified Ltl
import Data.Functor.Foldable
import Afa
import Afa.TreeDag.Patterns.Builder
  ( Term, pattern And, pattern Or, pattern Not, pattern State, pattern Var
  , pattern LTrue , pattern LFalse
  )
import Data.Functor.Foldable.Dag.Monadic (fromCataScanMAlg)


type MyMonad = StateT Int (Writer (Endo [Term]))


ltleToAfa :: Fix Ltl -> (Int, Afa)
ltleToAfa ltl = (maximum (cata Ltl.allVars_alg ltl) + 2,)$ Afa
  { terms = listArray (0, stateCnt - 1)$ initTerm:terms
  , states = listArray (0, stateCnt - 1) [0..]
  }
  where
    ((initTerm, stateCnt),  (`appEndo` []) -> terms) =
      runWriter$ runStateT (cata (fromCataScanMAlg ltleToAfa_alg) ltl) 1


ltleToAfa_alg :: Ltl Term -> MyMonad Term
ltleToAfa_alg Ltl.LTrue = return LTrue
ltleToAfa_alg Ltl.LFalse = return LFalse
ltleToAfa_alg (Ltl.Var i) = return$ Var$ i + 1
ltleToAfa_alg (Ltl.Not afa) = return$ Not afa
ltleToAfa_alg (Ltl.And afas) = return$ And afas
ltleToAfa_alg (Ltl.Or afas) = return$ Or afas

ltleToAfa_alg (Ltl.Next afa) = do
  q <- addState afa
  return$ And [State q, Not$ Var 0]

ltleToAfa_alg (Ltl.Until predicate end) = do
  q <- get
  let result = Or [end, And [predicate, Not$ Var 0, State q]]
  addState result
  return result

ltleToAfa_alg (Ltl.WeakUntil predicate end) = do
  q1 <- get
  let q2 = succ q1
  let globx = And [predicate, Not$ Var 0, State q2]
  let result = Or [globx, And [predicate, Not$ Var 0, State q1]]
  addState result -- q1
  addState$ Or [Var 0, globx] -- q2
  return result

ltleToAfa_alg (Ltl.Globally afa) = do
  q <- get
  let result = And [afa, Not$ Var 0, State q]
  addState$ Or [Var 0, result]
  return result

ltleToAfa_alg (Ltl.Finally afa) = do
  q <- get
  let result = Or [afa, And [Not$ Var 0, State q]]
  addState result
  return result

ltleToAfa_alg _release = error "Release not supported here! Use deRelease_alg before."


addState :: Term -> MyMonad Int
addState q = do
  stateCnt <- get
  put$ succ stateCnt
  lift$ tell$ Endo (q:)
  return stateCnt
