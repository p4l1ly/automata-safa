{-# LANGUAGE PatternSynonyms #-}
module Test.Afa.Convert.Separated where

import Control.Monad.Identity
import Test.HUnit hiding (State)
import qualified Afa.Functor.Fix as Fix
import qualified Afa.Functor
import qualified Afa.Convert.Separated
import Afa
import Data.Array
import Afa.TreeDag.Patterns.Builder hiding (Ref, NRef)
import Data.Functor.Foldable.Dag.TreeHybrid (pattern Ref, pattern NRef)

import Afa.Convert.Separated
  ( SeparatedFormula(..), QTerm(..), ATerm(..), DisjunctItem(..), SeparatedAfa(..)
  , separate
  )
import Data.Functor.Foldable
import Data.Functor.Foldable.Dag.Monadic (fromCataScanMAlg)

tests =
  [ "separate" ~: do
      assertEqual "formula1" separatedFormula1$ Disjunct
        [ QItem (Fix (QState 0))
        , AItem (Fix (AVar 0))
        , Conjunct
            (Fix (QAnd [Fix (QState 2), Fix (QState 3)]))
            (Fix (AAnd [Fix (AVar 1), Fix (AVar 2)]))
        , Conjunct
            (Fix (QAnd [Fix (QState 2), Fix (QAnd [Fix (QState 4), Fix (QState 5)])]))
            (Fix (AVar 3))
        ]
      assertEqual "afa0" (separate afa0)$ SeparatedAfa
        { qterms = toArr
            [ NRef$ QState 0
            , NRef$ QState 1
            , NRef$ QAnd [NRef$ QState 0, NRef$ QState 1]
            ]
        , aterms = toArr
            [ NRef$ AVar 1
            , NRef$ AVar 0
            , NRef$ AAnd [NRef$ AVar 1, NRef$ AVar 0]
            , NRef$ AAnd [NRef$ AVar 1, Ref 2]
            ]
        , Afa.Convert.Separated.states = toArr
            [ [(-1,0), (0,-1)]
            , [(1,0), (1,3), (2,0), (2,1), (2,2)]
            ]
        }
      assertEqual "afa1" (separate afa1)$ SeparatedAfa
        { qterms = toArr [NRef$ QState 1]
        , aterms = toArr
            [ NRef$ AVar 0
            , NRef$ AAnd [NRef$ ANot$ NRef$ AVar 0, NRef$ AVar 1]
            , NRef$ AAnd [Ref 1, NRef$ ANot$ NRef$ AVar 1]
            ]
        , Afa.Convert.Separated.states = toArr
            [ [(0, 2)]
            , [(-1, 0), (0, 1)]
            ]
        }
  ]

formula1 :: Fix Afa.Functor.Term
formula1 = Fix.Or
  [ Fix.State 0
  , Fix.Var 0
  , Fix.And
    [ Fix.Or [Fix.LTrue, Fix.State 1]
    , Fix.State 2
    , Fix.Or
        [ Fix.And [Fix.State 3, Fix.Var 1, Fix.Var 2]
        , Fix.And [Fix.State 4, Fix.State 5, Fix.Var 3]
        ]
    ]
  ]

separatedFormula1 = runIdentity$ cata (fromCataScanMAlg alg) formula1
  where alg = Afa.Convert.Separated.alg Disjunct (return . embed) (return . embed)

(a0@a:a1@b:_) = map Var [0..]
(q0:q1:_) = map State [0..]

afa0 :: Afa
afa0 = Afa
  { terms = listArray (0, 1)
      [ {- t0 -} Or [q0, b]
      , {- t1 -} And [q1, Ref 0, Or [And [a, Ref 0], And [b, Ref 0]]]
      ]
  , Afa.states = listArray (0, 1)
      [ {- q0 -} 0
      , {- q1 -} 1
      ]
  }


afa1 :: Afa
afa1 = Afa
  { terms = listArray (0, 2)
      [ {- t0 -} And [Not a0, q1, a1]
      , {- t1 -} Or [a0, Ref 0]
      , {- t2 -} And [Not a1, Ref 0]
      ]
  , Afa.states = listArray (0, 1) [2, 1]
  }
