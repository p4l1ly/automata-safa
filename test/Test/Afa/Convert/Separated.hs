{-# LANGUAGE PatternSynonyms #-}
module Test.Afa.Convert.Separated where

import Test.HUnit hiding (State)

import Control.Monad.Identity
import Data.Array

import qualified Afa.Term.Fix as Fix
import qualified Afa.Term
import qualified Afa.Convert.Separated
import Data.Functor.Foldable
import Data.Functor.Foldable.Utils (algMToAlg)
import Data.Functor.Tree (pattern Leaf, pattern Node)

import Afa
import Afa.Term.TreeF
import Afa.Ops.Preprocess (toArr)

import Afa.Convert.Separated
  ( SeparatedFormula(..), QTerm(..), ATerm(..), DisjunctItem(..), SeparatedAfa(..)
  , separate
  )

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
            [ Node$ QState 0
            , Node$ QState 1
            , Node$ QAnd [Node$ QState 0, Node$ QState 1]
            ]
        , aterms = toArr
            [ Node$ AVar 1
            , Node$ AVar 0
            , Node$ AAnd [Node$ AVar 1, Node$ AVar 0]
            , Node$ AAnd [Node$ AVar 1, Leaf 2]
            ]
        , Afa.Convert.Separated.states = toArr
            [ [(-1,0), (0,-1)]
            , [(1,0), (1,3), (2,0), (2,1), (2,2)]
            ]
        }
      assertEqual "afa1" (separate afa1)$ SeparatedAfa
        { qterms = toArr [Node$ QState 1]
        , aterms = toArr
            [ Node$ AVar 0
            , Node$ AAnd [Node$ ANot$ Node$ AVar 0, Node$ AVar 1]
            , Node$ AAnd [Leaf 1, Node$ ANot$ Node$ AVar 1]
            ]
        , Afa.Convert.Separated.states = toArr
            [ [(0, 2)]
            , [(-1, 0), (0, 1)]
            ]
        }
  ]

formula1 :: Fix Afa.Term.Term
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

separatedFormula1 = runIdentity$ cata (algMToAlg alg) formula1
  where alg = Afa.Convert.Separated.alg Disjunct (return . embed) (return . embed)

(a0@a:a1@b:_) = map Var [0..]
(q0:q1:_) = map State [0..]

afa0 :: Afa
afa0 = Afa
  { terms = listArray (0, 1)
      [ {- t0 -} Or [q0, b]
      , {- t1 -} And [q1, Leaf 0, Or [And [a, Leaf 0], And [b, Leaf 0]]]
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
      , {- t1 -} Or [a0, Leaf 0]
      , {- t2 -} And [Not a1, Leaf 0]
      ]
  , Afa.states = listArray (0, 1) [2, 1]
  }
