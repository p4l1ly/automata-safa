{-# LANGUAGE TupleSections #-}

module Test.Afa.Simplify where

import Test.HUnit hiding (State)

import Data.Array
import Data.Monoid
import Data.Functor

import Data.List.NonEmpty (NonEmpty(..))

import Afa
import Afa.Lib
import Afa.Bool
import qualified Afa.Term.Bool as BoolT
import qualified Afa.Term.Mix as MixT

tests =
  [ "Afa.Simplify" ~: do
      let simpAfa = simplifyAll afa0 <&> \simpAfa ->
            simpAfa{ afa = reorderStates$ afa simpAfa }
      assertEqual "afa0" simpAfa$ Right BoolAfa
        { boolTerms = listArray' [a]
        , afa = Afa
            { terms = listArray' [MixT.Predicate 0, MixT.State 1]
            , states = listArray' [1, 0]
            , initState = 0
            }
        }
  ]


(a:b:_) = map BoolT.Predicate [0..]

afa0 :: BoolAfaUnswallowed Int
afa0 = BoolAfa
  { boolTerms = listArray'$ reverse
      [ {- 7 -} BoolT.Or$ 6 :| [1, 0]
      , {- 6 -} BoolT.Not 5
      , {- 5 -} BoolT.Not 4
      , {- 4 -} BoolT.Not 1
      , {- 3 -} BoolT.Or$ 2 :| [0]
      , {- 2 -} a
      , {- 1 -} a
      , {- 0 -} b
      ]
  , afa = Afa
      { terms = listArray'$ reverse
          [ {- 13 -} MixT.Predicate 7
          , {- 12 -} MixT.Predicate 0
          , {- 11 -} MixT.And$ 10 :| [4]  -- blind
          , {- 10 -} MixT.State 0  -- blind
          , {-  9 -} MixT.And$ 8 :| [7]
          , {-  8 -} MixT.And$ 7 :| [6]
          , {-  7 -} MixT.And$ 3 :| [5]
          , {-  6 -} MixT.State 2
          , {-  5 -} MixT.State 1
          , {-  4 -} MixT.And$ 1 :| [2]
          , {-  3 -} MixT.State 4
          , {-  2 -} MixT.Predicate 3
          , {-  1 -} MixT.Predicate 2
          , {-  0 -} MixT.Predicate 1
          ]
      , states = listArray'$ reverse
          [ {- 4 -} 13
          , {- 3 -} 12
          , {- 2 -} 0
          , {- 1 -} 4
          , {- 0 -} 9
          ]
      , initState = 0
      }
  }
