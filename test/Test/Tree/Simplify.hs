module Test.Tree.Simplify (tests) where

import Test.HUnit
import Data.Functor.Foldable

import Afa.Term (Term)
import Afa.Term.Fix hiding (Term)
import Afa.Term.Prism.Ops.Simplify

tests =
  [ "removeEmptyClauses" ~:
      "check term_1" ~: term_1 ~=? term_1_expected
  , "delit" ~:
      "check term_2" ~: term_2 ~=? term_2_expected
  , "removeUselessClauses" ~:
      "check term_3" ~: term_3 ~=? term_3_expected
  , "removeDoubleNegation" ~:
      "check term_4" ~: term_4 ~=? term_4_expected
  , "flatten" ~:
      "check term_5" ~: term_5 ~=? term_5_expected
  , "simplify" ~:
      "check term_5" ~: term_simplified ~=? term_5_expected
  ]

term :: Fix Term
term = And
  [ Var 0
  , Not$ Not$ And
      [ Or [LTrue, Var 0]
      , Or [Var 1]
      , Or [LFalse, Var 2]
      , And []
      ]
  ]

term_1 :: Fix Term
term_1 = cata removeEmptyClauses_alg term

term_1_expected :: Fix Term
term_1_expected = And
  [ Var 0
  , Not$ Not$ And
      [ Or [LTrue, Var 0]
      , Or [Var 1]
      , Or [LFalse, Var 2]
      , LTrue
      ]
  ]

term_2 :: Fix Term
term_2 = cata delit_alg term_1

term_2_expected :: Fix Term
term_2_expected = And
  [ Var 0
  , Not$ Not$ And
      [ Or [Var 1]
      , Or [Var 2]
      ]
  ]

term_3 :: Fix Term
term_3 = cata removeSingletonClauses_alg term_2

term_3_expected :: Fix Term
term_3_expected = And
  [ Var 0
  , Not$ Not$ And
      [ Var 1
      , Var 2
      ]
  ]

term_4 :: Fix Term
term_4 = cata removeDoubleNegation_alg term_3

term_4_expected :: Fix Term
term_4_expected = And
  [ Var 0
  , And
      [ Var 1
      , Var 2
      ]
  ]

term_5 :: Fix Term
term_5 = cata flatten_alg term_4

term_5_expected :: Fix Term
term_5_expected = And
  [ Var 0
  , Var 1
  , Var 2
  ]

term_simplified :: Fix Term
term_simplified = cata simplify_alg term
