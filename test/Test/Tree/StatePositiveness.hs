{-# LANGUAGE LambdaCase #-}

module Test.Tree.StatePositiveness (tests) where

import Test.HUnit hiding (State)
import Data.Functor.Foldable

import Afa.Term (Term)
import qualified Afa.Term as F
import Afa.Term.Fix hiding (Term)
import Afa.Term.Prism.Ops.StatePositiveness

tests =
  [ "check none" ~: do
      statesArePositive term_none @? "none is positive"
      statesCanBePositive term_none @? "none can be positive"
  , "check positive" ~: do
      statesArePositive term_positive @? "positive is positive" 
      statesCanBePositive term_positive @? "positive can be positive"
  , "check negative" ~: do
      not (statesArePositive term_negative) @? "negative is negative"
      not (statesCanBePositive term_negative) @? "negative cannot be positive"
      not (statesArePositive term_negative2) @? "negative2 is negative"
      not (statesCanBePositive term_negative2) @? "negative2 cannot be positive"
  , "check a term with states under even number of negations" ~: do
      not (statesArePositive term_evenNegative) @? "evenNegative is negative"
      statesCanBePositive term_evenNegative @? "evenNegative can be positive"
  , "test positivisation" ~: do
      assertEqual "evenNegative_positivised"
        (makeStatesPositive term_evenNegative)
        (Just term_evenNegative_positivised_expected)
      assertEqual "negative2_positivised" (makeStatesPositive term_negative2) Nothing
      assertEqual "negative2_positivised" (makeStatesPositive term_negative) Nothing
      assertEqual "positive_positivised"
        (makeStatesPositive term_positive) (Just$ deep_reverse term_positive)
      assertEqual "none_positivised"
        (makeStatesPositive term_none) (Just$ deep_reverse term_none)
  ]

s0 = State 0
s1 = State 1
a = Var 0
b = Var 1
c = Var 2
d = Var 3

term_none :: Fix Term
term_none = Not$ And [a, LFalse]

term_positive :: Fix Term
term_positive = And [a, s0]

term_negative :: Fix Term
term_negative = Not$ And [a, s0]

term_evenNegative :: Fix Term
term_evenNegative = Or [Not$ Or [And [Not$ And [a, s0], b, Not s1], c], d]

term_negative2 :: Fix Term
term_negative2 = Or [Not$ Or [And [Not$ And [a, s0], b, s1], c], d]

term_evenNegative_positivised_expected :: Fix Term
term_evenNegative_positivised_expected = deep_reverse$
  Or [And [Or [And [a, s0], Not b, s1], Not c], d]

deep_reverse :: Fix Term -> Fix Term
deep_reverse = cata$ \case
  F.And xs -> And$ reverse xs
  F.Or xs -> Or$ reverse xs
  x -> Fix x
