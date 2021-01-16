{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE OverloadedStrings #-}

module Test.Afa.Convert.Stranger where

import Test.HUnit hiding (State)
import Data.Fix

import Afa.Convert.Stranger


pattern FSTrue = Fix STrue
pattern FSFalse = Fix SFalse
pattern FSState i = Fix (SState i)
pattern FSVar x = Fix (SVar x)
pattern FSNot x = Fix (SNot x)
pattern FSAnd a b = Fix (SAnd a b)
pattern FSOr a b = Fix (SOr a b)

tests =
  [ "Convert.Stranger" ~: do
      assertEqual "term"
        ( FSAnd
            (FSAnd (FSState 1) (FSNot$ FSVar "e_0"))
            (FSOr (FSVar "a_0") (FSVar "a_1"))
        )
        $ parseExpr "(s_1 ∧ ¬e_0 ∧ (a_0 ∨ a_1))"

      putStrLn ""
      print$ parseAfa
        "numOfStates:   3\n\
        \initialStates: s_0\n\
        \finalStates:   ¬s_0 ∧ ¬s_1 ∧ (¬s_1 ∨ ¬s_2)\n\
        \States: \n\
        \state 0:\n\
        \s_1 ∧ e_0\n\
        \state 1:\n\
        \s_2 ∧ ¬e_0\n\
        \state 2:\n\
        \s_0 ∧ ¬e_0\n\
        \"
  ]
