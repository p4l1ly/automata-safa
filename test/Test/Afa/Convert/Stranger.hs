{-# LANGUAGE PatternSynonyms #-}

module Test.Afa.Convert.Stranger where

import Test.HUnit hiding (State)
import Data.Fix

import Afa.Convert.Stranger


pattern FLTrue = Fix LTrue
pattern FLFalse = Fix LFalse
pattern FState i = Fix (State i)
pattern FVar x = Fix (Var x)
pattern FNot x = Fix (Not x)
pattern FAnd a b = Fix (And a b)
pattern FOr a b = Fix (Or a b)

tests =
  [ "Convert.Stranger" ~: do
      assertEqual "term"
        ( Right$
          FAnd (FAnd (FState 1) (FNot$ FVar "e_0")) (FOr (FVar "a_0") (FVar "a_1"))
        )
        $ runWParser expr "(s_1 ∧ ¬e_0 ∧ (a_0 ∨ a_1))"
  ]
