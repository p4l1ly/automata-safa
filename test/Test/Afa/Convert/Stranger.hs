{-# LANGUAGE PatternSynonyms #-}

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
        ( Right$ FSAnd
            (FSAnd (FSState 1) (FSNot$ FSVar "e_0"))
            (FSOr (FSVar "a_0") (FSVar "a_1"))
        )
        $ runWParser expr "(s_1 ∧ ¬e_0 ∧ (a_0 ∨ a_1))"
  ]
