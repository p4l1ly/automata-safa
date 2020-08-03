module Main (main) where

import Control.Monad

import Test.HUnit

import qualified Test.Afa.Simplify
import qualified Test.Tree.Simplify
import qualified Test.Tree.StatePositiveness

check result = do
  guard$ failures result == 0
  guard$ errors result == 0

main = (check =<<)$ runTestTT$ TestList$ concat
  [ Test.Tree.Simplify.tests
  , Test.Tree.StatePositiveness.tests
  , Test.Afa.Simplify.tests
  ]
