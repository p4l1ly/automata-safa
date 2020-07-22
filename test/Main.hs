module Main (main) where

import Control.Monad

import Test.HUnit

import qualified Tree.Simplify
import qualified Tree.StatePositiveness

check result = do
  guard$ failures result == 0
  guard$ errors result == 0

main = (check =<<)$ runTestTT$ TestList$ concat
  [ Tree.Simplify.tests
  , Tree.StatePositiveness.tests
  , []
  ]
