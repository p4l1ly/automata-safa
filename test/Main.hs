module Main (main) where

import Control.Monad

import Test.HUnit

import qualified Test.Afa.Simplify
import qualified Test.Afa.Convert.Separated

check result = do
  guard$ failures result == 0
  guard$ errors result == 0

main = (check =<<)$ runTestTT$ TestList$ concat
  [ Test.Afa.Simplify.tests
  , Test.Afa.Convert.Separated.tests
  , []
  ]
