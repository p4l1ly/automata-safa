module Test.Afa.QMinCut where

import Test.HUnit hiding (State)

import Data.Array

import Afa.Lib
import Afa.Ops.QMinCut

tests =
  [ "Afa.QMinCut" ~: do
      putStrLn ""
      print$ minCut dag0 [7, 8, 9]
      -- print$ minCut dag1 [7, 8, 9]
      -- print$ minCut dag2 [7, 8, 9]
      -- print$ minCut dag3 [10, 11, 9]
  ]

dag0 :: Array Int [Int]
dag0 = listArray'$ reverse
  [ {- 9 -} [6, 4]
  , {- 8 -} [5, 6]
  , {- 7 -} [5]
  , {- 6 -} [4]
  , {- 5 -} [3]
  , {- 4 -} [1, 2]
  , {- 3 -} [0, 1]
  , {- 2 -} []
  , {- 1 -} []
  , {- 0 -} []
  ]

dag1 :: Array Int [Int]
dag1 = listArray'$ reverse
  [ {- 9 -} [6, 4]
  , {- 8 -} [5, 6]
  , {- 7 -} [5]
  , {- 6 -} [4]
  , {- 5 -} [3, 4]
  , {- 4 -} [1, 2]
  , {- 3 -} [0, 1]
  , {- 2 -} []
  , {- 1 -} []
  , {- 0 -} []
  ]

dag2 :: Array Int [Int]
dag2 = listArray'$ reverse
  [ {- 9 -} [6, 4]
  , {- 8 -} [5, 6]
  , {- 7 -} [5]
  , {- 6 -} [4, 1]
  , {- 5 -} [3, 4]
  , {- 4 -} [1, 2]
  , {- 3 -} [0, 1]
  , {- 2 -} []
  , {- 1 -} []
  , {- 0 -} []
  ]

dag3 :: Array Int [Int]
dag3 = listArray'$ reverse
  [ {- 11 -} [8]
  , {- 10 -} [7]
  , {-  9 -} [6, 4]
  , {-  8 -} [5, 6]
  , {-  7 -} [5]
  , {-  6 -} [4]
  , {-  5 -} [3]
  , {-  4 -} [1, 2]
  , {-  3 -} [0, 1]
  , {-  2 -} []
  , {-  1 -} []
  , {-  0 -} []
  ]
