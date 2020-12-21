module Test.Afa.QMinCut where

import Test.HUnit hiding (State)

import Data.Array
import Data.List

import Afa.Lib
import Afa.Lib.QMinCut

tests =
  [ "Afa.QMinCut" ~: do
      putStrLn ""
      assertEqual "dag0" [3, 4]$ sort$ minCut dag0 [7, 8, 9] [0, 1, 2]
      assertEqual "dag1" [3, 4]$ sort$ minCut dag1 [7, 8, 9] [0, 1, 2]
      assertEqual "dag2" [0, 1, 2]$ sort$ minCut dag2 [7, 8, 9] [0, 1, 2]
      assertEqual "dag3" [3, 4]$ sort$ minCut dag3 [10, 11, 9] [0, 1, 2]
      assertEqual "dag4" [5, 6, 7]$ sort$ minCut dag4 [8, 9, 10, 11] [0, 1, 2, 3]
      assertEqual "dag5" [0, 4]$ sort$ minCut dag5 [5, 6] [0, 1, 2]
      assertEqual "dag6" [0, 2, 4]$ sort$ minCut dag6 [6, 7, 8] [0, 1, 2, 3]
      assertEqual "dag7" [4, 9]$ sort$ minCut dag7 [8, 9] [0, 1, 2, 3]
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
  , {- 4 -} [2, 1]
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

dag4 :: Array Int [Int]
dag4 = listArray'$ reverse
  [ {- 11 -} [7]
  , {- 10 -} [5, 7]
  , {-  9 -} [5, 6]
  , {-  8 -} [6]
  , {-  7 -} [3, 4, 5]
  , {-  6 -} [0, 1]
  , {-  5 -} [1, 2]
  , {-  4 -} [2, 3]
  , {-  3 -} []
  , {-  2 -} []
  , {-  1 -} []
  , {-  0 -} []
  ]

dag5 :: Array Int [Int]
dag5 = listArray'$ reverse
  [ {-  6 -} [4]
  , {-  5 -} [0]
  , {-  4 -} [1, 2, 3]
  , {-  3 -} [0, 1]
  , {-  2 -} []
  , {-  1 -} []
  , {-  0 -} []
  ]

dag6 :: Array Int [Int]
dag6 = listArray'$ reverse
  [ {-  8 -} [4]
  , {-  7 -} [4, 5]
  , {-  6 -} [0, 2, 5]
  , {-  5 -} [0, 4]
  , {-  4 -} [1, 3]
  , {-  3 -} []
  , {-  2 -} []
  , {-  1 -} []
  , {-  0 -} []
  ]

dag7 :: Array Int [Int]
dag7 = listArray'$ reverse
  [ {-  9 -} [6, 7]
  , {-  8 -} [4]
  , {-  7 -} [5, 6]
  , {-  6 -} [0, 2, 5]
  , {-  5 -} [0, 4]
  , {-  4 -} [1, 3]
  , {-  3 -} []
  , {-  2 -} []
  , {-  1 -} []
  , {-  0 -} []
  ]
