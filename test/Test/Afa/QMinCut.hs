module Test.Afa.QMinCut where

import Test.HUnit hiding (State)

import Data.Array

import Afa.Lib
import Afa.Ops.QMinCut

tests =
  [ "Afa.QMinCut" ~: do
      putStrLn ""
      print$ minCut dag0 [7, 8, 9]
      print$ minCut dag1 [7, 8, 9]
      print$ minCut dag2 [7, 8, 9]
      print$ minCut dag3 [10, 11, 9]
  ]

dag0 :: Array Int (Maybe ([Int], [Int]))
dag0 = listArray'$ reverse
  [ {- 9 -} Just ([], [6, 4])
  , {- 8 -} Just ([], [5, 6])
  , {- 7 -} Just ([], [5])
  , {- 6 -} Just ([8, 9], [4])
  , {- 5 -} Just ([7, 8], [3])
  , {- 4 -} Just ([6, 9], [1, 2])
  , {- 3 -} Just ([5], [0, 1])
  , {- 2 -} Nothing
  , {- 1 -} Nothing
  , {- 0 -} Nothing
  ]

dag1 :: Array Int (Maybe ([Int], [Int]))
dag1 = listArray'$ reverse
  [ {- 9 -} Just ([], [6, 4])
  , {- 8 -} Just ([], [5, 6])
  , {- 7 -} Just ([], [5])
  , {- 6 -} Just ([8, 9], [4])
  , {- 5 -} Just ([7, 8], [3, 4])
  , {- 4 -} Just ([6, 9, 5], [1, 2])
  , {- 3 -} Just ([5], [0, 1])
  , {- 2 -} Nothing
  , {- 1 -} Nothing
  , {- 0 -} Nothing
  ]

dag2 :: Array Int (Maybe ([Int], [Int]))
dag2 = listArray'$ reverse
  [ {- 9 -} Just ([], [6, 4])
  , {- 8 -} Just ([], [5, 6])
  , {- 7 -} Just ([], [5])
  , {- 6 -} Just ([8, 9], [4, 1])
  , {- 5 -} Just ([7, 8], [3, 4])
  , {- 4 -} Just ([6, 9, 5], [1, 2])
  , {- 3 -} Just ([5], [0, 1])
  , {- 2 -} Nothing
  , {- 1 -} Nothing
  , {- 0 -} Nothing
  ]

dag3 :: Array Int (Maybe ([Int], [Int]))
dag3 = listArray'$ reverse
  [ {- 11 -} Just ([], [8])
  , {- 10 -} Just ([], [7])
  , {-  9 -} Just ([], [6, 4])
  , {-  8 -} Just ([11], [5, 6])
  , {-  7 -} Just ([10], [5])
  , {-  6 -} Just ([8, 9], [4])
  , {-  5 -} Just ([7, 8], [3])
  , {-  4 -} Just ([6, 9], [1, 2])
  , {-  3 -} Just ([5], [0, 1])
  , {-  2 -} Nothing
  , {-  1 -} Nothing
  , {-  0 -} Nothing
  ]
