module Test.Afa.Goblin where

import Test.HUnit hiding (State)

import Data.Maybe
import Data.Array
import Data.Functor
import Data.List.NonEmpty (NonEmpty(..))

import Afa
import Afa.Lib
import Afa.Term.Mix
import Afa.Ops.Goblin
import Afa.Ops.QMinCut

tests =
  [ "Afa.Goblin" ~: do
      -- let Right simpAfa1 = simplifyAll afa1 <&> reorderStates
      -- print simpAfa1
      -- let Just gobAfa1 = goblin simpAfa1
      -- print gobAfa1
      -- let Right simpAfa2 = simplifyAll gobAfa1 <&> reorderStates
      -- print simpAfa2
      -- -- assertEqual "afa0" simpAfa$ Right Afa
      -- --   { terms = listArray' [Predicate 0, State 1]
      -- --   , states = listArray' [1, 0]
      -- --   , initState = 0
      -- --   }
      -- print$ goblin afa2
      -- assertEqual "afa2 double goblin" Nothing$ goblin$ fromJust$ goblin afa2
      -- print$ goblin afa3

      -- print$ goblin afa4
      -- print$ goblin afa4 >>= goblin
      -- print$ goblin afa4 >>= goblin >>= goblin
      -- print$ goblin afa4 >>= goblin >>= goblin >>= goblin
      -- print$ goblin afa5

      putStrLn ""
      putStrLn "Goblin: afa6"
      print$ markBack afa6
      let afa6' = afa6{terms = markBack afa6}
      print$ goblin2 afa6'
      print$ goblin2 afa6' >>= goblin2

      putStrLn ""
      putStrLn "Goblin: afa7"
      print$ markBack afa7
      let afa7' = afa7{terms = markBack afa7}
      print$ goblin2 afa7'

      putStrLn ""
      putStrLn "Goblin: afa8"
      print$ markBack afa8
      let afa8' = afa8{terms = markBack afa8}
      print$ goblin2 afa8'
      print$ goblin2 afa8' >>= goblin2

      putStrLn ""
      putStrLn "Goblin: afa9"
      let afa9' = goblinUntilFixpoint afa9
      print afa9'
      let Right afa9'' = simplifyAll afa9'
      print afa9''
      let afa9''' = qminCut afa9''
      print afa9'''
      let Right afa9'''' = simplifyAll afa9'''
      print afa9''''
  ]

afa0 :: AfaUnswallowed Int
afa0 = Afa
  { terms = listArray'$ reverse
      [ {- 5 -} And$ 3 :| [4]
      , {- 4 -} State 2
      , {- 3 -} State 1
      , {- 2 -} State 0
      , {- 1 -} Predicate 1
      , {- 0 -} Predicate 0
      ]
  , states = listArray'$ reverse
      [ {- 2 -} 1
      , {- 1 -} 0
      , {- 0 -} 5
      ]
  , initState = 0
  }

afa1 :: AfaUnswallowed Int
afa1 = Afa
  { terms = listArray'$ reverse
      [ {- 13 -} And$ 5 :| [6]
      , {- 12 -} And$ 1 :| [8]
      , {- 11 -} And$ 0 :| [7]
      , {- 10 -} State 6
      , {-  9 -} State 5
      , {-  8 -} State 4
      , {-  7 -} State 3
      , {-  6 -} State 2
      , {-  5 -} State 1
      , {-  4 -} State 0
      , {-  3 -} Predicate 3
      , {-  2 -} Predicate 2
      , {-  1 -} Predicate 1
      , {-  0 -} Predicate 0
      ]
  , states = listArray'$ reverse
      [ {- 6 -} 3
      , {- 5 -} 2
      , {- 4 -} 10
      , {- 3 -} 9
      , {- 2 -} 12
      , {- 1 -} 11
      , {- 0 -} 13
      ]
  , initState = 0
  }

afa2 :: AfaUnswallowed Int
afa2 = Afa
  { terms = array (0,15)
      [ (0,State 3)
      , (1,Predicate 1)
      , (2,Predicate 3)
      , (3,And (0 :| [2]))
      , (4,Or (1 :| [3]))
      , (5,Predicate 4)
      , (6,And (4 :| [5]))
      , (7,Predicate 0)
      , (8,Or (6 :| [7]))
      , (9,State 1)
      , (10,Predicate 5)
      , (11,State 2)
      , (12,And (2 :| [9,11]))
      , (13,Or (7 :| [12]))
      , (14,Or (1 :| [11]))
      , (15,And (8 :| [14]))
      ]
  , states = array (0,3) [(0,15),(1,10),(2,13),(3,1)]
  , initState = 0
  }

afa3 :: AfaUnswallowed Int
afa3 = Afa {terms = array (0,221) [(0,Predicate 0),(1,Predicate 3),(2,Predicate 8),(3,Predicate 9),(4,Predicate 4),(5,Predicate 6),(6,Predicate 7),(7,Predicate 5),(8,Predicate 10),(9,Predicate 11),(10,Predicate 12),(11,Predicate 13),(12,Predicate 14),(13,Predicate 15),(14,Predicate 16),(15,State 28),(16,Predicate 2),(17,State 28),(18,State 28),(19,State 28),(20,And (19 :| [16])),(21,Or (1 :| [20])),(22,State 9),(23,State 9),(24,State 9),(25,State 9),(26,And (25 :| [2,4,5,16])),(27,State 10),(28,State 11),(29,State 11),(30,State 11),(31,State 11),(32,And (31 :| [4,16])),(33,Or (5 :| [32])),(34,State 12),(35,State 12),(36,State 12),(37,State 12),(38,And (37 :| [5,16])),(39,Or (4 :| [38])),(40,State 13),(41,State 13),(42,State 13),(43,State 13),(44,And (43 :| [5,16])),(45,Or (1 :| [44])),(46,Or (8 :| [40])),(47,State 14),(48,State 29),(49,State 29),(50,State 29),(51,And (50 :| [16])),(52,Or (0 :| [51])),(53,State 5),(54,State 5),(55,State 5),(56,State 5),(57,And (56 :| [16])),(58,Or (9 :| [57])),(59,State 14),(60,State 14),(61,State 14),(62,And (61 :| [58])),(63,State 16),(64,State 16),(65,State 16),(66,State 16),(67,And (66 :| [16,46])),(68,State 30),(69,State 17),(70,State 31),(71,State 31),(72,State 31),(73,And (72 :| [0,4,6,16])),(74,State 32),(75,State 18),(76,State 33),(77,State 33),(78,State 33),(79,And (78 :| [16])),(80,State 34),(81,State 4),(82,State 3),(83,State 3),(84,State 3),(85,State 3),(86,And (85 :| [16])),(87,State 8),(88,State 35),(89,State 19),(90,State 19),(91,State 19),(92,State 19),(93,And (92 :| [16])),(94,Or (4 :| [5,81,86,93])),(95,State 6),(96,State 2),(97,State 2),(98,State 2),(99,State 2),(100,And (99 :| [16])),(101,State 20),(102,State 36),(103,State 36),(104,State 36),(105,And (104 :| [16])),(106,State 37),(107,State 1),(108,State 21),(109,State 21),(110,State 21),(111,State 21),(112,And (111 :| [7,16])),(113,Or (1 :| [112])),(114,Or (1 :| [108])),(115,State 1),(116,State 1),(117,State 1),(118,And (117 :| [4,114])),(119,State 22),(120,State 38),(121,State 38),(122,State 38),(123,And (122 :| [16])),(124,State 39),(125,State 22),(126,State 22),(127,State 22),(128,And (127 :| [94])),(129,State 40),(130,State 1),(131,State 1),(132,State 1),(133,And (132 :| [16])),(134,State 41),(135,State 41),(136,State 41),(137,And (136 :| [10,16])),(138,State 23),(139,State 23),(140,State 23),(141,State 23),(142,And (141 :| [0,1,7,16])),(143,State 42),(144,State 24),(145,State 24),(146,State 24),(147,State 24),(148,And (147 :| [0,16])),(149,Or (7 :| [148])),(150,Or (13 :| [14,15,144])),(151,State 7),(152,State 15),(153,State 43),(154,State 43),(155,State 43),(156,And (155 :| [16])),(157,Or (4 :| [57])),(158,And (10 :| [157])),(159,Or (1 :| [6,9,57,133,156,158])),(160,State 25),(161,State 25),(162,State 25),(163,State 25),(164,And (163 :| [5,16])),(165,Or (6 :| [164])),(166,State 26),(167,State 44),(168,State 44),(169,State 44),(170,And (169 :| [4,6,16])),(171,Or (0 :| [7,170])),(172,State 45),(173,State 45),(174,State 45),(175,And (174 :| [16])),(176,State 27),(177,State 46),(178,State 46),(179,State 46),(180,And (179 :| [16,150,159])),(181,State 0),(182,State 0),(183,State 0),(184,State 0),(185,And (184 :| [0,16])),(186,State 47),(187,And (0 :| [52])),(188,Or (52 :| [68])),(189,State 32),(190,State 32),(191,And (190 :| [33,39])),(192,State 48),(193,State 49),(194,State 50),(195,Or (7 :| [12])),(196,State 37),(197,State 37),(198,And (197 :| [4])),(199,Or (2 :| [198])),(200,State 39),(201,State 39),(202,And (201 :| [10])),(203,Or (106 :| [1,202])),(204,State 51),(205,And (7 :| [1])),(206,Or (205 :| [143])),(207,State 5),(208,State 5),(209,And (208 :| [11])),(210,And (165 :| [171])),(211,And (12 :| [171])),(212,State 52),(213,State 53),(214,Or (188 :| [192])),(215,State 50),(216,And (215 :| [21])),(217,State 54),(218,Or (194 :| [203])),(219,And (218 :| [206,211])),(220,Or (219 :| [213])),(221,Or (214 :| [217]))], states = array (0,54) [(0,186),(1,1),(2,2),(3,3),(4,4),(5,7),(6,10),(7,11),(8,12),(9,21),(10,26),(11,33),(12,39),(13,45),(14,52),(15,57),(16,68),(17,74),(18,80),(19,88),(20,106),(21,113),(22,124),(23,143),(24,149),(25,165),(26,171),(27,175),(28,0),(29,187),(30,188),(31,191),(32,192),(33,193),(34,194),(35,195),(36,198),(37,199),(38,202),(39,203),(40,204),(41,205),(42,206),(43,209),(44,210),(45,211),(46,212),(47,213),(48,214),(49,216),(50,217),(51,218),(52,219),(53,220),(54,221)], initState = 0}

afa4 :: AfaUnswallowed Int
afa4 = Afa
  { terms = listArray' [State 0, State 1, And$ 0 :| [1]]
  , states = listArray' [2, 1]
  , initState = 0
  }

afa5 :: AfaUnswallowed Int
afa5 = Afa
  { terms = listArray'$ reverse
      [ {-  6 -} And$ 4 :| [5]
      , {-  5 -} And$ 0 :| [3]
      , {-  4 -} And$ 0 :| [2]
      , {-  3 -} Predicate 1
      , {-  2 -} Predicate 0
      , {-  1 -} State 1
      , {-  0 -} State 0
      ]
  , states = listArray' [1, 6]
  , initState = 0
  }

afa6 :: AfaUnswallowed Int
afa6 = Afa
  { terms = listArray'$ reverse
      [ {-  5 -} And$ 0 :| [1, 2]
      , {-  4 -} Predicate 2
      , {-  3 -} Predicate 1
      , {-  2 -} Predicate 0
      , {-  1 -} State 2
      , {-  0 -} State 1
      ]
  , states = listArray' [5, 3, 4]
  , initState = 0
  }

afa7 :: AfaUnswallowed Int
afa7 = Afa
  { terms = listArray'$ reverse
      [ {-  2 -} And$ 0 :| [1]
      , {-  1 -} State 1
      , {-  0 -} State 0
      ]
  , states = listArray' [1, 2]
  , initState = 0
  }

afa8 :: AfaUnswallowed Int
afa8 = Afa
  { terms = listArray'$ reverse
      [ {-  4 -} And$ 0 :| [1, 2]
      , {-  3 -} Predicate 0
      , {-  2 -} State 2
      , {-  1 -} State 1
      , {-  0 -} State 0
      ]
  , states = listArray' [1, 4, 3]
  , initState = 0
  }

afa9 :: AfaUnswallowed Int
afa9 = Afa
  { terms = listArray'$ reverse
      [ {-  6 -} Or$ 0 :| [1, 3]
      , {-  5 -} Or$ 1 :| [3]
      , {-  4 -} Or$ 0 :| [2]
      , {-  3 -} Predicate 1
      , {-  2 -} Predicate 0
      , {-  1 -} State 2
      , {-  0 -} State 1
      ]
  , states = listArray' [6, 4, 5]
  , initState = 0
  }
