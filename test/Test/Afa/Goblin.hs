module Test.Afa.Goblin where

import Test.HUnit hiding (State)

import Data.Functor
import Data.List.NonEmpty (NonEmpty(..))

import Afa
import Afa.Lib
import Afa.Term.Mix
import Afa.Ops.Goblin

tests =
  [ "Afa.Goblin" ~: do
      let Right simpAfa1 = simplifyAll afa1 <&> reorderStates
      print simpAfa1
      let Just gobAfa1 = goblin simpAfa1
      print gobAfa1
      let Right simpAfa2 = simplifyAll gobAfa1 <&> reorderStates
      print simpAfa2
      -- assertEqual "afa0" simpAfa$ Right Afa
      --   { terms = listArray' [Predicate 0, State 1]
      --   , states = listArray' [1, 0]
      --   , initState = 0
      --   }
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
