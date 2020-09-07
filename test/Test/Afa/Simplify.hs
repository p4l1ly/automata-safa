module Test.Afa.Simplify where

import Test.HUnit hiding (State)

import Data.Array
import Data.Functor.Foldable

import Afa
import Afa.TreeDag.Patterns.Builder

tests =
  [ "Afa.Simplify" ~: do
      assertEqual "followRefs"
        afa_afterFollowRefs Afa
          { terms = listArray (0, 11)
              [ {-  t0 -} b
              , {-  t1 -} Not (Not a)
              , {-  t2 -} Or [Ref 1, Ref 0]
              , {-  t3 -} And [a, Ref 1]
              , {-  t4 -} Ref 2
              , {-  t5 -} Ref 4
              , {-  t6 -} Ref 5
              , {-  t7 -} Or [b, a]
              , {-  t8 -} Not a
              , {-  t9 -}
                And [Not (Ref 8), Or [And [Ref 7, Ref 3, Ref 2], And [Ref 2, b]], Ref 5]
              , {- t10 -} And [Ref 6, Ref 1]
              , {- t11 -} And [Ref 10, Ref 10]
              ]
          , states = listArray (0, 1)
              [ {- q0 -} 2
              , {- q1 -} 9
              ]
          }
      assertEqual "removeOrphans"
        afa_afterRemoveOrphans Afa
          { terms = listArray (0, 8)
              [ {- t0 -} b
              , {- t1 -} Not (Not a)
              , {- t2 -} Or [Ref 1, Ref 0]
              , {- t3 -} And [a, Ref 1]
              , {- t4 -} Ref 2
              , {- t5 -} Ref 4
              , {- t6 -} Or [b, a]
              , {- t7 -} Not a
              , {- t8 -}
                And [Not (Ref 7), Or [And [Ref 6, Ref 3, Ref 2], And [Ref 2, b]], Ref 5]
              ]
          , states = listArray (0, 1)
              [ {- q0 -} 2
              , {- q1 -} 8
              ]
          }
      assertEqual "swallowOnlyChilds"
        afa_afterSwallowOnlyChilds Afa
          { terms = listArray (0, 2)
              [ {- t0 -} Not (Not a)
              , {- t1 -} Or [Ref 0, b]
              , {- t2 -}
                And
                  [ Not (Not a)
                  , Or [And [Or [b, a], And [a, Ref 0], Ref 1], And [Ref 1, b]]
                  , Ref 1
                  ]
              ]
          , states = listArray (0, 1)
              [ {- q0 -} 1
              , {- q1 -} 2
              ]
          }
      assertEqual "simplify"
        afa_afterSimplify Afa
          { terms = listArray (0, 2)
              [ {- t0 -} a
              , {- t1 -} Or [Ref 0, b]
              , {- t2 -}
                And [a, Or [And [Or [b, a], a, Ref 0, Ref 1], And [Ref 1, b]], Ref 1]
              ]
          , states = listArray (0, 1)
              [ {- q0 -} 1
              , {- q1 -} 2
              ]
          }
      assertEqual "costFixpoint"
        afa_afterCostFixpoint Afa
          { terms = listArray (0, 1)
              [ {- t0 -} Or [a, b]
              , {- t1 -}
                And [a, Or [And [Or [b, a], a, a, Ref 0], And [Ref 0, b]], Ref 0]
              ]
          , states = listArray (0, 1)
              [ {- q0 -} 0
              , {- q1 -} 1
              ]
          }
      assertEqual "afterHashConsThenSwallow"
        afa_afterHashConsThenSwallow Afa
          { terms = listArray (0, 1)
              [ {- t0 -} Or [a, b]
              , {- t1 -} And [a, Ref 0, Or [And [a, Ref 0], And [b, Ref 0]]]
              ]
          , states = listArray (0, 1)
              [ {- q0 -} 0
              , {- q1 -} 1
              ]
          }
  ]


(a:b:_) = map Var [0..]

afa0 :: Afa
afa0 = Afa
  { terms = listArray (0, 11)
      [ {-  t0 -} b
      , {-  t1 -} Not (Not a)
      , {-  t2 -} Or [Ref 1, Ref 0]
      , {-  t3 -} And [a, Ref 1]
      , {-  t4 -} Ref 2
      , {-  t5 -} Ref 4
      , {-  t6 -} Ref 5
      , {-  t7 -} Or [b, a]
      , {-  t8 -} Not a
      , {-  t9 -}
        And [Not (Ref 8), Or [And [Ref 7, Ref 3, Ref 2], And [Ref 2, b]], Ref 5]
      , {- t10 -} And [Ref 6, Ref 1]
      , {- t11 -} And [Ref 10, Ref 10]
      ]
  , states = listArray (0, 1)
      [ {- q0 -} 6
      , {- q1 -} 9
      ]
  }

afa_afterFollowRefs :: Afa
afa_afterFollowRefs = followRefs afa0

afa_afterRemoveOrphans :: Afa
afa_afterRemoveOrphans = removeOrphans afa_afterFollowRefs

afa_afterSwallowOnlyChilds :: Afa
afa_afterSwallowOnlyChilds = swallowOnlyChilds afa_afterRemoveOrphans

afa_afterSimplify :: Afa
afa_afterSimplify = simplify afa_afterSwallowOnlyChilds

afa_afterCostFixpoint :: Afa
afa_afterCostFixpoint =
  costFixpoint (simplify . swallowOnlyChilds) afa_afterRemoveOrphans

afa_afterHashConsThenSwallow :: Afa
afa_afterHashConsThenSwallow = hashConsThenSwallow afa_afterCostFixpoint
