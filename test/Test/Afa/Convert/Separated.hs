module Test.Afa.Convert.Separated where

import Test.HUnit hiding (State)

import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE

import Afa
import Afa.Lib
import Afa.Lib.Tree
import Afa.Bool
import qualified Afa.Term.Bool as BoolT
import qualified Afa.Term.Mix as MixT
import Afa.Convert.Separated
import qualified Afa.Convert.Separated.Model as SepAfa

tests =
  [ "Afa.Convert.Separated" ~: do
      assertEqual "initTry1" Nothing$ mixedToSeparated afa1

      let separabilized = afa1{afa = separabilizeAfa$ afa afa1}
      let Just separabilized' = mixedToSeparated separabilized 
      let separabilized'' = SepAfa.simplify separabilized'

      let delayed = afa1{afa = delayPredicates$ afa afa1}
      let Just delayed' = mixedToSeparated delayed
      let delayed'' = SepAfa.simplify delayed'

      assertEqual "separabilized1" separabilized''$ Right$ SepAfa.Afa
        { SepAfa.aterms = listArray' [a]
        , SepAfa.qterms = listArray' [MixT.State 1]
        , SepAfa.states = listArray'
            [ [(Just 0, Nothing), (Nothing, Just 0)]
            , [(Just 0, Nothing)]
            ]
        , SepAfa.initState = 0
        }

      assertEqual "delayed1" delayed''$ Right$ SepAfa.Afa
        { SepAfa.aterms = listArray' [a]
        , SepAfa.qterms = listArray' [MixT.State 1, MixT.State 2, MixT.Or$ 0 :| [1]]
        , SepAfa.states = listArray'
            [ [(Nothing, Just 2)]
            , [(Just 0, Nothing)]
            , [(Nothing, Just 0)]
            ]
        , SepAfa.initState = 0
        }
  ]


(a:_) = map BoolT.Predicate [0..]

afa0 :: BoolAfaUnswallowed Int
afa0 = unswallow$ BoolAfa
  { boolTerms = listArray' []
  , afa = Afa
    { terms = listArray' []
    , states = listArray'
        [ Node$ MixT.Or$ NE.fromList [Node$ MixT.State 1, Node$ MixT.Predicate$ Node$ BoolT.Predicate 0]
        , Node$ MixT.Predicate$ Node$ BoolT.Predicate 0
        ]
    , initState = 0
    }
  }

afa1 :: BoolAfaUnswallowed Int
afa1 = BoolAfa
  { boolTerms = listArray'$ reverse
      [ {- 3 -} BoolT.And$ 0 :| [1]
      , {- 2 -} a
      , {- 1 -} a
      , {- 0 -} BoolT.LTrue
      ]
  , afa = Afa
      { terms = listArray'$ reverse
          [ {- 9 -} MixT.And$ 7 :| [8]
          , {- 8 -} MixT.Or$ 2 :| [1]
          , {- 7 -} MixT.Or$ 6 :| [4]
          , {- 6 -} MixT.State 2
          , {- 5 -} MixT.Predicate 0
          , {- 4 -} MixT.Predicate 3
          , {- 3 -} MixT.And$ 0 :| [1, 2]
          , {- 2 -} MixT.State 1
          , {- 1 -} MixT.Predicate 2
          , {- 0 -} MixT.LTrue
          ]
      , states = listArray'$ reverse
          [ {- 2 -} 3
          , {- 1 -} 5
          , {- 0 -} 9
          ]
      , initState = 0
      }
  }
