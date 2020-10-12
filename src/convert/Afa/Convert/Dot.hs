{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ExtendedDefaultRules #-}

module Afa.Convert.Dot (toDot) where

import Data.Foldable
import Text.InterpolatedString.Perl6 (qq)
import Data.List
import Data.Array
import Data.Array.MArray
import Control.Monad.Trans
import Control.Monad.ST
import Data.Functor.Foldable.Dag.Monadic (cataScanM)
import Data.Functor.Tree (treeFAlgM)
import Data.Functor.Foldable.Dag.Consing (nocons, runNoConsMonadT)

import qualified Afa.Term.TreeF as THB
import Afa
import Afa.Term

dagTerms :: Array Int THB.Term -> (Array Int Int, [Term Int])
dagTerms terms = runST$ runNoConsMonadT$
  cataScanM (treeFAlgM nocons) terms >>= lift . freeze

toDot :: Bool -> Afa -> String
toDot cyclic Afa{terms, states} = intercalate "\n"
  [ "digraph afa {"
  , "  graph [nodesep=0.2];"
  , "  node [fontsize=20];"
  , intercalate "\n"
      [ [qq|  "{termNames!i}" -> "{termNames!j}"|]
      | (i, term) <- zip [0..] terms'
      , j <- toList term
      ]
  , intercalate "\n"
      [ [qq|  "q{i}" -> "{termNames!q}"|]
      | (i, q) <- zip [0..] states'
      ]
  , intercalate "\n"
      [ [qq|  "q{i}" [style=filled, fillcolor=pink]|]
      | (i, q) <- zip [0..] states'
      ]
  , intercalate "\n"
      [ [qq|  "{termNames!i}" [style=filled, {style term}]|]
      | (i, term) <- zip [0..] terms'
      ]
  , "}"
  ]
  where
    (ixMap, terms') = dagTerms terms
    states' = map (ixMap!)$ elems states
    termNames = listArray (0, length terms' - 1)$
      flip map (zip [0..] terms')$ \(i, t) -> case t of
        LTrue -> [qq|{i}T|] :: String
        LFalse -> [qq|{i}F|]
        (Var j) -> [qq|{i}v{j}|]
        (State j) -> if cyclic then [qq|q{j}|] else [qq|{i}q{j}|]
        (Not _) -> [qq|{i}!|]
        (And _) -> [qq|{i}&|]
        (Or _) -> [qq|{i}||]

    style (Not _) = "shape=rectangle, fillcolor=indianred1"
    style (And _) = "shape=rectangle, fillcolor=lightgoldenrod1"
    style (Or _) = "shape=rectangle, fillcolor=lightblue"
    style (Var _) = "shape=rectangle, fillcolor=yellow"
    style (State _) = "shape=rectangle, fillcolor=pink"
    style LTrue = "shape=rectangle, fillcolor=green"
    style LFalse = "shape=rectangle, fillcolor=red"
