{-# LANGUAGE ExtendedDefaultRules #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module Afa.Convert.Dot (toDot) where

import Data.Array
import Data.Foldable
import Data.String.Interpolate.IsString
import qualified Data.Text as T

import Afa
import Afa.Bool
import qualified Afa.Term.Bool as BTerm
import qualified Afa.Term.Mix as MTerm

toDot :: Bool -> BoolAfaUnswallowed Int -> T.Text
toDot cyclic (BoolAfa bterms (Afa mterms states init)) =
  T.unlines
    [ "digraph afa {"
    , "  graph [nodesep=0.2];"
    , "  node [fontsize=20];"
    , T.unlines [[i|  b#{j} -> #{c};|] | (j, t) <- assocs bterms, c <- bchilds t]
    , T.unlines [[i|  m#{j} -> #{c};|] | (j, t) <- assocs mterms, c <- mchilds t]
    , T.unlines [[i|  q#{j} -> m#{q}|] | (j, q) <- assocs states]
    , T.unlines [[i|  q#{j} [style=filled, fillcolor=pink]|] | (j, _) <- assocs states]
    , T.unlines [[i|  b#{j} [style=filled, #{bstyle j t}]|] | (j, t) <- assocs bterms]
    , T.unlines [[i|  m#{j} [style=filled, #{mstyle j t}]|] | (j, t) <- assocs mterms]
    , "}"
    ]
  where
    bchilds t = [[i|b#{c}|] | c <- toList t]
    mchilds t = case t of
      MTerm.Predicate p -> [[i|b#{p}|]]
      MTerm.State q -> if cyclic then [[i|q#{q}|]] else [[i|Q#{q}|]]
      _ -> [[i|m#{c}|] | c <- toList t]

    bstyle j (BTerm.Not _) = "shape=rectangle, fillcolor=indianred1"
    bstyle j (BTerm.And _) = "shape=rectangle, fillcolor=lightgoldenrod1"
    bstyle j (BTerm.Or _) = "shape=rectangle, fillcolor=lightblue"
    bstyle j (BTerm.Predicate p) = [i|shape=rectangle, fillcolor=yellow, label=b#{j}p#{p}|]
    bstyle j BTerm.LTrue = "shape=rectangle, fillcolor=green"
    bstyle j BTerm.LFalse = "shape=rectangle, fillcolor=red"

    mstyle j (MTerm.And _) = "shape=rectangle, fillcolor=lightgoldenrod1"
    mstyle j (MTerm.Or _) = "shape=rectangle, fillcolor=lightblue"
    mstyle j (MTerm.Predicate p) = [i|shape=rectangle, fillcolor=lightgrey, label=m#{j}p#{p}|]
    mstyle j (MTerm.State _) = "shape=rectangle, fillcolor=white"
    mstyle j MTerm.LTrue = "shape=rectangle, fillcolor=green"
