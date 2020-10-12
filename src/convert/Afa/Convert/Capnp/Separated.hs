{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternSynonyms #-}

module Afa.Convert.Capnp.Separated where

import Control.Arrow
import Data.Array
import qualified Capnp.Gen.Schema.SeparatedAfa.Pure as Schema
import qualified Capnp.GenHelpers.ReExports.Data.Vector as V
import Data.Functor.Tree (pattern BLeaf, pattern BNode, TreeBase)
import Data.Functor.Foldable (cata)
import qualified Capnp
import System.IO

import Afa.Convert.Separated (SeparatedAfa(..), QTerm(..), ATerm(..))

hWrite :: Int -> SeparatedAfa -> Handle -> IO ()
hWrite varCount afa h = Capnp.hPutValue h$ serialize varCount afa

serialize :: Int -> SeparatedAfa -> Schema.SeparatedAfa
serialize varCount SeparatedAfa{qterms, aterms, states} = Schema.SeparatedAfa
  { Schema.qterms = V.fromList$ map (cata serializeQTerm)$ elems qterms
  , Schema.aterms = V.fromList$ map (cata serializeATerm)$ elems aterms
  , Schema.states = V.fromList$ flip map (elems states)$
      V.fromList . map (uncurry Schema.Conjunct . (fromIntegral *** fromIntegral))
  , Schema.variableCount = fromIntegral varCount
  }

serializeQTerm :: TreeBase QTerm Int Schema.QTerm -> Schema.QTerm
serializeQTerm (BLeaf i) = Schema.QTerm'ref$ fromIntegral i
serializeQTerm (BNode (QState i)) = Schema.QTerm'state$ fromIntegral i
serializeQTerm (BNode (QAnd xs)) = Schema.QTerm'and$ V.fromList xs
serializeQTerm (BNode (QOr xs)) = Schema.QTerm'or$ V.fromList xs

serializeATerm :: TreeBase ATerm Int Schema.ATerm -> Schema.ATerm
serializeATerm (BLeaf i) = Schema.ATerm'ref$ fromIntegral i
serializeATerm (BNode (AVar i)) = Schema.ATerm'var$ fromIntegral i
serializeATerm (BNode (AAnd xs)) = Schema.ATerm'and$ V.fromList xs
serializeATerm (BNode (AOr xs)) = Schema.ATerm'or$ V.fromList xs
serializeATerm (BNode (ANot x)) = Schema.ATerm'not x
