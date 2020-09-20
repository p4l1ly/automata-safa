{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternSynonyms #-}

module Afa.Convert.Capnp.Separated where

import Control.Arrow
import Data.Array
import Afa.Convert.Separated (SeparatedAfa(..), QTerm(..), ATerm(..))
import qualified Capnp.Gen.Schema.SeparatedAfa.Pure as Schema
import qualified Capnp.GenHelpers.ReExports.Data.Vector as V
import Data.Functor.Foldable.Dag.TreeHybrid (pattern BRef, pattern BNRef, MyBase)
import Data.Functor.Foldable (cata)
import qualified Capnp
import System.IO

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

serializeQTerm :: MyBase QTerm Int Schema.QTerm -> Schema.QTerm
serializeQTerm (BRef i) = Schema.QTerm'ref$ fromIntegral i
serializeQTerm (BNRef (QState i)) = Schema.QTerm'state$ fromIntegral i
serializeQTerm (BNRef (QAnd xs)) = Schema.QTerm'and$ V.fromList xs
serializeQTerm (BNRef (QOr xs)) = Schema.QTerm'or$ V.fromList xs

serializeATerm :: MyBase ATerm Int Schema.ATerm -> Schema.ATerm
serializeATerm (BRef i) = Schema.ATerm'ref$ fromIntegral i
serializeATerm (BNRef (AVar i)) = Schema.ATerm'var$ fromIntegral i
serializeATerm (BNRef (AAnd xs)) = Schema.ATerm'and$ V.fromList xs
serializeATerm (BNRef (AOr xs)) = Schema.ATerm'or$ V.fromList xs
serializeATerm (BNRef (ANot x)) = Schema.ATerm'not x
