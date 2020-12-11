{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternSynonyms #-}

module Afa.Convert.Capnp.Separated where

import Data.Functor
import Control.Arrow
import Data.Void
import Data.Array
import qualified Capnp.Gen.Afa.Model.Separated.Pure as AfaC
import qualified Capnp.Gen.Afa.Model.Term.Pure as TermC
import qualified Capnp.GenHelpers.ReExports.Data.Vector as V
import qualified Capnp
import System.IO

import Afa.Convert.Separated.Model (Afa(..))
import Afa.Convert.Capnp.Afa (serializeBTerm, varCount, iNeToVec)
import qualified Afa.Term.Mix as MTerm

hWrite :: Afa Int -> Handle -> IO ()
hWrite afa h = Capnp.hPutValue h$ serializeAfa afa

serializeAfa :: Afa Int -> AfaC.BoolAfa
serializeAfa (Afa aterms qterms states 0) = AfaC.BoolAfa
  { AfaC.aterms = V.fromList$ map serializeBTerm$ elems aterms
  , AfaC.varCount = fromIntegral$ varCount aterms
  , AfaC.qterms = V.fromList$ map serializeQTerm$ elems qterms
  , AfaC.states = V.fromList$ elems states <&>
      V.fromList . map (uncurry AfaC.Conjunct11 . (toMaybe1 *** toMaybe1))
  }

toMaybe1 :: Maybe Int -> AfaC.Maybe1
toMaybe1 Nothing = AfaC.Maybe1'nothing
toMaybe1 (Just a) = AfaC.Maybe1'just$ fromIntegral a

serializeQTerm :: MTerm.Term Void Int Int -> TermC.QTerm11
serializeQTerm MTerm.LTrue = TermC.QTerm11'litTrue
serializeQTerm (MTerm.State q) = TermC.QTerm11'state$ fromIntegral q
serializeQTerm (MTerm.Or xs) = TermC.QTerm11'or$ iNeToVec xs
serializeQTerm (MTerm.And xs) = TermC.QTerm11'and$ iNeToVec xs
