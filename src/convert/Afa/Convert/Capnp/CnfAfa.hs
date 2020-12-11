{-# LANGUAGE ScopedTypeVariables #-}

module Afa.Convert.Capnp.CnfAfa where

import Data.Array
import qualified Capnp
import qualified Capnp.GenHelpers.ReExports.Data.Vector as V
import qualified Capnp.Gen.Afa.Model.CnfAfa.Pure as Schema
import System.IO

import Afa.Convert.CnfAfa (CnfAfa(..), Lit(..))

hWriteCnfAfa :: CnfAfa -> Handle -> IO ()
hWriteCnfAfa afa h = Capnp.hPutValue h$ serializeCnfAfa afa

serializeCnfAfa :: CnfAfa -> Schema.Afa
serializeCnfAfa (CnfAfa states varCount clauses) = Schema.Afa
  { Schema.variableCount = fromIntegral varCount
  , Schema.outputs = V.fromList$ map toSchemaLit$ elems states
  , Schema.clauses = V.fromList$ map (V.fromList . map toSchemaLit) clauses
  }

toSchemaLit :: Lit -> Schema.Lit
toSchemaLit (Lit ix sign) =
  Schema.Lit{Schema.var = fromIntegral ix, Schema.positive = sign}
