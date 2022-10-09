{-# LANGUAGE ScopedTypeVariables #-}

module Afa.Convert.Capnp.CnfAfa where

import qualified Capnp
import qualified Capnp.Gen.Afa.Model.CnfAfa as Schema
import Data.Array
import qualified Data.Vector as V
import System.IO

import Afa.Convert.CnfAfa (CnfAfa (..), Lit (..))

hWriteCnfAfa :: CnfAfa -> Handle -> IO ()
hWriteCnfAfa afa h = Capnp.hPutParsed h $ serializeCnfAfa afa

serializeCnfAfa :: CnfAfa -> Capnp.Parsed Schema.Afa
serializeCnfAfa (CnfAfa states varCount clauses) =
  Schema.Afa
    { Schema.variableCount = fromIntegral varCount
    , Schema.outputs = V.fromList $ map toSchemaLit $ elems states
    , Schema.clauses = V.fromList $ map (V.fromList . map toSchemaLit) clauses
    }

toSchemaLit :: Lit -> Capnp.Parsed Schema.Lit
toSchemaLit (Lit ix sign) =
  Schema.Lit{Schema.var = fromIntegral ix, Schema.positive = sign}
