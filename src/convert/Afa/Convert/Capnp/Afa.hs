{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NamedFieldPuns #-}

module Afa.Convert.Capnp.Afa where

import Data.Array
import qualified Capnp
import qualified Capnp.GenHelpers.ReExports.Data.Vector as V
import Capnp.Gen.Schema.Afa.Pure
import System.IO
import qualified Afa
import qualified Afa.Term.TreeF as T
import qualified Afa.Term.TreeFBase as TB
import Data.Functor.Foldable (cata)

hReadAfa :: Handle -> IO Afa.Afa
hReadAfa h = deserializeAfa <$> Capnp.hGetValue h Capnp.defaultLimit

hWriteAfa :: Afa.Afa -> Handle -> IO ()
hWriteAfa afa h = Capnp.hPutValue h$ serializeAfa afa

deserializeAfa :: Afa -> Afa.Afa
deserializeAfa Afa{terms, states} = Afa.Afa
  { Afa.terms = listArray (0, length terms - 1)$ map deserializeTerm$ V.toList terms
  , Afa.states = listArray (0, length states - 1)$ map fromIntegral$ V.toList states
  }

deserializeTerm :: Term -> T.Term
deserializeTerm Term'litTrue = T.LTrue
deserializeTerm Term'litFalse = T.LFalse
deserializeTerm (Term'var i) = T.Var$ fromIntegral i
deserializeTerm (Term'state i) = T.State$ fromIntegral i
deserializeTerm (Term'ref i) = T.Ref$ fromIntegral i
deserializeTerm (Term'and xs) = T.And$ map deserializeTerm$ V.toList xs
deserializeTerm (Term'or xs) = T.Or$ map deserializeTerm$ V.toList xs
deserializeTerm (Term'not x) = T.Not$ deserializeTerm x

serializeAfa :: Afa.Afa -> Afa
serializeAfa (Afa.Afa terms states) = Afa
  { terms = V.fromList$ map (cata serializeTerm)$ elems terms
  , states = V.fromList$ map fromIntegral$ elems states
  }

serializeTerm :: TB.Term Term -> Term
serializeTerm TB.LTrue = Term'litTrue
serializeTerm TB.LFalse = Term'litFalse
serializeTerm (TB.Var i) = Term'var$ fromIntegral i
serializeTerm (TB.State i) = Term'state$ fromIntegral i
serializeTerm (TB.Ref i) = Term'ref$ fromIntegral i
serializeTerm (TB.And xs) = Term'and$ V.fromList xs
serializeTerm (TB.Or xs) = Term'or$ V.fromList xs
serializeTerm (TB.Not x) = Term'not x
