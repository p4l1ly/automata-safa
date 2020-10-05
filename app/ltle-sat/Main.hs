{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
module Main (main) where

import System.Environment

import Control.Arrow
import Control.Monad
import Network.Simple.TCP (connect)
import Capnp     (def, defaultLimit)
import Capnp.Rpc (ConnConfig(..), handleConn, socketTransport, wait, (?))

import Ltl.Parser
import Afa (SimplificationResult(..), preprocess)
import Afa.Convert.Ltle

import qualified Capnp.Gen.Schema.LoadedModelRpc.Pure as Rpc

import Afa.Convert.CnfAfa
import Afa.Convert.Capnp.CnfAfa
import qualified Capnp.Gen.Schema.CnfAfaRpc.Pure as CnfRpc

import Afa.Convert.Separated
import qualified Afa.Convert.Capnp.Separated as SepCapnp
import qualified Capnp.Gen.Schema.SeparatedAfaRpc.Pure as SepRpc

import qualified Capnp.Gen.Schema.MultisolverRpc.Pure as MRpc

main :: IO ()
main = do
  ltls <- lines<$> getContents
  let afas = map (second preprocess . ltleToAfa . parseLtl) ltls
  getArgs >>= \case
    ["afaminisat"] -> checkAfaminisat afas
    ["dantoni"] -> checkDAntoni afas
    _ -> checkBoth afas

checkAfaminisat :: [(Int, SimplificationResult)] -> IO ()
checkAfaminisat afas = connect "localhost" "4002" $ \(sock, _addr) ->
  handleConn (socketTransport sock defaultLimit) def
    { withBootstrap = Just $ \_sup client ->
        void$ forM afas$ \case
          (_, NonPositiveStates) -> putStrLn "NonPositiveStates"
          (_, EmptyLang) -> putStrLn "EmptyLang (detected in preprocessing)"
          (_, NonEmptyLang) -> putStrLn "NonEmptyLang (detected in preprocessing)"
          (varCount, UndecidedEmptiness afa) -> do
            let cnfafa = serializeCnfAfa$ tseytin varCount afa
            CnfRpc.Loader'load'results{CnfRpc.loadedModel} <- wait =<<
              CnfRpc.loader'load (CnfRpc.Loader client) ? def{CnfRpc.model=cnfafa}
            Rpc.ModelChecking'solve'results time result <- wait =<<
              Rpc.modelChecking'solve loadedModel ? def
            print time
            putStrLn$ case result of
              Rpc.ModelChecking'Result'empty -> "EmptyLang"
              Rpc.ModelChecking'Result'nonempty -> "NonEmptyLang"
              Rpc.ModelChecking'Result'cancelled -> "ModelCheckingCancelled"
    }

checkDAntoni :: [(Int, SimplificationResult)] -> IO ()
checkDAntoni afas = connect "localhost" "4001" $ \(sock, _addr) ->
  handleConn (socketTransport sock defaultLimit) def
    { withBootstrap = Just $ \_sup client ->
        void$ forM afas$ \case
          (_, NonPositiveStates) -> putStrLn "NonPositiveStates"
          (_, EmptyLang) -> putStrLn "EmptyLang (detected in preprocessing)"
          (_, NonEmptyLang) -> putStrLn "NonEmptyLang (detected in preprocessing)"
          (varCount, UndecidedEmptiness afa) -> do
            let sepafa = SepCapnp.serialize varCount$ separate afa
            SepRpc.Loader'load'results{SepRpc.loadedModel} <- wait =<<
              SepRpc.loader'load (SepRpc.Loader client) ? def{SepRpc.model=sepafa}
            Rpc.ModelChecking'solve'results time result <- wait =<<
              Rpc.modelChecking'solve loadedModel ? def
            print time
            putStrLn$ case result of
              Rpc.ModelChecking'Result'empty -> "EmptyLang"
              Rpc.ModelChecking'Result'nonempty -> "NonEmptyLang"
              Rpc.ModelChecking'Result'cancelled -> "ModelCheckingCancelled"
    }

checkBoth :: [(Int, SimplificationResult)] -> IO ()
checkBoth afas = connect "localhost" "4000" $ \(sock, _addr) ->
  handleConn (socketTransport sock defaultLimit) def
    { withBootstrap = Just $ \_sup client ->
        void$ forM afas$ \case
          (_, NonPositiveStates) -> putStrLn "NonPositiveStates"
          (_, EmptyLang) -> putStrLn "EmptyLang (detected in preprocessing)"
          (_, NonEmptyLang) -> putStrLn "NonEmptyLang (detected in preprocessing)"
          (varCount, UndecidedEmptiness afa) -> do
            let cnfafa = serializeCnfAfa$ tseytin varCount afa
            let sepafa = SepCapnp.serialize varCount$ separate afa

            MRpc.SeparatedCnfLoader'load'results{MRpc.loadedModel} <- wait =<<
              MRpc.separatedCnfLoader'load (MRpc.SeparatedCnfLoader client) ? def
                { MRpc.separatedAfa=sepafa
                , MRpc.cnfAfa=cnfafa
                }

            MRpc.ModelChecking'solve'results times results <- wait =<<
              MRpc.modelChecking'solve loadedModel ? def

            print times
            print$ (`fmap` results)$ \case
              Rpc.ModelChecking'Result'empty -> "EmptyLang"
              Rpc.ModelChecking'Result'nonempty -> "NonEmptyLang"
              Rpc.ModelChecking'Result'cancelled -> "ModelCheckingCancelled"
    }
