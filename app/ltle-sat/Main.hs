{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad.Primitive (touch)
import System.Environment

import Capnp (def, defaultLimit, hGetValue)
import Capnp.Rpc (ConnConfig (..), handleConn, socketTransport, wait, (?))
import Control.Arrow
import Control.Monad
import Network.Simple.TCP (connect)

import Afa.Convert.Ltle
import Afa.Ops.Preprocess (SimplificationResult (..), preprocess)
import Ltl.Parser

import qualified Capnp.Gen.Schema.LoadedModelRpc.Pure as Rpc

import Afa.Convert.Capnp.CnfAfa
import Afa.Convert.CnfAfa
import qualified Capnp.Gen.Schema.CnfAfaRpc.Pure as CnfRpc

import qualified Afa.Convert.Capnp.Separated as SepCapnp
import Afa.Convert.Separated
import qualified Capnp.Gen.Schema.SeparatedAfaRpc.Pure as SepRpc

import qualified Capnp.Gen.Schema.MultisolverRpc.Pure as MRpc

main :: IO ()
main = do
  ltls <- lines <$> getContents
  let afas = map (second preprocess . ltleToAfa . parseLtl) ltls
  getArgs >>= \case
    ["afaminisat"] -> checkAfaminisat afas
    ["dantoni"] -> checkDAntoni afas
    ["justPrint"] -> justPrint afas
    _ -> checkBoth afas

justPrint :: [(Int, SimplificationResult)] -> IO ()
justPrint afas = forM_ (zip [0 ..] afas) $ \(i, (varCount, afa)) -> do
  print i
  print varCount
  print afa

checkAfaminisat :: [(Int, SimplificationResult)] -> IO ()
checkAfaminisat afas = connect "localhost" "4002" $ \(sock, _addr) ->
  handleConn
    (socketTransport sock defaultLimit)
    def
      { withBootstrap = Just $ \_sup client ->
          void $
            forM (zip [0 ..] afas) $ \(i, afa) -> do
              msg <- case afa of
                (_, NonPositiveStates) -> return "NonPositiveStates"
                (_, EmptyLang) -> return "EmptyLang (detected in preprocessing)"
                (_, NonEmptyLang) -> return "NonEmptyLang (detected in preprocessing)"
                (varCount, UndecidedEmptiness afa) -> do
                  let cnfafa = serializeCnfAfa $ tseytin varCount afa
                  CnfRpc.Loader'load'results{CnfRpc.loadedModel} <-
                    wait
                      =<< CnfRpc.loader'load (CnfRpc.Loader client) ? def{CnfRpc.model = cnfafa}
                  Rpc.ModelChecking'solve'results time result <-
                    wait
                      =<< Rpc.modelChecking'solve loadedModel ? def
                  touch loadedModel
                  return $
                    show time ++ " "
                      ++ case result of
                        Rpc.ModelChecking'Result'empty -> "EmptyLang"
                        Rpc.ModelChecking'Result'nonempty -> "NonEmptyLang"
                        Rpc.ModelChecking'Result'cancelled -> "ModelCheckingCancelled"

              putStrLn $ show i ++ " " ++ msg
      }

checkDAntoni :: [(Int, SimplificationResult)] -> IO ()
checkDAntoni afas = connect "localhost" "4001" $ \(sock, _addr) ->
  handleConn
    (socketTransport sock defaultLimit)
    def
      { withBootstrap = Just $ \_sup client ->
          void $
            forM (zip [0 ..] afas) $ \(i, afa) -> do
              msg <- case afa of
                (_, NonPositiveStates) -> return "NonPositiveStates"
                (_, EmptyLang) -> return "EmptyLang (detected in preprocessing)"
                (_, NonEmptyLang) -> return "NonEmptyLang (detected in preprocessing)"
                (varCount, UndecidedEmptiness afa) -> do
                  let sepafa = SepCapnp.serialize varCount $ separate afa
                  SepRpc.Loader'load'results{SepRpc.loadedModel} <-
                    wait
                      =<< SepRpc.loader'load (SepRpc.Loader client) ? def{SepRpc.model = sepafa}
                  Rpc.ModelChecking'solve'results time result <-
                    wait
                      =<< Rpc.modelChecking'solve loadedModel ? def
                  touch loadedModel
                  return $
                    show time ++ " "
                      ++ case result of
                        Rpc.ModelChecking'Result'empty -> "EmptyLang"
                        Rpc.ModelChecking'Result'nonempty -> "NonEmptyLang"
                        Rpc.ModelChecking'Result'cancelled -> "ModelCheckingCancelled"

              putStrLn $ show i ++ " " ++ msg
      }

checkBoth :: [(Int, SimplificationResult)] -> IO ()
checkBoth afas = connect "localhost" "4000" $ \(sock, _addr) ->
  handleConn
    (socketTransport sock defaultLimit)
    def
      { withBootstrap = Just $ \_sup client ->
          void $
            forM (zip [0 ..] afas) $ \(i, afa) -> do
              msg <- case afa of
                (_, NonPositiveStates) -> return "NonPositiveStates"
                (_, EmptyLang) -> return "EmptyLang (detected in preprocessing)"
                (_, NonEmptyLang) -> return "NonEmptyLang (detected in preprocessing)"
                (varCount, UndecidedEmptiness afa) -> do
                  let cnfafa = serializeCnfAfa $ tseytin varCount afa
                  let sepafa = SepCapnp.serialize varCount $ separate afa

                  MRpc.SeparatedCnfLoader'load'results{MRpc.loadedModel} <-
                    wait
                      =<< MRpc.separatedCnfLoader'load (MRpc.SeparatedCnfLoader client)
                        ? def
                          { MRpc.separatedAfa = sepafa
                          , MRpc.cnfAfa = cnfafa
                          }

                  MRpc.ModelChecking'solve'results times results <-
                    wait
                      =<< MRpc.modelChecking'solve loadedModel ? def

                  touch loadedModel

                  return $
                    show times ++ " "
                      ++ ( show $
                            (`fmap` results) $ \case
                              Rpc.ModelChecking'Result'empty -> "EmptyLang"
                              Rpc.ModelChecking'Result'nonempty -> "NonEmptyLang"
                              Rpc.ModelChecking'Result'cancelled -> "ModelCheckingCancelled"
                         )

              putStrLn $ show i ++ " " ++ msg
      }
