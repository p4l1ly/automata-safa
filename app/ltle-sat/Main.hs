{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
module Main (main) where

import Control.Arrow
import Control.Monad
import Network.Simple.TCP (connect)
import Capnp     (def, defaultLimit)
import Capnp.Rpc (ConnConfig(..), handleConn, socketTransport, wait, (?))

import Ltl.Parser
import Afa (SimplificationResult(..), preprocess)
import Afa.Convert.Ltle
import Afa.Convert.CnfAfa
import Afa.Convert.Capnp.CnfAfa
import Capnp.Gen.Schema.CnfAfaRpc.Pure

main :: IO ()
main = do
  ltls <- lines<$> getContents
  let afas = map (second preprocess . ltleToAfa . parseLtl) ltls

  connect "localhost" "4000" $ \(sock, _addr) ->
    handleConn (socketTransport sock defaultLimit) def
        { withBootstrap = Just $ \_sup client ->
            void$ forM afas$ \case
              (_, NonPositiveStates) -> putStrLn "NonPositiveStates"
              (_, EmptyLang) -> putStrLn "EmptyLang (detected in preprocessing)"
              (_, NonEmptyLang) -> putStrLn "NonEmptyLang (detected in preprocessing)"
              (varCount, UndecidedEmptiness afa) -> do
                let cnfafa = serializeCnfAfa$ tseytin varCount afa
                Loader'load'results{loadedModel} <- wait =<<
                  loader'load (Loader client) ? def{model=cnfafa}
                LoadedModel'solve'results{empty} <- wait =<<
                  loadedModel'solve loadedModel ? def
                putStrLn$ if empty then "EmptyLang" else "NonEmptyLang"
        }
