{-# LANGUAGE NamedFieldPuns #-}

import Control.Monad
import Control.Monad.Primitive (touch)
import Data.List
import System.Directory
import System.Environment
import System.IO

import qualified Capnp.Gen.Schema.LoadedModelRpc.Pure as Rpc
import qualified Capnp.Gen.Schema.SeparatedAfaRpc.Pure as SepRpc

import Capnp (def, defaultLimit, hGetValue)
import Capnp.Rpc (ConnConfig (..), handleConn, socketTransport, wait, (?))
import Network.Simple.TCP (connect)

main :: IO ()
main = do
  [path] <- getArgs
  files <- listDirectory path
  let files' = sort $ map read files :: [Int]
  checkDAntoni $ map ((path ++ "/") ++) $ map show files'

checkDAntoni :: [String] -> IO ()
checkDAntoni files = connect "localhost" "4001" $ \(sock, _addr) ->
  handleConn
    (socketTransport sock defaultLimit)
    def
      { maxExports = 100000
      , debugMode = True
      , withBootstrap = Just $ \sup client ->
          forM_ files $ \file ->
            withFile file ReadMode $ \h -> do
              afa <- hGetValue h defaultLimit

              SepRpc.Loader'load'results{SepRpc.loadedModel} <-
                wait
                  =<< SepRpc.loader'load (SepRpc.Loader client) ? def{SepRpc.model = afa}

              Rpc.ModelChecking'solve'results time result <-
                wait
                  =<< Rpc.modelChecking'solve loadedModel ? def

              let msg =
                    show time ++ " "
                      ++ case result of
                        Rpc.ModelChecking'Result'empty -> "EmptyLang"
                        Rpc.ModelChecking'Result'nonempty -> "NonEmptyLang"
                        Rpc.ModelChecking'Result'cancelled -> "ModelCheckingCancelled"

              putStrLn $ file ++ " " ++ msg
      }
