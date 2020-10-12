{-# LANGUAGE NamedFieldPuns #-}

import System.Environment
import System.Directory
import System.IO
import Control.Monad.Primitive (touch)
import Control.Monad

import qualified Capnp.Gen.Schema.SeparatedAfaRpc.Pure as SepRpc
import qualified Capnp.Gen.Schema.LoadedModelRpc.Pure as Rpc

import Capnp (hGetValue, defaultLimit, def)
import Capnp.Rpc (ConnConfig(..), handleConn, socketTransport, wait, (?))
import Network.Simple.TCP (connect)

main :: IO ()
main = do
  [path] <- getArgs
  files <- listDirectory path
  checkDAntoni$ map ((path ++ "/") ++) files


checkDAntoni :: [String] -> IO ()
checkDAntoni files = connect "localhost" "4001" $ \(sock, _addr) ->
  handleConn (socketTransport sock defaultLimit) def
    { maxExports = 100000
    , debugMode = True
    , withBootstrap = Just $ \sup client ->
        forM_ (zip [0..] files)$ \(i, file) ->
          withFile file ReadMode$ \h -> do
            afa <- hGetValue h defaultLimit

            SepRpc.Loader'load'results{SepRpc.loadedModel} <- wait =<<
              SepRpc.loader'load (SepRpc.Loader client) ? def{SepRpc.model=afa}

            Rpc.ModelChecking'solve'results time result <- wait =<<
              Rpc.modelChecking'solve loadedModel ? def

            let msg = show time ++ " " ++
                  case result of
                    Rpc.ModelChecking'Result'empty -> "EmptyLang"
                    Rpc.ModelChecking'Result'nonempty -> "NonEmptyLang"
                    Rpc.ModelChecking'Result'cancelled -> "ModelCheckingCancelled"

            putStrLn$ show i ++ " " ++ msg
    }
