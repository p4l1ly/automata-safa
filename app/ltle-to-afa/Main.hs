{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Main where

import Options.Applicative

import Data.List
import Data.Array
import Control.Exception
import Data.Fix (Fix(..))
import Data.Functor.Base
import Data.Functor.Foldable
import Data.Functor.Compose
import Data.Functor
import System.IO
import Ltl.Parser
import Afa.Convert.Ltle
import Afa.Convert.Capnp.Afa
import Afa.Convert.Capnp.CnfAfa (hWriteCnfAfa)
import Afa.Convert.CnfAfa (tseytin')
import Afa.Bool
import Afa
import Data.Time.Clock.POSIX (getPOSIXTime)
import System.Directory

data Opts = Opts
  { readers :: Fix (Compose IO (ListF (BoolAfaUnswallowed Int)))
  , writers :: [BoolAfaUnswallowed Int -> IO ()]
  , preprocessor :: BoolAfaUnswallowed Int -> Either Bool (BoolAfaUnswallowed Int)
  }

afaReaders :: String -> Fix (Compose IO (ListF (BoolAfaUnswallowed Int)))
afaReaders indir = Fix$ Compose$ do
  (sort . map read -> files0 :: [Int]) <- listDirectory indir
  reader (project files0) <&> \case
    Nil -> Nil
    Cons afa a -> Cons afa$ hoist (Compose . reader) a
  where
  reader Nil = return Nil
  reader (Cons file a) = do
    afa <- withFile (indir ++ "/" ++ show file) ReadMode hReadAfa
    return$ Cons afa a

optParser :: Parser Opts
optParser = Opts
  <$> option
    ( eitherReader$ \case
      "ltl" -> Right$ flip ana ()$ \_ -> Compose$
        (getLine <&> parseLtl <&> ltleToUnswallowedAfa <&> flip Cons ())
        `catch` \(SomeException _) -> return Nil
      (break (== ':') -> ("afa", ':':indir)) -> Right$ afaReaders indir
      x -> Left$ "expected one of: ltl, afa:<path>; got " ++ x
    )
    ( long "input"
      <> short 'i'
      <> help "Input format: ltl, afa:<path>"
    )
  <*> option
    ( eitherReader$ \case
      (break (== ':') -> ("afa", ':':outdir)) -> Right$ flip map [0..]$ \i afa ->
        withFile (outdir ++ "/" ++ show i) WriteMode$ hWriteAfa afa
      (break (== ':') -> ("cnfafa", ':':outdir)) -> Right$ flip map [0..]$ \i afa ->
        withFile (outdir ++ "/" ++ show i) WriteMode$ hWriteCnfAfa$ tseytin' afa
      x -> Left$ "expected afa:<path>; got " ++ x
    )
    ( long "output"
      <> short 'o'
      <> help "Output format: afa:<path>"
    )
  <*> option
    ( eitherReader$ \case
      "none" -> Right Right
      "basic" -> Right simplifyAll
    )
    ( long "preprocess"
      <> short 'p'
      <> value Right
      <> help "Preprocessor: none, basic"
    )

arrSize :: Ix i => Array i a -> Int
arrSize = rangeSize . bounds

edgeCount :: (Functor f, Foldable f, Foldable g) => f (g a) -> Int
edgeCount = sum . fmap length

main :: IO ()
main = do
  (Opts readers writers preprocessor) <- execParser$ info (optParser <**> helper)$
    fullDesc
    <> progDesc
      "Convert LTLe to a symbolic alternating finite automaton, possibly \
      \preprocess the automaton and output it somewhere further."
    <> header "ltle-to-afa: symbolic alternating finite automata preprocessing"

  ($ (writers, readers))$ hylo
    ( \(Compose (writer, Compose action)) ->
      action >>= \case
        Nil -> return ()
        Cons bafa rec -> do
          tic <- getPOSIXTime
          case preprocessor bafa of
            Left result -> do
              toc <- getPOSIXTime
              putStrLn$ intercalate "\t"
                [ show$ floor$ 1000*(toc - tic)
                , "0"
                , "0"
                , "0"
                , if result then "1" else "0"
                ]
            Right bafa0 -> do
              let bafa = bafa0{afa = reorderStates$ afa bafa0}
              let qafa = afa bafa
              writer bafa
              toc <- getPOSIXTime
              putStrLn$ intercalate "\t"
                [ show$ floor$ 1000*(toc - tic)
                , show$ arrSize$ states qafa
                , show$ arrSize (terms qafa) + arrSize (boolTerms bafa)
                , show$ edgeCount (terms qafa) + edgeCount (boolTerms bafa)
                , "-1"
                ]
          rec
    )
    ( \(writer:writers, Fix readers) -> Compose (writer, fmap (writers,) readers) )
