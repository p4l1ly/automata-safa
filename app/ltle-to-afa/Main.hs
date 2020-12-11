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
import Afa.Bool
import Afa
import Data.Time.Clock.POSIX (getPOSIXTime)

data Opts = Opts
  { readers :: Fix (Compose IO (ListF (BoolAfaUnswallowed Int)))
  , writers :: [BoolAfaUnswallowed Int -> IO ()]
  }

optParser :: Parser Opts
optParser = Opts
  <$> option
    (eitherReader$ \case
      "ltl" -> Right$ flip ana ()$ \_ -> Compose$
        (getLine <&> parseLtl <&> ltleToUnswallowedAfa <&> flip Cons ())
        `catch` \(SomeException _) -> return Nil
      "afa" -> undefined
      x -> Left$ "expected one of: ltl; got " ++ x
    )
    ( long "input"
      <> short 'i'
      <> help "Input format, one of: ltl"
    )
  <*> option
    (eitherReader$ \case
      (break (== ':') -> ("afa", ':':outdir)) -> Right$ flip map [0..]$ \i afa ->
        withFile (outdir ++ "/" ++ show i) WriteMode$ hWriteAfa afa
      x -> Left$ "expected afa:<path>; got " ++ x
    )
    ( long "output"
      <> short 'o'
      <> help "Output format, afa:<path>"
    )

main :: IO ()
main = do
  (Opts readers writers) <- execParser$ info (optParser <**> helper)$
    fullDesc
    <> progDesc
      "Convert LTLe to a symbolic alternating finite automaton, possibly \
      \preprocess the automaton and output it somewhere further."
    <> header "ltle-to-afa: symbolic alternating finite automata preprocessing"

  ($ (writers, readers))$ hylo
    ( \(Compose (writer, Compose action)) ->
      action >>= \case
        Nil -> return ()
        Cons bafa0 rec -> do
          tic <- getPOSIXTime
          let bafa = bafa0{afa = reorderStates$ afa bafa0}
          writer bafa
          toc <- getPOSIXTime
          putStrLn$ intercalate "\t"
            [ show (floor$ 1000*(toc - tic))
            , show$ rangeSize$ bounds$ states$ afa bafa
            , show$ rangeSize (bounds$ terms$ afa bafa) + rangeSize (bounds$ boolTerms bafa)
            , show$ sum (fmap length$ terms$ afa bafa) + sum (fmap length$ boolTerms bafa)
            ]
          rec
    )
    ( \(writer:writers, Fix readers) -> Compose (writer, fmap (writers,) readers) )
