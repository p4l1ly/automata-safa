{-# LANGUAGE TupleSections #-}
module Main where

import Options.Applicative
import Data.Semigroup ((<>))

import System.IO
import Ltl.Parser
import Afa.Ops.Preprocess (SimplificationResult(..), preprocess)
import Afa.Convert.Ltle
import Afa.Convert.Capnp.Afa
import Afa.Convert.Pretty
import Afa.Convert.Dot
import Afa.Convert.CnfAfa
import Afa.Convert.Capnp.CnfAfa
import Afa.Convert.Separated
import qualified Afa.Convert.Capnp.Separated as Separated
import System.Environment 

data OutputType
  = Dot
  | Pretty
  | Afa
  | CnfAfa
  | Separated
  deriving Read

data PreprocessType
  = Full
  | None
  deriving Read

optParser :: Parser (OutputType, PreprocessType)
optParser = (,)
  <$> option auto
     ( long "output"
    <> short 'o'
    <> value Afa
    <> help "Output format, one of: Dot, Pretty, Afa, CnfAfa, Separated"
     )
  <*> option auto
     ( long "preprocess"
    <> value Full
    <> help "Preprocessing method, one of: Full, None"
     )

main :: IO ()
main = do
  (outputType, preprocessType) <- execParser$ info (optParser <**> helper)
     ( fullDesc
    <> progDesc
      "convert LTLe to a symbolic alternating finite automaton, possibly preprocess \
      \the automaton and output it somewhere further"
    <> header "ltle-to-afa: symbolic alternating finite automata preprocessing"
     )
  let preprocess' = case preprocessType of Full -> preprocess; _ -> UndecidedEmptiness

  (varCount, afa) <- ltleToAfa . parseLtl <$> getContents

  case preprocess' afa of
    NonPositiveStates -> putStrLn "NonPositiveStates"
    EmptyLang -> putStrLn "EmptyLang"
    NonEmptyLang -> putStrLn "NonEmptyLang"
    UndecidedEmptiness afa' -> case outputType of
      Dot -> putStrLn$ toDot True afa'
      Pretty -> putStrLn$ exportPrettyAfa varCount afa'
      Afa -> hWriteAfa afa' stdout
      Main.CnfAfa -> hWriteCnfAfa (tseytin varCount afa') stdout
      Separated -> Separated.hWrite varCount (separate afa') stdout
