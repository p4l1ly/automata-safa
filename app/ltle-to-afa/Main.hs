{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Main where

import Debug.Trace

import Options.Applicative
import Control.Monad
import Control.Concurrent.STM
import Control.Concurrent
import Data.Maybe
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
import qualified Afa.Convert.Capnp.Separated as SepCap
import qualified Afa.Convert.Separated as Sep
import qualified Afa.Convert.Separated.Model as Sep
import Afa.Convert.CnfAfa (tseytin')
import Afa.Bool
import Afa hiding (simplifyAll)
import Afa.Ops.Compound
import Data.Time.Clock.POSIX (getPOSIXTime)
import System.Directory
import qualified Afa.Term.Mix as MTerm
import qualified Afa.Term.Bool as BTerm
import qualified Afa.Convert.Stranger as Stranger
import qualified Data.Text.IO as TIO

data Opts = Opts
  { readers :: Fix (Compose IO (ListF (String, BoolAfaUnswallowed Int)))
  , writers :: [String -> BoolAfaUnswallowed Int -> Either Bool ((Int, Int, Int), IO ())]
  }

dirReaders :: (Handle -> IO a) -> String -> Fix (Compose IO (ListF (String, a)))
dirReaders fileReader indir = Fix$ Compose$ do
  (sort . map read -> files0 :: [Int]) <- listDirectory indir
  reader (project files0) <&> \case
    Nil -> Nil
    Cons afa a -> Cons afa$ hoist (Compose . reader) a
  where
  reader Nil = return Nil
  reader (Cons file a) = do
    afa <- withFile (indir ++ "/" ++ show file) ReadMode fileReader
    return$ Cons (show file, afa) a

afaReaders :: String -> Fix (Compose IO (ListF (String, BoolAfaUnswallowed Int)))
afaReaders = dirReaders hReadAfa

strangerReaders :: String -> Fix (Compose IO (ListF (String, BoolAfaUnswallowed Int)))
strangerReaders = dirReaders$ \h -> TIO.hGetContents h <&> Stranger.parseAfa

arrSize :: Array Int a -> Int
arrSize = rangeSize . bounds

mtermNCount :: Array Int (MTerm.Term p q t) -> Int
mtermNCount arr = length$ ($ elems arr)$ filter$
  \case MTerm.And _ -> True; MTerm.Or _ -> True; _ -> False

btermNCount :: Array Int (BTerm.Term p t) -> Int
btermNCount arr = length$ ($ elems arr)$ filter$
  \case BTerm.And _ -> True; BTerm.Or _ -> True; _ -> False

edgeCount :: (Functor f, Foldable f, Foldable g) => f (g a) -> Int
edgeCount = sum . fmap length

afaCosts bafa = (qCount, nCount, eCount)
  where
  qafa = afa bafa
  qCount = arrSize$ states qafa
  nCount = btermNCount (boolTerms bafa) + mtermNCount (terms qafa)
  eCount = edgeCount (terms qafa) + edgeCount (boolTerms bafa)

sepAfaCosts sepafa = (qCount, nCount, eCount)
  where
  qCount = arrSize$ Sep.states sepafa
  nCount = btermNCount (Sep.aterms sepafa) + mtermNCount (Sep.qterms sepafa) +
    sum (Sep.states sepafa <&> length . filter (\(a, q) -> isJust a && isJust q))
  eCount = edgeCount (Sep.aterms sepafa) + edgeCount (Sep.qterms sepafa) +
    sum (Sep.states sepafa <&> length) +
    sum (Sep.states sepafa <&> (2*) . length . filter (\(a, q) -> isJust a && isJust q))

afaWriter outdir i (reorderStates' -> bafa) = 
  ( afaCosts bafa
  , withFile (outdir ++ "/" ++ i) WriteMode$ hWriteAfa bafa
  )

sepAfaWriter outdir i (Sep.reorderStates' -> sepafa) =
  ( sepAfaCosts sepafa
  , withFile (outdir ++ "/" ++ i) WriteMode$ SepCap.hWrite sepafa
  )

optParser :: Parser Opts
optParser = Opts
  <$> option
    ( eitherReader$ \case
      "ltl" -> Right$ flip ana 0$ \i -> Compose$
        ( getLine <&> parseLtl <&> ltleToUnswallowedAfa
          <&> (show i,) <&> flip Cons (i+1)
        )
        `catch` \(SomeException _) -> return Nil
      (break (== ':') -> ("afa", ':':indir)) -> Right$ afaReaders indir
      (break (== ':') -> ("stranger", ':':indir)) -> Right$ strangerReaders indir
      x -> Left$ "expected one of: ltl, afa:<path>; got " ++ x
    )
    ( long "input"
      <> short 'i'
      <> help "Input format: ltl, afa:<path>"
    )
  <*> option
    ( eitherReader$ \case
      (break (== ':') -> ("afa", ':':outdir)) ->
        Right$ repeat$ \i bafa ->
          Right$ afaWriter outdir i bafa
      (break (== ':') -> ("afaBasicSimp", ':':outdir)) ->
        Right$ repeat$ \i bafa ->
          simplifyAll bafa <&> afaWriter outdir i
      (break (== ':') -> ("afaSimpGoblinMincut", ':':outdir)) ->
        Right$ repeat$ \i bafa ->
          simpGoblinMincut bafa <&> afaWriter outdir i
      (break (== ':') -> ("afaSimpGoblin", ':':outdir)) ->
        Right$ repeat$ \i bafa ->
          simpGoblin bafa <&> afaWriter outdir i
      (break (== ':') -> ("afaSimpMincut", ':':outdir)) ->
        Right$ repeat$ \i bafa ->
          simpMincut bafa <&> afaWriter outdir i
      (break (== ':') -> ("cnfafa", ':':outdir)) ->
        Right$ repeat$ \i bafa ->
          Right$ (afaCosts bafa,)$
            withFile (outdir ++ "/" ++ i) WriteMode$ hWriteCnfAfa$ tseytin' bafa
      (break (== ':') -> ("sepafaExploding", ':':outdir)) ->
        Right$ repeat$ \i bafa ->
          let Just sepafa = Sep.mixedToSeparated bafa
                <|> Sep.mixedToSeparated bafa{ afa = Sep.separabilizeAfa$ afa bafa }
          in Sep.simplify sepafa <&> sepAfaWriter outdir i
      (break (== ':') -> ("sepafaDelaying", ':':outdir)) ->
        Right$ repeat$ \i bafa ->
          let Just sepafa = Sep.mixedToSeparated bafa
                <|> Sep.mixedToSeparated bafa{ afa = delayPredicates$ afa bafa }
          in Sep.simplify sepafa <&> sepAfaWriter outdir i
      x -> Left$ "expected one of: \
        \{afa,afaBasicSimp,cnfafa,sepafaExploding,sepafaDelaying}:<path>; got " ++ x
    )
    ( long "output"
      <> short 'o'
      <> help "Output format: \
        \{afa,afaBasicSimp,cnfafa,sepafaExploding,sepafaDelaying}:<path>"
    )

timeoutMicro = 500*1000000

main :: IO ()
main = do
  (Opts readers writers) <- execParser$ info (optParser <**> helper)$
    fullDesc
    <> progDesc
      "Convert LTLe to a symbolic alternating finite automaton, possibly \
      \preprocess the automaton and output it somewhere further."
    <> header "ltle-to-afa: symbolic alternating finite automata preprocessing"

  applyWritersAndReaders writers readers

applyWritersAndReaders (writer:writers) (Fix (Compose action)) = action >>= \case
  Nil -> return ()
  Cons (name, bafa) readers' -> do
    tic <- getPOSIXTime
    finishedVar <- registerDelay timeoutMicro
    resultVar <- newTVarIO Nothing
    threadId <- forkIO$
      case writer name bafa of
        Left result -> do
          atomically$ do
            writeTVar finishedVar True
            writeTVar resultVar$ Just$ Left result
        Right (sizes, write) -> do
          write
          atomically$ do
            writeTVar finishedVar True
            writeTVar resultVar$ Just$ Right sizes

    mresult <- atomically$ readTVar finishedVar >>= \case
      False -> retry
      _ -> readTVar resultVar

    toc <- getPOSIXTime

    when (isNothing mresult)$ killThread threadId

    let (qCount, nodeCount, edgeCount, result) = case mresult of
          Nothing -> (0, 0, 0, -2)
          Just (Left result) -> (0, 0, 0, if result then 1 else 0)
          Just (Right (qCount, nCount, eCount)) -> (qCount, nCount, eCount, -1)

    putStrLn$ intercalate "\t"
      [ name
      , show$ floor$ 1000*(toc - tic)
      , show qCount
      , show nodeCount
      , show edgeCount
      , show result
      ]

    hFlush stdout

    applyWritersAndReaders writers readers'
