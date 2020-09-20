{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ExtendedDefaultRules #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}

module Afa.Convert.Pretty (parsePrettyAfa, exportPrettyAfa) where

import Text.Parsec.Pos
import Text.InterpolatedString.Perl6 (qq)
import GHC.Exts (sortWith)
import Data.Foldable
import Data.Array
import Data.Semigroup
import Data.List
import Data.Char
import Control.Monad
import Data.Either
import Text.Parsec hiding (token)
import Data.Composition ((.:))
import Afa
import qualified Afa.TreeDag.Patterns.Builder as TDB
import qualified Afa.TreeDag.Patterns as TDI
import Data.Functor.Foldable hiding (fold)
import qualified Data.Map.Strict as M
import Data.Functor.Foldable.Dag.Pure (cataScan)
import Data.Functor.Foldable.Dag.Monadic (fromCataScanMAlg)

parsePrettyAfa :: String -> (Int, Afa)
parsePrettyAfa str = case runWParser (many statement) str of
  Right statements -> case semanticAnalysis statements of
    Right afa -> afa
    Left err -> error err
  Left err -> error$ show err

exportPrettyAfa :: Int -> Afa -> String
exportPrettyAfa varCount (Afa terms states) = intercalate "\n"$ concat
  [ map (\i -> [qq|var var{i}|]) [0..varCount - 1]
  , map (\(i, t) -> [qq|term term{i} {cata show_alg t}|])$ assocs terms
  , map (\(i, q) -> [qq|state state{i} term{q}|])$ assocs states
  ]
  where
  show_alg :: TDI.Term String -> String
  show_alg TDI.LTrue = "1"
  show_alg TDI.LFalse = "0"
  show_alg (TDI.Var ix) = [qq|var{ix}|]
  show_alg (TDI.State ix) = [qq|state{ix}|]
  show_alg (TDI.Ref ix) = [qq|term{ix}|]
  show_alg (TDI.And xs) = [qq|(& {unwords xs})|]
  show_alg (TDI.Or xs) = [qq|(| {unwords xs})|]
  show_alg (TDI.Not x) = [qq|(! {x})|]

type WParser a = Parsec [String] () a
runWParser p = runParser p () "parser" . tokenizer

tokenizer :: String -> [String]
tokenizer str = case runParser (spaces *> many parseToken <* eof) () "tokenizer" str of
  Right tokens -> tokens
  Left err -> error$ show err
  where
  parseToken = (many1 alphaNum <|> ((:[]) <$> satisfy (not . isSpace))) <* spaces

data Term rec
  = LTrue
  | LFalse
  | Iden String
  | And [rec]
  | Or [rec]
  | Not rec
  deriving (Functor, Foldable, Traversable)

data Statement
  = VarDef String
  | TermDef String (Fix Term)
  | StateDef String (Fix Term)

tsatisfy :: (Stream s m String) => (String -> Bool) -> ParsecT s u m String
tsatisfy p = tokenPrim id (\pos c _ -> updatePosString pos c)
  (\c -> if p c then Just c else Nothing)

identifier :: (Stream s m String) => ParsecT s u m String
identifier = tsatisfy (isAlphaNum . head)

token :: (Stream s m String) => String -> ParsecT s u m String
token str = tsatisfy (== str)

statement :: WParser Statement
statement = foldr1 (<|>)
  [ VarDef <$> (token "var" *> identifier)
  , TermDef <$> (token "term" *> identifier) <*> term
  , StateDef <$> (token "state" *> identifier) <*> term
  ]

term :: WParser (Fix Term)
term = between (token "(") (token ")") operator
  <|> (fromAlphaNums <$> identifier)
  where
  fromAlphaNums "1" = Fix LTrue
  fromAlphaNums "0" = Fix LFalse
  fromAlphaNums iden = Fix$ Iden iden

  operator = foldr1 (<|>)
    [ Fix . And <$> (token "&" *> many1 term)
    , Fix . Or <$> (token "|" *> many1 term)
    , Fix . Not <$> (token "!" *> term)
    ]

semanticAnalysis :: [Statement] -> Either String (Int, Afa)
semanticAnalysis statements = case nameClashes of
  [] -> do
    terms_unsorted <- listArray (0, termCount - 1)<$>
      mapM (cata (fromCataScanMAlg mapTerm_alg) . snd) terms

    states <- mapM (cata (fromCataScanMAlg mapTerm_alg) . snd) states

    let topos = cataScan (succ . fold) terms_unsorted :: Array Int (Max Word)
        termIxMap = listArray (0, termCount - 1)$ sortWith (topos!) [0..termCount - 1]
        terms_unsorted' = (fmap.fmap) (termIxMap!) terms_unsorted
        terms' = listArray (0, termCount + stateCount - 1)$
          map (terms_unsorted'!) (elems termIxMap)
          ++ (fmap.fmap) (termIxMap!) states

    return$ (varCount,)$ Afa
      { terms = terms'
      , states = listArray (0, stateCount - 1) [termCount..]
      }

  clashes -> Left$ "Clashing identifiers: " ++ unwords clashes

  where
  names = map (\case VarDef n -> n; TermDef n _ -> n; StateDef n _ -> n) statements
  nameClashes = [name | (name:_:_) <- group$ sort names]

  vars = [name | VarDef name <- statements]
  states = [(name, term) | StateDef name term <- statements]
  terms = [(name, term) | TermDef name term <- statements]

  varNameToIx = M.fromList$ zip vars [0..]
  stateNameToIx = M.fromList$ zip (map fst states) [0..]
  termNameToIx = M.fromList$ zip (map fst terms) [0..]

  varCount = length vars
  termCount = length terms
  stateCount = length states

  mapTerm_alg LTrue = Right TDB.LTrue
  mapTerm_alg LFalse = Right TDB.LFalse
  mapTerm_alg (And xs) = Right$ TDB.And xs
  mapTerm_alg (Or xs) = Right$ TDB.Or xs
  mapTerm_alg (Not x) = Right$ TDB.Not x
  mapTerm_alg (Iden str) =
    case map (M.lookup str) [varNameToIx, stateNameToIx, termNameToIx] of
      [Just ix, _, _] -> Right$ TDB.Var ix
      [_, Just ix, _] -> Right$ TDB.State ix
      [_, _, Just ix] -> Right$ TDB.Ref ix
      _ -> Left$ "Unknown identifier: " ++ str
