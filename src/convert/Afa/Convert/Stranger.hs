{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveGeneric #-}

module Afa.Convert.Stranger where

import GHC.Generics hiding (Prefix, Infix)
import Data.Functor.Classes
import Generic.Data (Generically1(..))
import Generic.Data.Orphans ()

import Data.Char
import Text.Parsec hiding (State)
import Text.Parsec.Expr
import Text.Parsec.Token
import Data.Fix
import Data.Composition ((.:))
import Data.Traversable

type WParser a = Parsec String () a
runWParser p = runParser p () ""

parseExpr str = let Right x = runParser expr () ""$ filter (not . isSpace) str in x

afa :: WParser (Int, Fix Term, Fix Term, [Fix Term])
afa = do
  qcount <- string "numOfStates:" *> spaces *> (read <$> many1 digit) <* newline
  init <- string "initialStates:" *> spaces *> (parseExpr <$> manyTill anyChar newline) 
  final <- string "finalStates:" *> spaces *> (parseExpr <$> manyTill anyChar newline) 
  string "States:" *> manyTill space newline
  states <- for [0..qcount - 1]$ \i ->
    string "state" *> spaces *> string (show i ++ ":") *> newline
    *> (parseExpr <$> manyTill anyChar newline) 
  return (qcount, init, final, states)

data Term rec
  = LTrue
  | LFalse
  | State Int
  | Var String
  | Not rec
  | And rec rec
  | Or rec rec
  deriving (Functor, Foldable, Traversable, Show, Eq, Generic, Generic1)
  deriving (Eq1, Show1) via (Generically1 Term)

expr :: WParser (Fix Term)
expr = buildExpressionParser table term <?> "expression" where
  table =
    [ [Prefix$ Fix . Not <$ char '¬']
    , [Infix (Fix .: And <$ char '∧') AssocLeft]
    , [Infix (Fix .: Or <$ char '∨') AssocLeft]
    ]

term :: WParser (Fix Term)
term = between (char '(') (char ')') expr
   <|> (Fix . State . read <$> (string "s_" *> many1 digit))
   <|> (Fix LTrue <$ string "True")
   <|> (Fix LFalse <$ string "False")
   <|> (Fix . Var <$> many1 (alphaNum <|> char '_'))
   <?> "expected a term"
