module Ltl.Parser (parseLtl) where

import Data.Char
import Control.Monad
import Data.Either
import Text.Parsec
import Data.Composition ((.:))
import Data.Fix

import Ltl

type WParser a = Parsec String () a
runWParser p = runParser p () "" . filter (not . isSpace)

parseLtl :: String -> Fix Ltl
parseLtl str = case runWParser term str of
  Right x -> x
  Left err -> error $ show err

operator :: WParser (Fix Ltl)
operator = (Fix . And <$> (char '&' *> many1 term))
       <|> (Fix . Or  <$> (char '|' *> many1 term))
       <|> (Fix . Not <$> (char '!' *> term))
       <|> (Fix . Next <$> (char 'X' *> term))
       <|> (Fix . Globally <$> (char 'G' *> term))
       <|> (Fix . Finally <$> (char 'F' *> term))
       <|> (Fix .: Until <$> (char 'U' *> term) <*> term)
       <|> (Fix .: WeakUntil <$> (char 'W' *> term) <*> term)
       <|> (Fix .: Release <$> (char 'R' *> term) <*> term)

term :: WParser (Fix Ltl)
term = between (char '(') (char ')') operator
   <|> (Fix . Var . read <$> (char 'a' *> many1 digit))
   <|> (Fix LTrue <$ char 't')
   <|> (Fix LFalse <$ char 'f')
