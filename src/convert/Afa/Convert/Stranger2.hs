{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Afa.Convert.Stranger2 where

import qualified Afa.Convert.PrettyStranger2 as Pretty
import Afa.Finalful.STerm
import Control.Applicative (Alternative ((<|>)))
import Control.Monad.Free
import qualified Control.Monad.State.Strict as MS
import Data.Attoparsec.Expr
import Data.Attoparsec.Text
import Data.Char (isAlphaNum, isSpace)
import Data.Composition ((.:))
import Data.Functor ((<&>))
import qualified Data.Text as T
import Data.Traversable (for)
import Debug.Trace

data VarT = DeBruijn Int | Ctx STermStr STermStr | RealVar T.Text
type STermStr = Free (Term T.Text VarT) T.Text

parseExpr :: T.Text -> STermStr
parseExpr str = case parse expr $ T.filter (not . isSpace) str of
  Fail i ctxs err -> error $ show (i, ctxs, err)
  Partial p -> case p "" of
    Fail i ctxs err -> error $ show (i, ctxs, err)
    Partial _ -> error "expr double partial"
    Done _ x -> x
  Done _ x -> x

expr :: Parser STermStr
expr = buildExpressionParser table term <?> "expression"
  where
    table =
      [ [Prefix $ Free . Not <$ (char '¬' <|> char '!')]
      , [Infix (Free .: And <$ (char '∧' <|> char '&')) AssocLeft]
      , [Infix (Free .: Or <$ (char '∨' <|> char '|')) AssocLeft]
      ]

term :: Parser STermStr
term =
  "(" *> expr <* ")"
    <|> (Free . State <$> ("s_" *> decimal <&> T.pack . show))
    -- <|> (Pure <$> ("f_" *> decimal <&> T.pack . show))
    <|> (Free LTrue <$ "True")
    <|> (Free LFalse <$ "False")
    <|> (Free . Var .: Ctx <$> (char '[' *> expr <* char ']') <*> expr)
    <|> (Free . Var . DeBruijn <$> try (char '_' *> decimal))
    <|> (Free . Var . RealVar <$> takeWhile1 (\case '_' -> True; x -> isAlphaNum x))
    <?> "expected a term"

parseDefinitions :: T.Text -> [Pretty.Definition]
parseDefinitions str = flip Pretty.parseWhole str do
  qcount <- string "numOfStates:" *> skipSpace *> decimal <* endOfLine
  init <- string "initialStates:" *> skipSpace *> (parseExpr <$> takeTill isEndOfLine <* endOfLine)
  final <- string "finalStates:" *> skipSpace *> (parseExpr <$> takeTill isEndOfLine <* endOfLine)

  -- fcount :: Int <- (string "numOfTransitionSubformulae:" *> skipSpace *> decimal <* endOfLine) <|> pure 0
  -- formulae <-
  --   if fcount /= 0
  --     then do
  --       string "TransitionSubformulae:" *> skipSpace
  --       for [0 .. fcount - 1] $ \i ->
  --         "formula" *> skipSpace *> string (T.pack $ show i ++ ":") *> endOfLine
  --           *> (parseExpr <$> takeTill isEndOfLine <* endOfLine)
  --     else return []

  string "States:" *> skipSpace
  states <- for [0 .. qcount - 1] $ \i ->
    "state" *> skipSpace *> string (T.pack $ show i ++ ":") *> endOfLine
      *> (parseExpr <$> takeTill isEndOfLine <* endOfLine)

  let ((init', final', states'), (fCount, _, formulae)) = flip MS.runState (0, [], []) do
        (,,) <$> applySharing init <*> applySharing final <*> mapM applySharing states

  let result =
        Pretty.DInitialStates init' :
        Pretty.DFinalStates final' :
        zipWith (\i f -> Pretty.DFormula (T.pack $ show i) f) [fCount - 1, fCount - 2 ..] formulae
          ++ zipWith (\i f -> Pretty.DState (T.pack $ show i) f) [0 :: Int ..] states'
  return result

applySharing :: STermStr -> MS.State (Int, [Int], [Pretty.STermStr]) Pretty.STermStr
applySharing (Pure x) = return $ Pure x
applySharing (Free LTrue) = return $ Free LTrue
applySharing (Free LFalse) = return $ Free LFalse
applySharing (Free (State q)) = return $ Free (State q)
applySharing (Free (Not x)) = Free . Not <$> applySharing x
applySharing (Free (And x y)) = Free .: And <$> applySharing x <*> applySharing y
applySharing (Free (Or x y)) = Free .: Or <$> applySharing x <*> applySharing y
applySharing (Free (Var (RealVar v))) = return $ Free (Var v)
applySharing (Free (Var (Ctx ctx expr))) = do
  (_, ctxs, _) <- MS.get
  ctx' <- applySharing ctx
  (i, _, formulae) <- MS.get
  MS.put (i + 1, i : ctxs, ctx' : formulae)
  applySharing expr
applySharing (Free (Var (DeBruijn i))) = do
  (_, ctxs, _) <- MS.get
  return $ Pure (T.pack $ show $ ctxs !! i)
