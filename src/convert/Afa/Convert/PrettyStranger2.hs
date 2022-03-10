{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Afa.Convert.PrettyStranger2 where

import Afa.Finalful (BuildD, buildFree) -- TODO these are generic methods, they shouldn't be in Afa.Finalful
import Afa.Finalful.STerm (Term (..))
import Afa.Lib (listArray')
import Control.Applicative
import Control.Monad.Free
import Control.Monad.State.Strict
import Control.Monad.Trans (lift)
import Control.Monad.Writer.Strict
import Data.Array
import Data.Attoparsec.Expr
import Data.Attoparsec.Text
import qualified Data.Attoparsec.Text as Parsec
import Data.Char
import Data.Composition ((.:))
import qualified Data.HashMap.Strict as HM
import Data.List.NonEmpty (NonEmpty ((:|)))
import qualified Data.List.NonEmpty as NE
import Data.Monoid (Endo (..))
import Data.String.Interpolate.IsString
import qualified Data.Text as T
import qualified Data.Text.Read as TR
import Data.Traversable
import DepDict (DepDict ((:|:)))
import qualified DepDict as D
import Lift (Lift)
import Shaper
import TypeDict

parseWhole :: Parser a -> T.Text -> a
parseWhole parser str = case parse parser str of
  Fail i ctxs err -> error $ show (i, ctxs, err)
  Partial p -> case p "" of
    Fail i ctxs err -> error $ show (i, ctxs, err)
    Partial _ -> error "expr double partial"
    Done _ x -> x
  Done _ x -> x

parseDefinitions :: T.Text -> [Definition]
parseDefinitions str = parseWhole parser str'
  where
    str' = T.filter (not . isSpace) str
    parser =
      many $
        parseOne
          <$> (char '@' *> Parsec.takeWhile (/= ':') <* char ':')
          <*> Parsec.takeWhile (/= '@')

type ParseGenericD d m = ParseGenericD_ d m (ParseGenericA d) [g|r|]
type ParseGenericA d =
  Name "buildTreeD" (Name "build" [d|buildTree|] :+: d)
    :+: End
type ParseGenericD_ d m (d' :: TypeDict) (r :: *) =
  D.Name "aliases" (r ~ [g|r|], d' ~ ParseGenericA d)
    :|: D.Name "" (MonadFn' [d|shareTree|] r r m)
    :|: D.Name "" (BuildD [g'|buildTreeD|] (Term T.Text T.Text) r m)
    :|: D.End
parseGeneric ::
  forall d m r d'.
  D.ToConstraint (ParseGenericD_ d m d' r) =>
  T.Text ->
  m (r, r, (Int, Int -> T.Text, Int -> r, T.Text -> Int))
parseGeneric str = do
  (initR, finalR, stateRs) <- flip evalStateT HM.empty $ do
    (,,) <$> convert init <*> convert final <*> mapM convert states
  let stateList = HM.toList stateRs
      arr = listArray (0, HM.size stateRs - 1) stateList
      stateNames = map fst stateList
      state2ix = HM.fromList $ zip stateNames [0 ..]
  return
    ( initR
    , finalR
    ,
      ( rangeSize $ bounds arr
      , fst . (arr !)
      , snd . (arr !)
      , (state2ix HM.!)
      )
    )
  where
    (init, final, formulae, states) = orize $ parseDefinitions str
    convert f = mapM fRec f >>= buildFree @(LiftTags [g'|buildTreeD|])
    fRec name =
      gets (HM.!? name) >>= \case
        Just Nothing -> error $ "cycle " ++ T.unpack name
        Just (Just r) -> return r
        Nothing -> do
          modify $ HM.insert name Nothing
          (f :: Free (Term T.Text T.Text) r) <- mapM fRec (formulae HM.! name)
          buildFree @(LiftTags [g'|buildTreeD|]) f >>= monadfn @(Lift [d|shareTree|])

type STermStr = Free (Term T.Text T.Text) T.Text

data Definition
  = DInitialStates {dterm :: STermStr}
  | DFinalStates {dterm :: STermStr}
  | DFormula {name :: T.Text, dterm :: STermStr}
  | DState {name :: T.Text, dterm :: STermStr}

parseOne :: T.Text -> T.Text -> Definition
parseOne name value = case T.uncons name of
  Just ('f', name') -> DFormula name' $ parseWhole expr value
  Just ('s', name') -> DState name' $ parseWhole expr value
  Just ('k', keyword) -> case keyword of
    "InitialFormula" -> DInitialStates $ parseWhole expr value
    "FinalFormula" -> DFinalStates $ parseWhole expr value
    _ -> error [i|unknown keyowrd #{keyword}|]
  Just (t, _) -> error [i|unknown type #{t}|]
  Nothing -> error "empty identifier"

expr :: Parser STermStr
expr = buildExpressionParser table term <?> "expression"
  where
    table =
      [ [Prefix $ Free . Not <$ char '!']
      , [Infix (Free .: And <$ char '&') AssocLeft]
      , [Infix (Free .: Or <$ char '|') AssocLeft]
      ]

identifier = Parsec.takeWhile (\case '_' -> True; x -> isAlphaNum x)

term :: Parser STermStr
term =
  "(" *> expr <* ")"
    <|> (Free . State <$> ("s" *> identifier))
    <|> (Pure <$> ("f" *> identifier))
    <|> (Free LTrue <$ "True")
    <|> (Free LFalse <$ "False")
    <|> (Free . Var <$> identifier)
    <?> "expected a term"

recur :: ((a -> b) -> a -> b) -> a -> b
recur fn = rec where rec = fn rec

orize :: [Definition] -> (STermStr, STermStr, HM.HashMap T.Text STermStr, HM.HashMap T.Text STermStr)
orize defs =
  ( foldr (Free .: Or) (Free LFalse) $ init `appEndo` []
  , foldr (Free .: Or) (Free LFalse) $ final `appEndo` []
  , HM.fromListWith (Free .: Or) $ formulae `appEndo` []
  , HM.fromListWith (Free .: Or) $ states `appEndo` []
  )
  where
    (init, final, states, formulae) = execWriter $
      for defs $ \case
        DFormula name dterm -> tell (mempty, mempty, mempty, Endo ((name, dterm) :))
        DState name dterm -> tell (mempty, mempty, Endo ((name, dterm) :), mempty)
        DInitialStates dterm -> tell (Endo (dterm :), mempty, mempty, mempty)
        DFinalStates dterm -> tell (mempty, Endo (dterm :), mempty, mempty)

-- formatAfa :: BoolAfaUnswallowed Int -> T.Text
-- formatAfa (swallow -> BoolAfa bterms (Afa mterms states init)) =
--   T.unlines $
--     [ [i|@kInitialFormula: s#{init}|]
--     , let finals = map (\q -> [i|!s#{q}|]) $ Data.Array.indices states
--        in [i|@kFinalFormula: #{T.intercalate " & " finals}|]
--     ]
--       ++ map (\(j, t) -> [i|@fBool#{j}: #{fromBTermTree t}|]) (assocs bterms)
--       ++ map (\(j, t) -> [i|@fMix#{j}: #{fromMTermTree t}|]) (assocs mterms)
--       ++ map (\(j, t) -> [i|@s#{j}: #{fromMTermTree t}|]) (assocs states)
--
-- fromBTermTree :: BoolTermIFree Int -> T.Text
-- fromBTermTree = iter fromBTerm . fmap (\j -> [i|fBool#{j}|])
--
-- fromBTerm :: BTerm.Term Int T.Text -> T.Text
-- fromBTerm BTerm.LTrue = "kTrue"
-- fromBTerm BTerm.LFalse = "kFalse"
-- fromBTerm (BTerm.Predicate p) = [i|a#{p}|]
-- fromBTerm (BTerm.Not x) = [i|!#{x}|]
-- fromBTerm (BTerm.And (x :| [])) = x
-- fromBTerm (BTerm.Or (x :| [])) = x
-- fromBTerm (BTerm.And xs) = [i|(#{T.intercalate " & "$ NE.toList xs})|]
-- fromBTerm (BTerm.Or xs) = [i|(#{T.intercalate " | "$ NE.toList xs})|]
--
-- fromMTermTree :: MixTermIFree (BoolTermIFree Int) -> T.Text
-- fromMTermTree = iter fromMTerm . fmap (\j -> [i|fMix#{j}|])
--
-- fromMTerm :: MTerm.Term (BoolTermIFree Int) Int T.Text -> T.Text
-- fromMTerm MTerm.LTrue = "kTrue"
-- fromMTerm (MTerm.Predicate p) = fromBTermTree p
-- fromMTerm (MTerm.State q) = [i|s#{q}|]
-- fromMTerm (MTerm.And (x :| [])) = x
-- fromMTerm (MTerm.Or (x :| [])) = x
-- fromMTerm (MTerm.And xs) = [i|(#{T.intercalate " & "$ NE.toList xs})|]
-- fromMTerm (MTerm.Or xs) = [i|(#{T.intercalate " | "$ NE.toList xs})|]
