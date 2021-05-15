{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}

module Afa.Convert.Stranger where

import Debug.Trace

import GHC.Generics hiding (Prefix, Infix)
import Data.Functor.Classes
import Generic.Data (Generically1(..))
import Generic.Data.Orphans ()

import Control.Applicative
import Control.Monad.Free
import Control.Arrow
import Data.Functor.Compose
import Control.Lens
import Data.Char
import Data.Attoparsec.Text
import Data.Attoparsec.Expr
import Data.Fix hiding (cata)
import Data.Composition ((.:))
import Data.Traversable
import Control.RecursionSchemes.Lens
import Control.RecursionSchemes.Utils.HashCons
import Data.Array
import Data.List.NonEmpty (NonEmpty((:|)))
import qualified Data.List.NonEmpty as NE
import Data.Monoid (Endo(..))
import qualified Data.Text as T
import qualified Data.Text.Read as TR

import Afa.Lib.Free
import Afa
import Afa.Bool
import qualified Afa.Term.Bool as BTerm
import qualified Afa.Term.Mix as MTerm
import qualified Afa.Term.Bool.Simplify as BTerm
import qualified Afa.Term.Mix.Simplify as MTerm

parseExpr :: T.Text -> Fix STerm'
parseExpr str = case parse expr$ T.filter (not . isSpace) str of
  Fail i ctxs err -> error$ show (i, ctxs, err)
  Partial p -> case p "" of
    Fail i ctxs err -> error$ show (i, ctxs, err)
    Partial _ -> error "expr double partial"
    Done _ x -> x
  Done _ x -> x

parseAfa :: T.Text -> BoolAfaUnswallowed Int
parseAfa str = case parse afaParser str of
  Fail i ctxs err -> error$ show (i, ctxs, err)
  Partial p -> error "parseAfa: partial"
  Done _ x -> x

afaParser :: Parser (BoolAfaUnswallowed Int)
afaParser = do
  qcount <- string "numOfStates:" *> skipSpace *> decimal <* endOfLine
  init <- string "initialStates:" *> skipSpace *> (parseExpr <$> takeTill isEndOfLine <* endOfLine)
  final <- string "finalStates:" *> skipSpace *> (parseExpr <$> takeTill isEndOfLine <* endOfLine)
  string "States:" *> skipSpace
  states <- for [0..qcount - 1]$ \i ->
    "state" *> skipSpace *> string (T.pack$ show i ++ ":") *> endOfLine
    *> (parseExpr <$> takeTill isEndOfLine <* endOfLine) 
  return$ toAfa (qcount, init, final, states)

data STerm var rec
  = STrue
  | SFalse
  | SState !Int
  | SVar !var
  | SNot !rec
  | SAnd !rec !rec
  | SOr !rec !rec
  deriving (Functor, Foldable, Traversable, Show, Eq, Generic, Generic1)
  deriving (Eq1, Show1) via (Generically1 (STerm var))

type STerm' = STerm T.Text

expr :: Parser (Fix STerm')
expr = buildExpressionParser table term <?> "expression" where
  table =
    [ [Prefix$ Fix . SNot <$ char '¬']
    , [Infix (Fix .: SAnd <$ char '∧') AssocLeft]
    , [Infix (Fix .: SOr <$ char '∨') AssocLeft]
    ]

term :: Parser (Fix STerm')
term = "(" *> expr <* ")"
   <|> (Fix . SState <$> ("s_" *> decimal))
   <|> (Fix STrue <$ "True")
   <|> (Fix SFalse <$ "False")
   <|> (Fix . SVar <$> takeWhile1 (\case '_' -> True; x -> isAlphaNum x))
   <?> "expected a term"

toAfa :: (Int, Fix STerm', Fix STerm', [Fix STerm']) -> BoolAfaUnswallowed Int
toAfa (qcount, init, final, states) = unswallow BoolAfa
  { boolTerms = listArray (0, 3 + symCount)$
      [ Free BTerm.LTrue
      , Free BTerm.LFalse
      , Free$ BTerm.Predicate qcount
      , Free$ BTerm.Not$ Pure 2
      ] ++ map (Free . BTerm.Predicate) [qcount + 1 ..]
  , Afa.Bool.afa = Afa
      { terms = extendedStates
      , states = states'''
      , initState = init''
      }
  }
  where
  (simpleNonfinal, nonsimpleFinal) = finalSplitSimple qcount final

  nonsimpleFinal' = (nonsimpleFinal <&>)$ cataRecursive$ getCompose >>> \case
    [x] -> alg x
    xs -> Free$ BTerm.And$ NE.fromList$ xs <&> alg
    where
    alg = \case
      SState q
        | simpleNonfinal!q -> Pure 1
        | otherwise -> Free$ BTerm.Predicate q
      SNot x -> Free$ BTerm.Not x
      SAnd a b -> Free$ BTerm.And$ a :| [b]
      SOr a b -> Free$ BTerm.Or$ a :| [b]
      STrue -> Pure 0
      SFalse -> Pure 1

  nonsimpleFinal'' = nonsimpleFinal' <&> \fq -> Free$ MTerm.Or$
    Free (MTerm.And$ Free (MTerm.State$ qcount + 1) :| [Free$ MTerm.Predicate$ Pure 3])
    :| [Free$ MTerm.And$ Free (MTerm.Predicate$ Pure 2) :| [Free$ MTerm.Predicate fq]]

  qsInNonsimpleFinal = accumArray (\_ _ -> True) False (0, qcount - 1)$
    nonsimpleFinal' ^.. folded . \add -> (`freeModChilds` pure)$ \rec ->
      BTerm.modChilds BTerm.ChildMod
        { BTerm.lP = \p -> p <$ add (p, ()), BTerm.lT = rec }

  extendedStates = listArray (0, qcount - 1)$ [0..qcount - 1] <&> \i ->
    case (simpleNonfinal!i, qsInNonsimpleFinal!i) of
      (True, _) -> Free$ MTerm.And$
        Free (MTerm.State i) :| [Free$ MTerm.Predicate$ Pure 3]
      (_, False) -> Free$ MTerm.Or$
        Free (MTerm.State i) :| [Free$ MTerm.Predicate$ Pure 2]
      _ -> Free$ MTerm.Or$ Free (MTerm.State i) :|
        [Free$ MTerm.Predicate$ Free$ BTerm.And$ Pure 2 :| [Free$ BTerm.Predicate i]]

  (states'', length -> symCount) = runIdentity$ runHashConsTFrom 4$ for states'$
    (`freeModChilds` pure)$ modPT$
      cataT (freeTraversal traversed)$ \case
        Left x -> return$ Pure (x :: Int)
        Right (BTerm.Predicate (p :: T.Text)) -> Pure <$> hashCons' p
        Right x -> return$ Free$ case x of
          BTerm.LTrue -> BTerm.LTrue
          BTerm.LFalse -> BTerm.LFalse
          BTerm.And xs -> BTerm.And xs
          BTerm.Or xs -> BTerm.Or xs
          BTerm.Not x -> BTerm.Not x

  leftPure (Left x) = Pure x
  leftPure (Right x) = x

  freeJust (Free t) = Just t
  freeJust _ = Nothing

  modPT lP lT = MTerm.modChilds MTerm.pureChildMod{ MTerm.lT = lT, MTerm.lP = lP }

  flattenFree fn = either (return . Pure)$ return . Free . fn freeJust

  -- flattening highly improves performance
  states' = states <&> \x -> runIdentity$ convertTransition x & cataT
    (freeTraversal$ modPT$ cataT (freeTraversal traversed) (flattenFree BTerm.flatten0))
    (flattenFree MTerm.flatten0)

  convertTransition = (asRight .)$ cataRecursive$ \case
    STrue -> Left$ Pure 0
    SFalse -> Left$ Pure 1
    SState q -> Right$ Pure q
    SVar v -> Left$ Free$ BTerm.Predicate v
    SNot (Left x) -> Left$ Free$ BTerm.Not x
    SAnd (Left x) (Left y) -> Left$ Free$ BTerm.And$ x :| [y]
    SOr (Left x) (Left y) -> Left$ Free$ BTerm.Or$ x :| [y]
    SAnd x y -> Right$ Free$ MTerm.And$ NE.map asRight$ x :| [y]
    SOr x y -> Right$ Free$ MTerm.Or$ NE.map asRight$ x :| [y]

  asRight (Left x) = Free$ MTerm.Predicate x
  asRight (Right x) = x

  init' = ($ (convertTransition init >>= Free . MTerm.State))$
    (`freeAppMFun` id)$ \rec -> MTerm.appMTFun MTerm.mtfun0
      { MTerm.mtfunT = rec
      , MTerm.mtfunP = (`freeAppMFun` id)$ \rec2 -> BTerm.appMTFun BTerm.mtfun0
          { BTerm.mtfunP = error "variable in init formula", BTerm.mtfunT = rec2 }
      }

  (init'', states''') = case nonsimpleFinal'' of
    Just finalTrans ->
      ( qcount
      , listArray (0, qcount + 1)$ states'' ++
          [Free$ MTerm.And$ init' :| [Free$ MTerm.State$ qcount + 1], finalTrans]
      )
    Nothing -> case init' of
      Free (MTerm.State q) -> (q, listArray (0, qcount - 1) states'')
      _ -> (qcount, listArray (0, qcount)$ states'' ++ [init'])

finalSplitSimple :: Int -> Fix STerm' -> (Array Int Bool, Maybe (Fix (Compose [] STerm')))
finalSplitSimple qcount final =
  getSimples &&& getNonsimples$ ($ final)$ cataRecursive$ \case
    SState q -> Left (q, False)

    SNot (Left (q, False)) -> Left (q, True)
    SNot (Left (q, True))  -> Left (q, False)
    SNot x -> Right ([], Compose [SNot$ Fix$Compose$ unsimplify2 x])

    SAnd (Left (q1, True)) (Left (q2, True)) -> Right ([q1, q2], Compose [])
    SAnd (Left (q1, True)) (Right (qs, nonSimples)) -> Right (q1 : qs, nonSimples)
    SAnd (Right (qs, nonSimples)) (Left (q2, True)) -> Right (q2 : qs, nonSimples)
    SAnd (Right (qs1, Compose nonSimples1)) (Right (qs2, Compose nonSimples2)) ->
      Right (qs1 ++ qs2, Compose$ nonSimples1 ++ nonSimples2)
    SAnd a (Right (qs, Compose nonSimples)) ->
      Right (qs, Compose$ unsimplify2 a ++ nonSimples)
    SAnd (Right (qs, Compose nonSimples)) b ->
      Right (qs, Compose$ unsimplify2 b ++ nonSimples)
    SAnd a b -> Right ([], Compose
        [SAnd (Fix$Compose$ unsimplify2 a) (Fix$Compose$ unsimplify2 b)]
      )

    STrue -> Right ([], Compose [])
    SFalse -> Right ([], Compose [SFalse])
    SOr a b -> Right ([], Compose
        [SOr (Fix$Compose$ unsimplify2 a) (Fix$Compose$ unsimplify2 b)]
      )
  where
  qmask = accumArray (\_ _ -> True) False (0, qcount - 1)
  getSimples (Left (q, True)) = qmask [(q, ())]
  getSimples (Right (qs, _)) = qmask$ map (, ()) qs

  getNonsimples (Left (q, True)) = Nothing
  getNonsimples (Right (_, Compose [])) = Nothing
  getNonsimples (Right (_, nonSimples)) = Just$ Fix nonSimples

  unsimplify q = SNot$ Fix$Compose [SState q]

  unsimplify2 (Left (q, False)) = [SState q]
  unsimplify2 (Left (q, True)) = [SNot$ Fix$Compose [SState q]]
  unsimplify2 (Right (qs, Compose nonSimples)) = map unsimplify qs ++ nonSimples
