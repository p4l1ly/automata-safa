{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Afa.Convert.Stranger where

import Debug.Trace

import GHC.Generics hiding (Prefix, Infix)
import Data.Functor.Classes
import Generic.Data (Generically1(..))
import Generic.Data.Orphans ()

import Control.Monad.Free
import Control.Arrow
import Data.Functor.Compose
import Control.Lens
import Data.Char
import Text.Parsec hiding (State)
import Text.Parsec.Expr
import Text.Parsec.Token
import Data.Fix hiding (cata)
import Data.Composition ((.:))
import Data.Traversable
import Control.RecursionSchemes.Lens
import Data.Array
import Data.List.NonEmpty (NonEmpty((:|)))
import qualified Data.List.NonEmpty as NE
import Data.Monoid (Endo(..))

import Afa.Lib.Free
import Afa
import Afa.Bool
import qualified Afa.Term.Bool as BTerm
import qualified Afa.Term.Mix as MTerm

type WParser a = Parsec String () a
runWParser p = runParser p () ""

parseExpr str = let Right x = runParser expr () ""$ filter (not . isSpace) str in x

afa :: WParser (BoolAfaUnswallowed Int)
afa = do
  qcount <- string "numOfStates:" *> spaces *> (read <$> many1 digit) <* newline
  init <- string "initialStates:" *> spaces *> (parseExpr <$> manyTill anyChar newline) 
  final <- string "finalStates:" *> spaces *> (parseExpr <$> manyTill anyChar newline) 
  string "States:" *> manyTill space newline
  states <- for [0..qcount - 1]$ \i ->
    string "state" *> spaces *> string (show i ++ ":") *> newline
    *> (parseExpr <$> manyTill anyChar newline) 
  return$ toAfa (qcount, init, final, states)

data STerm var rec
  = STrue
  | SFalse
  | SState Int
  | SVar var
  | SNot rec
  | SAnd rec rec
  | SOr rec rec
  deriving (Functor, Foldable, Traversable, Show, Eq, Generic, Generic1)
  deriving (Eq1, Show1) via (Generically1 (STerm var))

type STerm' = STerm String

expr :: WParser (Fix STerm')
expr = buildExpressionParser table term <?> "expression" where
  table =
    [ [Prefix$ Fix . SNot <$ char '¬']
    , [Infix (Fix .: SAnd <$ char '∧') AssocLeft]
    , [Infix (Fix .: SOr <$ char '∨') AssocLeft]
    ]

term :: WParser (Fix STerm')
term = between (char '(') (char ')') expr
   <|> (Fix . SState . read <$> (string "s_" *> many1 digit))
   <|> (Fix STrue <$ string "True")
   <|> (Fix SFalse <$ string "False")
   <|> (Fix . SVar <$> many1 (alphaNum <|> char '_'))
   <?> "expected a term"

toAfa :: (Int, Fix STerm', Fix STerm', [Fix STerm']) -> BoolAfaUnswallowed Int
toAfa (qcount, init, final, states) = unswallow BoolAfa
  { boolTerms = listArray (0, 3)
      [ Free BTerm.LTrue
      , Free BTerm.LFalse
      , Free$ BTerm.Predicate qcount
      , Free$ BTerm.Not$ Pure 2
      ]
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

  (states'', _) = runIdentity$ runHashConsTFrom (qcount + 1)$ for states'$
    (`freeModChilds` pure)$ \rec -> MTerm.modChilds MTerm.pureChildMod
      { MTerm.lT = rec
      , MTerm.lP = (`freeModChilds` pure)$ \rec2 -> BTerm.modChilds BTerm.ChildMod
          { BTerm.lP = hashCons', BTerm.lT = rec2 }
      }

  states' = states <&> convertTransition
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

  init' = ($ (convertTransition init >>= Free . MTerm.State))$ (runIdentity .)$
    (`freeModChilds` pure)$ \rec -> MTerm.modChilds MTerm.pureChildMod
      { MTerm.lT = rec
      , MTerm.lP = (`freeModChilds` pure)$ \rec2 -> BTerm.modChilds BTerm.ChildMod
          { BTerm.lP = error "variable in init formula", BTerm.lT = rec2 }
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

  asRight (Left x) = Free$ MTerm.Predicate x
  asRight (Right x) = x

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
