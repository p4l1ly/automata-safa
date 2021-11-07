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
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeApplications #-}


module Afa.Convert.Stranger where

import Debug.Trace

import Data.String.Interpolate.IsString
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
import Control.RecursionSchemes.Utils.NoCons
import Data.Array
import Data.List.NonEmpty (NonEmpty((:|)))
import qualified Data.List.NonEmpty as NE
import Data.Monoid (Endo(..))
import qualified Data.Text as T
import qualified Data.Text.Read as TR
import Data.Array.ST
import Control.Monad.ST
import Control.Monad.Trans (lift)

import Afa.Lib (listArray')
import Afa.Lib.Free
import Afa.Lib.LiftArray
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

  fcount :: Int <- (string "numOfTransitionSubformulae:" *> skipSpace *> decimal <* endOfLine) <|> pure 0
  formulae <- if fcount /= 0
    then do
      string "TransitionSubformulae:" *> skipSpace
      for [0..fcount - 1]$ \i ->
        "formula" *> skipSpace *> string (T.pack$ show i ++ ":") *> endOfLine
        *> (parseExpr <$> takeTill isEndOfLine <* endOfLine)
    else return []

  string "States:" *> skipSpace
  states <- for [0..qcount - 1]$ \i ->
    "state" *> skipSpace *> string (T.pack$ show i ++ ":") *> endOfLine
    *> (parseExpr <$> takeTill isEndOfLine <* endOfLine) 
  return$ toAfa (qcount, fcount, init, final, formulae, states)

data STerm frec var rec
  = STrue
  | SFalse
  | SState !Int
  | SFormula !frec
  | SVar !var
  | SNot !rec
  | SAnd !rec !rec
  | SOr !rec !rec
  deriving (Functor, Foldable, Traversable, Show, Eq, Generic, Generic1)
  deriving (Eq1, Show1) via (Generically1 (STerm frec var))

type STerm' = STerm Int T.Text

expr :: Parser (Fix STerm')
expr = buildExpressionParser table term <?> "expression" where
  table =
    [ [Prefix$ Fix . SNot <$ (char '¬' <|> char '!')]
    , [Infix (Fix .: SAnd <$ (char '∧' <|> char '&')) AssocLeft]
    , [Infix (Fix .: SOr <$ (char '∨' <|> char '|')) AssocLeft]
    ]

term :: Parser (Fix STerm')
term = "(" *> expr <* ")"
   <|> (Fix . SState <$> ("s_" *> decimal))
   <|> (Fix . SFormula <$> ("f_" *> decimal))
   <|> (Fix STrue <$ "True")
   <|> (Fix SFalse <$ "False")
   <|> (Fix . SVar <$> takeWhile1 (\case '_' -> True; x -> isAlphaNum x))
   <?> "expected a term"


convertFormulae :: [Fix (STerm Int Int)] -> Int -> Int -> Int
  -> ( Array Int (Bool, Int)
     , [Free (BTerm.Term Int) Int]
     , [Free (MTerm.Term (Free (BTerm.Term Int) Int) Int) Int]
     )
convertFormulae formulae fcount qcount symCount = runST action where
    action :: forall s. ST s (Array Int (Bool, Int), [Free (BTerm.Term Int) Int], [Free (MTerm.Term (Free (BTerm.Term Int) Int) Int) Int])
    action = do
      let formulaeArr = listArray (0, fcount - 1) formulae
      ((ixMap0, fbterms0), fmterms0) <- runNoConsTFrom qcount$ runNoConsTFrom (4 + symCount)$
        ($ formulaeArr)$ cataScanT' @(LLSTArray s) ftraversed$
          \f -> do
            let f' = ($f)$ cataRecursive$ \case
                  STrue -> Left$ Pure 0
                  SFalse -> Left$ Pure 1
                  SState q -> Right$ Pure q
                  SFormula (False, i) -> Left$ Pure i
                  SFormula (True, i) -> Right$ Pure i
                  SVar v -> Left$ Pure v
                  SNot (Left x) -> Left$ Free$ BTerm.Not x
                  SAnd (Left x) (Left y) -> Left$ Free$ BTerm.And$ x :| [y]
                  SOr (Left x) (Left y) -> Left$ Free$ BTerm.Or$ x :| [y]
                  SAnd x y -> Right$ Free$ MTerm.And$ NE.map asRight$ x :| [y]
                  SOr x y -> Right$ Free$ MTerm.Or$ NE.map asRight$ x :| [y]
            case f' of
              Left bterm -> (False,) <$> nocons bterm
              Right mterm -> (True,) <$> lift (nocons mterm)
      return (ixMap0, fbterms0, fmterms0)

ftraversed :: Applicative m => (a -> m b) -> Fix (STerm a var) -> m (Fix (STerm b var))
ftraversed fn = cataRecursive$ \case
  STrue -> pure$ Fix STrue
  SFalse -> pure$ Fix SFalse
  SState i -> pure$ Fix$ SState i
  SFormula f -> Fix . SFormula <$> fn f
  SVar v -> pure$ Fix$ SVar v
  SNot t -> Fix . SNot <$> t
  SAnd t1 t2 -> Fix .: SAnd <$> t1 <*> t2
  SOr t1 t2 -> Fix .: SOr <$> t1 <*> t2

vtraversed :: Applicative m => (a -> m b) -> Fix (STerm frec a) -> m (Fix (STerm frec b))
vtraversed fn = cataRecursive$ \case
  STrue -> pure$ Fix STrue
  SFalse -> pure$ Fix SFalse
  SState i -> pure$ Fix$ SState i
  SFormula f -> pure$ Fix$ SFormula f
  SVar v -> Fix . SVar <$> fn v
  SNot t -> Fix . SNot <$> t
  SAnd t1 t2 -> Fix .: SAnd <$> t1 <*> t2
  SOr t1 t2 -> Fix .: SOr <$> t1 <*> t2

asRight (Left x) = Free$ MTerm.Predicate x
asRight (Right x) = x

toAfa :: (Int, Int, Fix STerm', Fix STerm', [Fix STerm'], [Fix STerm']) -> BoolAfaUnswallowed Int
toAfa args@(qcount, fcount, init, final, formulae, states) = unswallow BoolAfa
  { boolTerms = listArray'$
      [ Free BTerm.LTrue
      , Free BTerm.LFalse
      , Free$ BTerm.Predicate qcount
      , Free$ BTerm.Not$ Pure 2
      ] ++ map (Free . BTerm.Predicate) [qcount + 1 .. qcount + symCount] ++ fbterms
  , Afa.Bool.afa = Afa
      { terms = listArray'$ extendedStates ++ fmterms
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

  extendedStates = [0..qcount - 1] <&> \i ->
    case (simpleNonfinal!i, qsInNonsimpleFinal!i) of
      (True, _) -> Free$ MTerm.And$
        Free (MTerm.State i) :| [Free$ MTerm.Predicate$ Pure 3]
      (_, False) -> Free$ MTerm.Or$
        Free (MTerm.State i) :| [Free$ MTerm.Predicate$ Pure 2]
      _ -> Free$ MTerm.Or$ Free (MTerm.State i) :|
        [Free$ MTerm.Predicate$ Free$ BTerm.And$ Pure 2 :| [Free$ BTerm.Predicate i]]

  ((states', formulae'), length -> symCount) = runIdentity$ runHashConsTFrom 4$
    (,) <$> for states enumerateSyms <*> for formulae enumerateSyms

  enumerateSyms = vtraversed hashCons'

  leftPure (Left x) = Pure x
  leftPure (Right x) = x

  freeJust (Free t) = Just t
  freeJust _ = Nothing

  modPT lP lT = MTerm.modChilds MTerm.pureChildMod{ MTerm.lT = lT, MTerm.lP = lP }

  flattenFree fn = either (return . Pure)$ return . Free . fn freeJust

  -- flattening highly improves performance
  states'' = states' <&> \x -> runIdentity$ convertTransition x & cataT
    (freeTraversal$ modPT$ cataT (freeTraversal traversed) (flattenFree BTerm.flatten0))
    (flattenFree MTerm.flatten0)

  (fIxMap, fbterms, fmterms) = convertFormulae formulae' fcount qcount symCount

  convertTransition = (asRight .)$ cataRecursive$ \case
    STrue -> Left$ Pure 0
    SFalse -> Left$ Pure 1
    SState q -> Right$ Pure q
    SFormula f -> case fIxMap!f of
      (False, f) -> Left$ Pure f
      (True, f) -> Right$ Pure f
    SVar v -> Left$ Pure v
    SNot (Left x) -> Left$ Free$ BTerm.Not x
    SAnd (Left x) (Left y) -> Left$ Free$ BTerm.And$ x :| [y]
    SOr (Left x) (Left y) -> Left$ Free$ BTerm.Or$ x :| [y]
    SAnd x y -> Right$ Free$ MTerm.And$ NE.map asRight$ x :| [y]
    SOr x y -> Right$ Free$ MTerm.Or$ NE.map asRight$ x :| [y]
    x -> error$ "non-exhaustive patterns " ++ show x

  init' = convertTransition (runIdentity$ vtraversed rejectVar init) >>= Free . MTerm.State
    where rejectVar = error "variable in init formula"

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


formatAfa :: BoolAfaUnswallowed Int -> T.Text
formatAfa (BoolAfa bterms (Afa mterms states init)) = T.unlines
  [ [i|numOfStates: #{len states}|]
  , [i|initialStates: s_#{init}|]
  , let finals = map (\q -> [i|!s_#{q}|]) $ Data.Array.indices states
    in [i|finalStates: #{T.intercalate " & " finals}|]
  , [i|numOfTransitionSubformulae: #{len bterms + len mterms}|]
  , "TransitionSubformulae:"
  , T.intercalate "\n"$ map (\(j, t) -> [i|formula #{j}:\n#{fromBTerm t}|]) (assocs bterms)
  , T.intercalate "\n"$ map (\(j, t) -> [i|formula #{j + btermCount}:\n#{fromMTerm t}|]) (assocs mterms)
  , "States:"
  , T.intercalate "\n"$ map (\(j, t) -> [i|state #{j}:\nf_#{t + btermCount}|]) (assocs states)
  ]
  where
  len = rangeSize . bounds
  btermCount = len bterms

  fromBTerm :: BTerm.Term Int Int -> T.Text
  fromBTerm BTerm.LTrue = "True"
  fromBTerm BTerm.LFalse = "False"
  fromBTerm (BTerm.Predicate p) = [i|a_#{p}|]
  fromBTerm (BTerm.Not x) = [i|!f_#{x}|]
  fromBTerm (BTerm.And xs) = T.intercalate " & "$ map (\x -> [i|f_#{x}|])$ NE.toList xs
  fromBTerm (BTerm.Or xs) = T.intercalate " | "$ map (\x -> [i|f_#{x}|])$ NE.toList xs

  fromMTerm :: MTerm.Term Int Int Int -> T.Text
  fromMTerm MTerm.LTrue = "True"
  fromMTerm (MTerm.Predicate p) = [i|f_#{p}|]
  fromMTerm (MTerm.State q) = [i|s_#{q}|]
  fromMTerm (MTerm.And xs) = T.intercalate " & "$ map (\x -> [i|f_#{x + btermCount}|])$ NE.toList xs
  fromMTerm (MTerm.Or xs) = T.intercalate " | "$ map (\x -> [i|f_#{x + btermCount}|])$ NE.toList xs
