{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}

module Afa.TreeDag where

import Control.Arrow ((>>>))
import Data.Functor.Compose
import Data.Monoid (Sum(..))

import Control.Monad.State
import Control.Monad.ST
import Data.Array
import Data.Array.ST
import Data.Functor.Foldable.Dag.TreeHybrid (TreeHybrid(..))
import Data.Functor.Foldable
import Data.Functor.Foldable.Dag.Monadic (consuScanM, cataScanM)

import Afa.Functor (Term(..))

pattern And' ts = (Compose (Right (And ts)))
pattern Or' ts = (Compose (Right (Or ts)))
pattern Not' t = (Compose (Right (Not t)))
pattern LFalse' = (Compose (Right LFalse))
pattern LTrue' = (Compose (Right LFalse))

-- The following algebrae are basically the same as in Afa.Simplify, only the
-- above pattern synonyms are used instead of the bare data constructors of
-- Term. I haven't found an elegant way yet to remove this code duplication.
-- Maybe something like this: https://gitlab.haskell.org/ghc/ghc/-/issues/11461
-- could be used, not sure how elegant would the result be.
-- Another useful link:
-- https://www.reddit.com/r/haskell/comments/38owdh/question_would_an_associated_data_constructor_be/crxnn71/

removeDoubleNegation_alg
  :: Compose (Either Int) Term (TreeHybrid Term Int) -> TreeHybrid Term Int
removeDoubleNegation_alg (Not' (project -> Not' ct)) = ct
removeDoubleNegation_alg x = embed x

flatten_alg
  :: Compose (Either Int) Term (TreeHybrid Term Int) -> TreeHybrid Term Int
flatten_alg (And' ts) = embed$ And'$ flip concatMap ts$ \t ->
  case project t of And' cts -> cts; _ -> [t]
flatten_alg (Or' ts) = embed$ Or'$ flip concatMap ts$ \t ->
  case project t of Or' cts -> cts; _ -> [t]
flatten_alg x = embed x

delit_alg
  :: Compose (Either Int) Term (TreeHybrid Term Int) -> TreeHybrid Term Int
delit_alg x@(Not' t) = embed$ case project t of
  LTrue' -> LFalse'
  LFalse' -> LTrue'
  _ -> x
delit_alg (And' ts)
  | any (\t -> case project t of LFalse' -> True; _ -> False) ts = embed LFalse'
  | otherwise = embed$ And'$
      filter (\t -> case project t of LTrue' -> False; _ -> True) ts
delit_alg (Or' ts)
  | any (\t -> case project t of LTrue' -> True; _ -> False) ts = embed LTrue'
  | otherwise = embed$ Or'$
      filter (\t -> case project t of LFalse' -> False; _ -> True) ts
delit_alg x = embed x

removeUselessClauses_alg
  :: Compose (Either Int) Term (TreeHybrid Term Int) -> TreeHybrid Term Int
removeUselessClauses_alg (And' []) = embed LTrue'
removeUselessClauses_alg (And' [t]) = t
removeUselessClauses_alg (Or' []) = embed LFalse'
removeUselessClauses_alg (Or' [t]) = t
removeUselessClauses_alg x = embed x

simplify_alg
  :: Compose (Either Int) Term (TreeHybrid Term Int) -> TreeHybrid Term Int
simplify_alg
  = flatten_alg . project
  . delit_alg . project
  . removeDoubleNegation_alg . project
  . removeUselessClauses_alg

-- End of the duplicated code from Afa.Simplify ----------------------------------------

type SimpleTerms = Array Int (Term Int)
type Terms = Array Int (TreeHybrid Term Int)
