{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

module Afa.Simplify where

import Data.List (sort, group)
import Data.Functor.Foldable (embed, project, Corecursive, Recursive, Base)

import Afa.Functor (Term(..))

removeDoubleNegation_alg :: (Corecursive t, Recursive t, Term ~ Base t) => Term t -> t
removeDoubleNegation_alg (Not (project -> Not ct)) = ct
removeDoubleNegation_alg x = embed x

flatten_alg :: (Corecursive t, Recursive t, Term ~ Base t) => Term t -> t
flatten_alg (And ts) = embed$ And$ flip concatMap ts$ \t ->
  case project t of And cts -> cts; _ -> [t]
flatten_alg (Or ts) = embed$ Or$ flip concatMap ts$ \t ->
  case project t of Or cts -> cts; _ -> [t]
flatten_alg x = embed x

delit_alg :: (Corecursive t, Recursive t, Term ~ Base t) => Term t -> t
delit_alg x@(Not t) = embed$ case project t of
  LTrue -> LFalse
  LFalse -> LTrue
  _ -> x
delit_alg (And ts)
  | any (\t -> case project t of LFalse -> True; _ -> False) ts = embed LFalse
  | otherwise = embed$ And$
      filter (\t -> case project t of LTrue -> False; _ -> True) ts
delit_alg (Or ts)
  | any (\t -> case project t of LTrue -> True; _ -> False) ts = embed LTrue
  | otherwise = embed$ Or$
      filter (\t -> case project t of LFalse -> False; _ -> True) ts
delit_alg x = embed x

removeEmptyClauses_alg :: (Corecursive t, Term ~ Base t) => Term t -> t
removeEmptyClauses_alg (And []) = embed LTrue
removeEmptyClauses_alg (Or []) = embed LFalse
removeEmptyClauses_alg x = embed x

removeSingletonClauses_alg :: (Corecursive t, Term ~ Base t) => Term t -> t
removeSingletonClauses_alg (And [t]) = t
removeSingletonClauses_alg (Or [t]) = t
removeSingletonClauses_alg x = embed x

-- | This has quadratic complexity if using as an algebra for the fixpoint of terms.
-- Hash consing + unwinding should do the same with lesser complexity.
uniqOperands_simple :: (Eq a, Ord a) => Term a -> Term a
uniqOperands_simple (And as) = And$ map head$ group$ sort as
uniqOperands_simple (Or as) = Or$ map head$ group$ sort as
uniqOperands_simple x = x

simplify_alg :: (Corecursive t, Recursive t, Term ~ Base t) => Term t -> t
simplify_alg
  = flatten_alg . project
  . removeDoubleNegation_alg . project
  . removeSingletonClauses_alg . project
  . delit_alg . project
  . removeEmptyClauses_alg
