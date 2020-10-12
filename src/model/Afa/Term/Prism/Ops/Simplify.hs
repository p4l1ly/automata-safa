{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

module Afa.Term.Prism.Ops.Simplify where

import Data.List (sort, group)
import Data.Functor.Foldable (embed, project, Corecursive, Recursive, Base)

import Afa.Term.Prism
  ( Term, PositiveTerm, LitTerm
  , pattern LTrue
  , pattern LFalse
  , pattern Not
  , pattern And
  , pattern Or
  )

flatten_alg :: (PositiveTerm f, Corecursive t, Recursive t, f ~ Base t) => f t -> t
flatten_alg (And ts) = embed$ And$ flip concatMap ts$ \t ->
  case project t of And cts -> cts; _ -> [t]
flatten_alg (Or ts) = embed$ Or$ flip concatMap ts$ \t ->
  case project t of Or cts -> cts; _ -> [t]
flatten_alg x = embed x

removeSingletonClauses_alg :: (PositiveTerm f, Corecursive t, f ~ Base t) => f t -> t
removeSingletonClauses_alg (And [t]) = t
removeSingletonClauses_alg (Or [t]) = t
removeSingletonClauses_alg x = embed x

removeDoubleNegation_alg
  :: (Term f, Corecursive t, Recursive t, f ~ Base t) => f t -> t
removeDoubleNegation_alg (Not (project -> Not ct)) = ct
removeDoubleNegation_alg x = embed x

delit_alg :: (LitTerm f, Corecursive t, Recursive t, f ~ Base t) => f t -> t
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

removeEmptyClauses_alg :: (LitTerm f, Corecursive t, f ~ Base t) => f t -> t
removeEmptyClauses_alg (And []) = embed LTrue
removeEmptyClauses_alg (Or []) = embed LFalse
removeEmptyClauses_alg x = embed x

simplify_alg :: (LitTerm f, Corecursive t, Recursive t, f ~ Base t) => f t -> t
simplify_alg
  = flatten_alg . project
  . removeDoubleNegation_alg . project
  . removeSingletonClauses_alg . project
  . delit_alg . project
  . removeEmptyClauses_alg

positiveSimplify_alg :: (PositiveTerm f, Corecursive t, Recursive t, f ~ Base t)
  => f t -> t
positiveSimplify_alg
  = flatten_alg . project
  . removeSingletonClauses_alg

nolitSimplify_alg :: (Term f, Corecursive t, Recursive t, f ~ Base t)
  => f t -> t
nolitSimplify_alg
  = flatten_alg . project
  . removeDoubleNegation_alg . project
  . removeSingletonClauses_alg
