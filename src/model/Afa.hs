{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE LambdaCase #-}

module Afa where

import Debug.Trace

import Data.Functor
import Data.Array
import Afa.Term.Mix (Term(..))
import qualified Afa.Term.Mix as MTerm
import Afa.Lib.Tree
import Control.RecursionSchemes.Lens
import Control.Monad.Trans
import Control.Monad.Identity
import Data.Traversable
import Afa.Lib (listArray')

data Afa terms states init = Afa
  { terms :: terms
  , states :: states
  , initState :: init
  }
  deriving (Show, Eq)

type MixTermITree p = Tree (Term p Int) Int
type AfaSwallowed p = Afa (Array Int (MixTermITree p)) (Array Int (MixTermITree p)) Int
type AfaUnswallowed p = Afa (Array Int (Term p Int Int)) (Array Int Int) Int

delayPredicates :: (Show p) => AfaUnswallowed p -> AfaUnswallowed p
delayPredicates afa@Afa{terms, states} = afa
  { terms = listArray'$ elems terms1 ++ terms2
  , states = listArray'$ elems states ++ states2
  }
  where
  stateCount = rangeSize (bounds states)
  termCount = rangeSize (bounds terms)
  Identity ((terms1, terms2), states2) =
    runNoConsTFrom stateCount$ runNoConsTFrom termCount$
      for terms$ \case
        p@(Predicate _) -> (nocons p >>= lift . nocons) <&> State
        x -> return x


reorderStates :: Functor f
  => Afa (f (Term p' Int t')) (Array Int a) Int
  -> Afa (f (Term p' Int t')) (Array Int a) Int
reorderStates afa@Afa{initState = 0} = afa
reorderStates Afa{terms, states, initState} = Afa
  { initState = 0
  , states = states // [(0, states!initState), (initState, states!0)]
  , terms = terms <&> runIdentity . MTerm.modChilds MTerm.pureChildMod
      { MTerm.lQ = Identity . \case
          0 -> initState
          q | q == initState -> 0
            | otherwise -> q
      }
  }
