{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE LambdaCase #-}

module Afa where

import Data.Functor
import Data.Array
import Afa.Term.Mix (Term(..))
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

delayPredicates :: AfaUnswallowed p -> AfaUnswallowed p
delayPredicates afa@Afa{terms, states} = afa
  { terms = listArray'$ elems terms1 ++ terms2
  , states = listArray'$ elems states ++ states2
  }
  where
  stateCount = rangeSize (bounds states)
  termCount = rangeSize (bounds terms)
  ((terms1, terms2), states2) =
    runIdentity$ runNoConsTFrom stateCount$ runNoConsTFrom termCount$
      for terms$ \case
        p@(Predicate _) -> (nocons p >>= lift . nocons) <&> State
        x -> return x
