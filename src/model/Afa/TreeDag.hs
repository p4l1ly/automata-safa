{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}

module Afa.TreeDag where

import Control.Arrow ((>>>))
import Data.Functor.Compose

import Data.Array
import Data.Functor.Foldable
import Data.Functor.Foldable.Dag.Pure (cataScan)
import Data.Functor.Foldable.Dag.TreeHybrid (TreeHybrid(..))

import Afa.Functor (Term)
import Afa.StatePositiveness (StateSignum)
import qualified Afa.StatePositiveness

makeStatesPositive
  :: Array Int (TreeHybrid Term Int)
  -> Array Int (Maybe (StateSignum, TreeHybrid Term Int))
makeStatesPositive =
  cataScan makeStatesPositive_alg
  . fmap (Compose . fmap (\ix -> (ix, ix)))

makeStatesPositive_alg
  :: Compose (TreeHybrid Term) ((,) Int) (Maybe (StateSignum, TreeHybrid Term Int))
  -> Maybe (StateSignum, TreeHybrid Term Int)
makeStatesPositive_alg = (getCompose >>>)$ cata$ \case
  (Compose (Left (ix, Nothing))) -> Nothing
  (Compose (Left (ix, Just (sig, _)))) -> Just (sig, TreeHybrid$ Left ix)
  (Compose (Right t)) -> Afa.StatePositiveness.makeStatesPositive_alg t

complement :: TreeHybrid Term Int -> TreeHybrid Term Int
complement = cata$ \case
  (Compose (Left ix)) -> TreeHybrid$ Left ix
  (Compose (Right t)) -> Afa.StatePositiveness.complement_alg t
