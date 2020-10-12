{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}

module Afa.Term.TreeF.Ops where

import Control.Arrow ((>>>))
import Data.Functor.Compose

import Data.Array
import Data.Functor.Foldable
import Data.Functor.Foldable.Dag.Pure (cataScan)
import Data.Functor.Tree (TreeF(..))

import Afa.Term (Term)
import qualified Afa.Term.TreeFBase as B
import qualified Afa.Term.TreeF as T
import Afa.Term.Prism.Ops.StatePositiveness (StateSignum)
import qualified Afa.Term.Prism.Ops.StatePositiveness as StatePositiveness

makeStatesPositive
  :: Array Int (TreeF Term Int)
  -> Array Int (Maybe (StateSignum, TreeF Term Int))
makeStatesPositive =
  cataScan makeStatesPositive_alg
  . fmap (Compose . fmap (\ix -> (ix, ix)))

makeStatesPositive_alg
  :: Compose (TreeF Term) ((,) Int) (Maybe (StateSignum, TreeF Term Int))
  -> Maybe (StateSignum, TreeF Term Int)
makeStatesPositive_alg = (getCompose >>>)$ cata$ \case
  B.Ref (ix, Nothing) -> Nothing
  B.Ref (ix, Just (sig, _)) -> Just (sig, TreeF$ Left ix)
  B.NRef t -> StatePositiveness.makeStatesPositive_alg t
