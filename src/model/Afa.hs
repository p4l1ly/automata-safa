{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Afa where

import Data.Array
import Afa.Term.Mix (Term)
import Afa.Lib.Tree

data Afa terms states init = Afa
  { terms :: terms
  , states :: states
  , initState :: init
  }
  deriving (Show, Eq)

type MixTermITree p = Tree (Term p Int) Int
type AfaSwallowed p = Afa (Array Int (MixTermITree p)) (Array Int (MixTermITree p)) Int
type AfaUnswallowed p = Afa (Array Int (Term p Int Int)) (Array Int Int) Int
