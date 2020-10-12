{-# LANGUAGE TypeFamilies #-}

module Afa.Ops.Language where

import Data.Functor.Foldable (embed, Corecursive, Base)

import qualified Afa.Term.TreeF.Ops as TD
import Afa


complement :: Afa -> Afa
complement afa@Afa{terms} = afa{terms = fmap TD.complement terms}
