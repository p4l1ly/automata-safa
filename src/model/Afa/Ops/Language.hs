{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE LambdaCase #-}
module Afa.Ops.Language where

import Data.Functor.Foldable (cata, embed, Corecursive, Base)

import Afa
import Afa.Term (Term(..))
import qualified Afa.Term.Prism as P
import qualified Afa.Term.TreeFBase as B
import Data.Functor.Tree (TreeF(TreeF))

complement_alg :: (P.StateVarTerm f, Corecursive t, f ~ Base t) => Term t -> t
complement_alg LTrue = embed P.LFalse
complement_alg LFalse = embed P.LTrue
complement_alg (Var x) = embed$ P.Not$ embed$ P.Var x
complement_alg (State x) = embed$ P.State x
complement_alg (Not x) = embed$ P.Not x
complement_alg (And xs) = embed$ P.Or xs
complement_alg (Or xs) = embed$ P.And xs

complementTreeF :: TreeF Term Int -> TreeF Term Int
complementTreeF = cata$ \case
  B.Ref ix -> TreeF$ Left ix
  B.NRef t -> complement_alg t

complement :: Afa -> Afa
complement afa@Afa{terms} = afa{terms = fmap complementTreeF terms}
