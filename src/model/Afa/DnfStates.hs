{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE BangPatterns #-}

module Afa.DnfStates where

import Afa.Finalful.STerm (Term(..))
import TypeDict
import Shaper
import Data.Kind (Constraint)
import Shaper.Helpers
import DepDict ( ToConstraint, DepDict((:|:)) )
import qualified DepDict as D
import Data.Functor ((<&>))

type QDnfAlgD d m = QDnfAlgD_ d m (QDnfAlgA d [g|q|] [g|v|] [g|r|]) [g|q|] [g|v|] [g|r|]
type QDnfAlgA d q v r =  -- keyword aliases
  Name "rec" (Mk (MfnK r [r]) [d|rec|])
    :+: Name "self" (Mk (MfnK () r) [d|rec|])
    :+: Name "fail" (Mk (MfnK (Term q v [r]) [r]) [d|fail|])
    :+: Name "buildD"
          ( Name "shareTree" (Mk (MfnK r r) [d|shareTree|])
              :+: Name "buildTree" (Mk (MfnK (Term q v r) r) [d|buildTree|])
              :+: d
          )
    :+: End
type QDnfAlgD_ :: TypeDict -> (* -> *) -> TypeDict -> * -> * -> * -> DepDict
type QDnfAlgD_ d m d' q v r =
  D.Name "aliases" (q ~ [g|q|], v ~ [g|v|], r ~ [g|r|], d' ~ QDnfAlgA d q v r)
  :|: D.Name "rec"
        ( D.Name "self" (MonadFn [d'|self|] m)
            :|: D.Name "rec" (MonadFn [d'|rec|] m)
            :|: D.Name "isTree" (MonadFn (Mk IsTree [d|rec|]) m)
            :|: D.End
        )
  :|: D.Name "build" (D.Remove "isTree" (BuildInheritShareD [g'|buildD|] (Term q v r) r m))
  :|: D.End
qdnfAlg ::
  forall d q v r m d'.
  ToConstraint (QDnfAlgD_ d m d' q v r) =>
  Term q v r -> m [r]
qdnfAlg LTrue = [d'|ask|self|] <&> single
qdnfAlg LFalse = [d'|ask|self|] <&> single
qdnfAlg (State _) = [d'|ask|self|] <&> single
qdnfAlg (Var _) = [d'|ask|self|] <&> single
qdnfAlg fr = traverse [d'|monadfn|rec|] fr >>= \case
  (Or !disj1 !disj2) -> return $ disj1 ++ disj2
  (And [!x1] [!x2]) -> [d'|ask|self|] <&> single
  (And !disj1 !disj2) -> sequence [buildInheritShare @[g'|buildD|] (And x1 x2) | !x1 <- disj1, !x2 <- disj2]
  (Not !x1) -> error "qdnfAlg: Not unsupported"

single :: r -> [r]
single r = [r]
