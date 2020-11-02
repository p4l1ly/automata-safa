{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeApplications #-}

module Afa where

import GHC.Generics ((:*:)(..))
import Data.Functor.Compose
import Control.Lens
import Data.Array
import Data.Functor.Foldable.MultiDag (TheLens(..), Containing(..), constIso)
import Data.Functor.Tree (TreeF)

import Afa.Term (Term, Term_p(..), Term_q(..))

data Afa terms states init = Afa
  { terms :: terms
  , states :: states
  , initState :: init
  }
  deriving (Show, Eq)

type Afa' p = Afa
  (Array Int (TreeF (Term p Int) Int))
  (Array Int (State Int))
  (Identity (InitState Int))

newtype State t = State t
newtype InitState t = InitState t

data TermLens
data StateLens
data InitStateLens
data StateParentLens

newtype StateParents t s i = StateParents {unStateParents :: Afa t s i}

instance TheLens TermLens (Afa t s i) (Afa t' s i) t t' where
  theLens = lens terms (\afa terms' -> afa{terms = terms'})
instance TheLens StateLens (Afa t s i) (Afa t s' i) s s' where
  theLens = lens states (\afa states' -> afa{states = states'})
instance TheLens InitStateLens (Afa t s i) (Afa t s i') i i' where
  theLens = lens initState (\afa initState' -> afa{initState = initState'})

instance Containing TermLens (Term p q t) (Term p q t') (Term p q) t t' where
  containerIso = id
instance Containing StateLens (Term p q t) (Term p q' t) (Term_q p t) q q' where
  containerIso = iso Term_q unTerm_q
instance Containing InitStateLens (Term p q t) (Term p q t) (Const (Term p q t)) i i'
  where containerIso = constIso

instance Containing TermLens (State t) (State t') Identity t t' where
  containerIso = iso (\(State t) -> Identity t) (\(Identity t) -> State t)
instance Containing StateLens (State t) (State t) (Const (State t)) q q' where
  containerIso = constIso
instance Containing InitStateLens (State t) (State t) (Const (State t)) q q' where
  containerIso = constIso

instance Containing TermLens (InitState q) (InitState q) (Const (InitState q)) t t'
  where containerIso = constIso
instance Containing StateLens (InitState q) (InitState q') Identity q q' where
  containerIso = iso (\(InitState t) -> Identity t) (\(Identity t) -> InitState t)
instance Containing InitStateLens (InitState q) (InitState q) (Const (InitState q)) t t'
  where containerIso = constIso

instance TheLens
  StateParentLens (Afa t s i) (Afa t' s i')
  (Identity (StateParents t s i))
  (Identity (StateParents t' s i'))
  where
  theLens = iso (Identity . StateParents) (unStateParents . runIdentity)

instance
  ( Functor gt
  , Functor gi
  , Containing StateLens t t' ft x x'
  , Containing StateLens i i' fi x x'
  )
  => Containing StateLens
     (StateParents (gt t) s (gi i)) (StateParents (gt t') s (gi i'))
     (Compose ((,) s) (Compose gt ft :*: Compose gi fi)) x x'
  where
  containerIso =
    withIso (containerIso @StateLens) $ \ytoF yfromF ->
      withIso (containerIso @StateLens) $ \ztoF zfromF -> iso
        (\(StateParents (Afa t s i)) ->
          Compose$ (s, Compose (fmap ytoF t) :*: Compose (fmap ztoF i))
        )
        (\(Compose (s, Compose t' :*: Compose i')) ->
          StateParents (Afa (fmap yfromF t') s (fmap zfromF i'))
        )
