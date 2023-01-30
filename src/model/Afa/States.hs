{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}

module Afa.States where

import Data.Array
import qualified Data.HashMap.Strict as HM
import Data.Hashable
import Data.Maybe

class States qs q r | qs -> q r where
  stateList :: qs -> [(q, r)]
  transition :: qs -> q -> r
  default transition :: Eq q => qs -> q -> r
  transition qs q = fromJust $ lookup q $ stateList qs

class RTraversable qs r r' qs' | qs -> r, qs r' -> qs' where
  traverseR :: Applicative m => (r -> m r') -> qs -> m qs'

newtype StateList q r = StateList [(q, r)]

instance Eq q => States (StateList q r) q r where
  stateList (StateList qs) = qs

instance RTraversable (StateList q r) r r' (StateList q r') where
  traverseR f (StateList qs) = StateList <$> traverse (traverse f) qs

newtype StateArray r = StateArray (Array Int r)

instance States (StateArray r) Int r where
  stateList (StateArray qs) = assocs qs
  transition (StateArray qs) q = qs ! q

instance RTraversable (StateArray r) r r' (StateArray r') where
  traverseR f (StateArray qs) = StateArray <$> traverse f qs

newtype StateHashMap q r = StateHashMap (HM.HashMap q r)

instance Hashable q => States (StateHashMap q r) q r where
  stateList (StateHashMap qs) = HM.toList qs
  transition (StateHashMap qs) q = qs HM.! q

instance RTraversable (StateHashMap q r) r r' (StateHashMap q r') where
  traverseR f (StateHashMap qs) = StateHashMap <$> traverse f qs
