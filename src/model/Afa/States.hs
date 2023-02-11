{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Afa.States where

import Control.Lens
import Data.Array
import Data.Functor
import qualified Data.HashMap.Strict as HM
import Data.Hashable
import Data.Maybe
import InversionOfControl.TypeDict
import Language.Haskell.TH hiding (Q)
import Language.Haskell.TH.Quote (QuasiQuoter (..))

class (Q qs ~ q, R qs ~ r) => States qs q r | qs -> q where
  stateList :: qs -> [(q, R qs)]
  redirect :: qs -> [(q, R qs)] -> qs

  transition :: qs -> q -> R qs
  default transition :: Eq q => qs -> q -> R qs
  transition qs q = fromJust $ lookup q $ stateList qs

  stateCount :: qs -> Int
  default stateCount :: qs -> Int
  stateCount = length . stateList

type family RTraversed qs r'
type family R qs
type family Q qs

class
  (States qs q r, States qs' q r', r ~ R qs, qs' ~ RTraversed qs r', r' ~ R qs') =>
  RTraversable qs q r r' qs'
    | qs r' -> qs'
  where
  traverseQR :: Applicative m => (q -> R qs -> m r') -> qs -> m qs'

  traverseR :: Applicative m => (R qs -> m r') -> qs -> m qs'
  traverseR = traverseQR . const

newtype StateList q r = StateList [(q, r)]
type instance R (StateList q r) = r
type instance Q (StateList q r) = q
type instance RTraversed (StateList q r) r' = StateList q r'

instance Eq q => States (StateList q r) q r where
  stateList (StateList qs) = qs
  redirect (StateList qs) redirs = StateList $ foldl step qs redirs
    where
      step (elem@(q2, r2) : rest) redir@(q, r)
        | q == q2 = (q, r) : rest
        | otherwise = elem : step rest redir
      step _ _ = error "redirect: not found"

instance Eq q => RTraversable (StateList q r) q r r' (StateList q r') where
  traverseQR f (StateList qs) =
    StateList
      <$> traverse (\(q, r) -> (q,) <$> f q r) qs

newtype StateArray r = StateArray (Array Int r)
type instance R (StateArray r) = r
type instance Q (StateArray r) = Int
type instance RTraversed (StateArray r) r' = StateArray r'

instance States (StateArray r) Int r where
  stateList (StateArray qs) = assocs qs
  transition (StateArray qs) q = qs ! q
  redirect (StateArray qs) redirs = StateArray $ qs // redirs

instance RTraversable (StateArray r) Int r r' (StateArray r') where
  traverseQR f (StateArray qs) = StateArray <$> itraverse f qs

newtype StateHashMap q r = StateHashMap (HM.HashMap q r)
type instance R (StateHashMap q r) = r
type instance Q (StateHashMap q r) = q
type instance RTraversed (StateHashMap q r) r' = StateHashMap q r'

instance Hashable q => States (StateHashMap q r) q r where
  stateList (StateHashMap qs) = HM.toList qs
  transition (StateHashMap qs) q = qs HM.! q
  redirect (StateHashMap qs) redirs =
    StateHashMap $
      foldl (\qs (q, r) -> HM.insert q r qs) qs redirs

instance Hashable q => RTraversable (StateHashMap q r) q r r' (StateHashMap q r') where
  traverseQR f (StateHashMap qs) = StateHashMap <$> HM.traverseWithKey f qs

qs :: TypeQ
qs = do
  d <- lookupTypeName "d"
  case d of
    Just d ->
      return $
        let followD = AppT (ConT ''Follow) (VarT d)
            getQs = AppT (AppT (ConT ''Get) (LitT (StrTyLit "qs")))
         in getQs followD
    Nothing -> error "paramGetter: type d not in scope"
