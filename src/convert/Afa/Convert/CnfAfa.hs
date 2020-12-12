{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE LambdaCase #-}

module Afa.Convert.CnfAfa (CnfAfa(..), Lit(..), tseytin, tseytin') where

import Control.Lens
import Data.Bifunctor
import Control.Monad.ST
import Control.Monad.State
import Control.Monad.Writer
import Data.Array
import Data.Array.ST
import qualified Data.List.NonEmpty as NE
import Control.RecursionSchemes.Lens
import qualified Afa.Term.Mix as MTerm
import qualified Afa.Term.Bool as BTerm
import Afa.Bool
import qualified Afa
import Afa.Lib.LiftArray
import qualified Afa.Convert.Capnp.Afa as CapAfa (varCount)


data Lit = Lit
  { ix :: Int
  , isPositive :: Bool
  } deriving Show


data CnfAfa = CnfAfa
  { states :: Array Int Lit
  , varCount :: Int
  , clauses :: [[Lit]]
  }

tseytin' bafa = tseytin varCnt bafa{boolTerms = aterms'} where
  (varCnt, aterms') = CapAfa.varCount$ boolTerms bafa

tseytin :: Int -> BoolAfaUnswallowed Int -> CnfAfa
tseytin varCount (BoolAfa bterms (Afa.Afa mterms states 0)) = CnfAfa
  { states = fmap (mIxMap!) states
  , varCount = varCount
  , clauses = clauses
  }
  where
  stateCount = rangeSize$ bounds states

  (mIxMap, clauses) = runST action where
    action :: forall s. ST s (Array Int Lit, [[Lit]])
    action = runCountLogT (stateCount + varCount)$ do
      bIxMap <- cataScanT' @(LiftArray (STArray s))
        traversed (btermTseytin stateCount) bterms
      cataScanT' @(LiftArray (STArray s)) traversed (mtermTseytin bIxMap) mterms

btermTseytin :: Monad m => Int -> BTerm.Term Int Lit -> CountLog [Lit] m Lit
btermTseytin stateCount = \case
  BTerm.Predicate v -> return (Lit (stateCount + v) True)
  BTerm.Not (Lit ix isPositive) -> return$ Lit ix$ not isPositive
  BTerm.And lits -> do
    ix <- newSignal
    newClauses$ map (: [Lit ix False])$ NE.toList lits
    return$ Lit ix True
  BTerm.Or lits -> do
    ix <- newSignal
    newClause$ Lit ix False : NE.toList lits
    return$ Lit ix True
  BTerm.LFalse -> error
    "Tseytin does not support LFalse, please simplify the AFA"
  BTerm.LTrue -> error
    "Tseytin does not support LFalse, please simplify the AFA"

mtermTseytin :: Monad m => Array Int Lit -> MTerm.Term Int Int Lit -> CountLog [Lit] m Lit
mtermTseytin bIxMap = \case
  MTerm.Predicate v -> return$ bIxMap!v
  MTerm.State q -> return$ Lit q True
  MTerm.And lits -> do
    ix <- newSignal
    newClauses$ map (: [Lit ix False])$ NE.toList lits
    return$ Lit ix True
  MTerm.Or lits -> do
    ix <- newSignal
    newClause$ Lit ix False : NE.toList lits
    return$ Lit ix True
  MTerm.LTrue -> error
    "Tseytin does not support LFalse, please simplify the AFA"


newtype CountLog x m a = CountLog (StateT Int (WriterT (Endo [x]) m) a)
  deriving (Functor, Applicative, Monad)
instance MonadTrans (CountLog x) where
  lift = CountLog . lift . lift

runCountLogT :: Monad m => Int -> CountLog x m a -> m (a, [x])
runCountLogT offset (CountLog action) =
  fmap (second (`appEndo` []))$ runWriterT$ evalStateT action offset

newSignal :: Monad m => CountLog x m Int
newSignal = CountLog$ do
  ix <- get
  ix <$ put (ix + 1)

newClauses :: Monad m => [x] -> CountLog x m ()
newClauses clauses = CountLog$ lift$ tell (Endo (clauses ++))

newClause :: Monad m => x -> CountLog x m ()
newClause clauses = CountLog$ lift$ tell (Endo (clauses :))
