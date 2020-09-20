{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Afa.Convert.CnfAfa (CnfAfa(..), Lit(..), tseytin) where

import Data.Bifunctor
import Control.Monad.ST
import Control.Monad.State
import Control.Monad.Writer
import Data.Array
import Data.Array.Unsafe
import Data.Monoid
import qualified Afa.TreeDag.Patterns.Builder as THB
import Data.Functor.Foldable.Dag.Consing (nocons, runNoConsMonadT)
import Data.Functor.Foldable.Dag.Monadic (cataScanM)
import Data.Functor.Foldable.Dag.TreeHybrid (treeDagCataScanMAlg)

import Afa.Functor
import Afa


data Lit = Lit
  { ix :: Int
  , isPositive :: Bool
  } deriving Show


data CnfAfa = CnfAfa
  { states :: Array Int Lit
  , varCount :: Int
  , clauses :: Array Int [Lit]
  }


tseytin :: Int -> Afa -> CnfAfa
tseytin varCount (Afa terms states) = CnfAfa
  { Afa.Convert.CnfAfa.states = fmap ((litMap!) . (ixMap!)) states
  , Afa.Convert.CnfAfa.varCount = varCount
  , clauses = listArray (0, length clauses - 1) clauses
  }
  where
  stateCount = rangeSize$ bounds states

  (ixMap, terms') = dagTerms terms
  litMap :: Array Int Lit
  (litMap, clauses) = runST$ runCountLogT (stateCount + varCount)$
    cataScanM tseytin_alg (listArray (0, length terms' - 1) terms')
    >>= lift . unsafeFreeze

  tseytin_alg :: Monad m => Term Lit -> CountLog [Lit] m Lit
  tseytin_alg (State q) = CountLog$ return (Lit q True)
  tseytin_alg (Var v) = return (Lit (stateCount + v) True)
  tseytin_alg (Not (Lit ix isPositive)) = return$ Lit ix$ not isPositive
  tseytin_alg (And lits) = CountLog$ do
    ix <- get
    put$ ix + 1
    let neg_out = Lit ix False
        clauses = map (: [neg_out]) lits
    lift$ tell (Endo (clauses ++))
    return$ Lit ix True
  tseytin_alg (Or lits) = CountLog$ do
    ix <- get
    put$ ix + 1
    let clause = Lit ix False : lits
    lift$ tell (Endo (clause :))
    return$ Lit ix True
  tseytin_alg LFalse = error
    "Tseytin does not support LFalse, please use removeFalseStates and simplify \
    \until a fixpoint is reached"
  tseytin_alg LTrue = error
    "Tseytin does not support LTrue, please use removeTrueStates and simplify \
    \until a fixpoint is reached"


dagTerms :: Array Int THB.Term -> (Array Int Int, [Term Int])
dagTerms terms = runST$ runNoConsMonadT$
  cataScanM (treeDagCataScanMAlg nocons) terms >>= lift . unsafeFreeze


newtype CountLog x m a = CountLog (StateT Int (WriterT (Endo [x]) m) a)
  deriving (Functor, Applicative, Monad)
instance MonadTrans (CountLog x) where
  lift = CountLog . lift . lift


runCountLogT :: Monad m => Int -> CountLog x m a -> m (a, [x])
runCountLogT offset (CountLog action) =
  fmap (second (`appEndo` []))$ runWriterT$ evalStateT action offset
