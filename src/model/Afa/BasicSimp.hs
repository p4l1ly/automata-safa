module Afa.BasicSimp where

import qualified Data.HashMap.Strict as M
import Data.Vector.Mutable as V
import Data.IORef

newtype RefIx = RefIx Int deriving (Show, Eq)

-- API: references will be moved as in Rust or copied or abandoned. It will be
-- unchecked - we cannot forbid the use of a moved reference but it is not guaranteed
-- that it will refer to the same term all the time.

data Subterm q v = State q | Var v | Nonterminal RefIx
data Term q v
  = Not (Subterm q v)
  | And [Subterm q v]
  | Or [Subterm q v]

data Ref (q :: *) (v :: *) =
  { refId :: RefIx
  , refTerm :: Term q v
  , refState :: Maybe q
  , parents :: [RefIx]
  , externalCount :: Int
  } deriving Show

data ConsData (q :: *) (v :: *) = Cons
  { tCons :: M.HashMap (Term q v) RefIx
  , refs :: V.IOVector (Ref q v)
  , refsLen :: Int
  , freeList :: [RefIx]
  }

newtype ConsT (ioDepth :: Pean) q v m a = ConsT (ReaderT (IORef (ConsData q v)) m a)

add :: Term q v -> ConsData q v -> IO (ConsData q v)


-- external term reference is RefIx
-- Term has n-ary Ands and Ors
-- states:
--   - count
--   - q2i
--   - i2q
--   - i2r
