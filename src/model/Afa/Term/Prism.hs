{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}

module Afa.Term.Prism where

import Prelude hiding (not, or, and)

import Control.Lens.Prism
import Control.Lens.Fold (preview)
import Control.Lens.Review (review)
import Data.Functor.Compose

import qualified Afa.Term as T
import Data.Functor.Tree (TreeBase, pattern BNode)

class PositiveTerm f where
  or :: Prism' (f a) [a]
  and :: Prism' (f a) [a]

class PositiveTerm f => LitPositiveTerm f where
  ltrue :: Prism' (f a) ()

class PositiveTerm f => Term f where
  not :: Prism' (f a) a

class (Term f, LitPositiveTerm f) => LitTerm f where
  lfalse :: Prism' (f a) ()

pattern LFalse :: LitTerm f => f a
pattern LFalse <- (preview lfalse -> Just ()) where LFalse = review lfalse ()

pattern LTrue :: LitPositiveTerm f => f a
pattern LTrue <- (preview ltrue -> Just ()) where LTrue = review ltrue ()

pattern Not :: Term f => a -> f a
pattern Not a <- (preview not -> Just a) where Not a = review not a

pattern Or :: PositiveTerm f => [a] -> f a
pattern Or a <- (preview or -> Just a) where Or a = review or a

pattern And :: PositiveTerm f => [a] -> f a
pattern And a <- (preview and -> Just a) where And a = review and a

instance PositiveTerm (T.Term p) where
  or = prism T.Or$ \case T.Or a -> Right a; x -> Left x
  and = prism T.And$ \case T.And a -> Right a; x -> Left x

instance LitPositiveTerm (T.Term p) where
  ltrue = prism (const T.LTrue)$ \case T.LTrue -> Right (); x -> Left x

instance PositiveTerm f => PositiveTerm (TreeBase f ix) where
  or = prism (BNode . Or)$ \case BNode (Or a) -> Right a; x -> Left x
  and = prism (BNode . And)$ \case BNode (And a) -> Right a; x -> Left x

instance LitPositiveTerm f => LitPositiveTerm (TreeBase f ix) where
  ltrue = prism (BNode . const LTrue)$ \case BNode LTrue -> Right (); x -> Left x

instance Term f => Term (TreeBase f ix) where
  not = prism (BNode . Not)$ \case BNode (Not a) -> Right a; x -> Left x

instance LitTerm f => LitTerm (TreeBase f ix) where
  lfalse = prism (BNode . const LFalse)$ \case BNode LFalse -> Right (); x -> Left x

positiveIsRecursive :: PositiveTerm f => f a -> Bool
positiveIsRecursive (And _) = True
positiveIsRecursive (Or _) = True
positiveIsRecursive _ = False

isRecursive :: Term f => f a -> Bool
isRecursive (Not _) = True
isRecursive x = positiveIsRecursive x
