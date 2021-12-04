{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

module Afa.Convert.Separated.ToDnf where

import Afa.Convert.Separated.Model
import Afa.Lib (listArray')
import Afa.Lib.LiftArray
import qualified Afa.Term.Bool as BTerm
import qualified Afa.Term.Mix as MTerm
import Control.Lens
import Control.Monad.ST
import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.State
import Control.Monad.Trans.Writer
import Control.RecursionSchemes.Lens
import Control.RecursionSchemes.Utils.NoCons
import Data.Array
import Data.Array.ST
import Data.Bifunctor
import Data.Either
import Data.List.NonEmpty (NonEmpty ((:|)))
import qualified Data.List.NonEmpty as NE
import Data.Monoid (Endo (..))
import Data.Semigroup (Max (..))
import Data.Traversable
import Data.Void
import Debug.Trace

distributeTopOrs :: Show p => Afa p -> Maybe (Afa p)
distributeTopOrs afa@Afa{qterms, states} = traceShow afa $ do
  scanResult <&> \(ixMap, qterms') ->
    afa
      { qterms = listArray' qterms'
      , states = (`fmap` states) $
          concatMap $ \case
            (a, Just t) -> case ixMap ! t of
              Left xs -> map (\x -> (a, Just x)) xs
              Right x -> [(a, Just x)]
            x -> [x]
      }
  where
    scanResult = runST action
    action :: forall s. ST s (Maybe (Array Int (Either [Int] Int), [MTerm.Term Void Int Int]))
    action = runMaybeT $ runNoConsT $ cataScanT' @(LLSTArray s) traversed alg qterms

    alg ::
      MTerm.Term Void Int (Either [Int] Int) ->
      NoConsT (MTerm.Term Void Int Int) (MaybeT (ST s)) (Either [Int] Int)
    alg = \case
      MTerm.Or ts -> Left . NE.toList <$> assertRights ts
      MTerm.And ts -> assertRights ts >>= fmap Right . nocons . MTerm.And
      x -> fmap Right $ nocons $ MTerm.appMTFun MTerm.mtfun0{MTerm.mtfunT = undefined} x
      where
        assertRights = lift . MaybeT . return . mapM (either (const Nothing) Just)

type MyMonad m = StateT Int (WriterT (Endo [Conjuncts]) (NoConsT (MTerm.Term Void Int Int) m))

type Conjuncts = [(Maybe Int, Maybe Int)]

newMTerm :: Monad m => MTerm.Term Void Int Int -> MyMonad m Int
newMTerm = lift . lift . nocons

newStateTrans :: Monad m => Conjuncts -> MyMonad m ()
newStateTrans cs = lift $ tell $ Endo (cs :)

newState :: Monad m => Conjuncts -> MyMonad m Int
newState cs = do
  q <- get
  put $ q + 1
  newStateTrans cs
  newMTerm $ MTerm.State q

newPhantomState :: Monad m => Int -> Conjuncts -> MyMonad m Int
newPhantomState epsilon transitions = do
  q <- get
  put $ q + 1
  tq <- newMTerm $ MTerm.State q
  newStateTrans $ (Just epsilon, Just tq) : transitions
  return tq

epsilonize :: Afa Int -> Afa Int
epsilonize afa@Afa{aterms, qterms, states} =
  afa
    { aterms = aterms'
    , qterms = listArray' qterms'
    , states =
        listArray (0, stateCount - 1) $
          elems oldStates' ++ newStates
    }
  where
    acount = snd (bounds aterms) + 1
    epsilonP = getMax $ 1 + foldMap (BTerm.appMTFol BTerm.mtfol0{BTerm.mtfolP = Max}) aterms
    epsilon = acount
    nepsilon = 1 + epsilon
    bOffset = 1 + nepsilon
    aterms' =
      listArray
        (0, acount * 2 + 1)
        $ concat
          [ elems aterms
          , [BTerm.Predicate epsilonP, BTerm.Not epsilon]
          , map (\x -> BTerm.And $ x :| [nepsilon]) [0 .. acount - 1]
          ]

    (((oldStates', stateCount), (`appEndo` []) -> newStates), qterms') = runST action
      where
        action :: forall s. ST s (((Array Int Conjuncts, Int), Endo [Conjuncts]), [MTerm.Term Void Int Int])
        action = runNoConsT $
          runWriterT $
            flip runStateT (snd (bounds states) + 1) $ do
              ixMap <- ($ qterms) $
                cataScanT' @(LLLSTArray s) traversed $ \case
                  MTerm.LTrue -> newMTerm MTerm.LTrue
                  MTerm.And xs -> newMTerm $ MTerm.And xs
                  MTerm.State q -> do
                    tq <- newMTerm $ MTerm.State q
                    newPhantomState epsilon [(Just nepsilon, Just tq)]
                  MTerm.Or xs -> newState $ NE.toList xs <&> \x -> (Just epsilon, Just x)

              for states $
                mapM $ \case
                  (Nothing, Nothing) -> return (Nothing, Nothing)
                  (Nothing, Just t) -> return (Just epsilon, Just $ ixMap ! t)
                  (Just b, Nothing) -> do
                    tq <- newPhantomState epsilon [(Just $ b + bOffset, Nothing)]
                    return (Just epsilon, Just tq)
                  (Just b, Just t) -> do
                    tq <- newPhantomState epsilon [(Just $ b + bOffset, Nothing)]
                    ttq <- newMTerm $ MTerm.And $ ixMap ! t :| [tq]
                    return (Just epsilon, Just ttq)
