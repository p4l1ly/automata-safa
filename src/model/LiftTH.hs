{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}

module LiftTH where

import Control.Monad.Trans (MonadTrans (..))
import Data.Functor ((<&>))
import qualified Data.Map.Strict as M
import Data.Traversable (for)
import Language.Haskell.TH.Datatype (applySubstitution)
import Language.Haskell.TH.Syntax (
  Body (NormalB),
  Clause (Clause),
  Dec (ClassD, FunD, InstanceD, SigD),
  Exp (AppE, AppTypeE, VarE),
  Info (ClassI),
  Name,
  Pat (VarP),
  Q,
  TyVarBndr (KindedTV, PlainTV),
  Type (AppT, ArrowT, ConT, ForallT, VarT),
  newName,
  reify,
 )
import Lift (Lift)

-- |
-- ```
-- instance (X k p1 ... pn m, MonadTrans mt, Monad m) => X (Lift k) p1 ... pn (mt m) where
--   method1 p1 ... pm = lift (method1 @k p1 ... pm)
--   ...
-- ```
makeLiftable :: Name -> Q [Dec]
makeLiftable clsName = do
  ClassI (ClassD ctx _ bndrs _ methods) _ <- reify clsName
  mt <- VarT <$> newName "mt"
  let vars@(k : rest) = map (VarT . (\case PlainTV na -> na; KindedTV na _ -> na)) bndrs
      m = last rest
      k' = AppT (ConT ''Lift.Lift) k
      m' = AppT mt m
      vars' = k' : init rest ++ [m']
      sub = M.fromList [(kName, k'), (mName, m')] where VarT kName = k; VarT mName = m
      ctx' = map (applySubstitution sub) ctx
      preds = [foldl AppT (ConT clsName) vars, AppT (ConT ''MonadTrans) mt, AppT (ConT ''Monad) m] ++ ctx'
  methods' <- for methods \(SigD fnname typ) -> do
    params <- for [1 .. arity typ] \i -> newName ("p" ++ show i)
    let base = foldl AppE (AppTypeE (VarE fnname) k) (map VarE params)
    return $ FunD fnname [Clause (map VarP params) (NormalB (AppE (VarE 'lift) base)) []]
  return . (: []) $
    InstanceD
      Nothing
      preds
      (foldl AppT (ConT clsName) vars')
      methods'

arity :: Type -> Integer
arity = \case
  ForallT _ _ rest -> arity rest
  AppT (AppT ArrowT _) rest -> arity rest + 1
  _ -> 0
