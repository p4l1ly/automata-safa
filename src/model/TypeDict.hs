{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module TypeDict (Name, TypeDict (..), Tag, Get, NotFound, d, d', g, g') where

import Data.Functor ((<&>))
import GHC.TypeLits (Symbol)
import Language.Haskell.TH (Exp (AppTypeE, VarE), TyLit (StrTyLit), Type (AppT, ConT, LitT, VarT), lookupTypeName, lookupValueName)
import Language.Haskell.TH.Quote (QuasiQuoter (..))
import Lift (Lift)

data NotFound (k :: Symbol)
data Named (a :: Symbol) (b :: k) = Named

type family Name (a :: Symbol) (b :: k) :: Named a b where
  Name a b = 'Named

data TypeDict where
  End :: TypeDict
  (:+:) :: Named a b -> TypeDict -> TypeDict
  LiftTags :: TypeDict -> TypeDict
infixr 1 :+:

type family Tag (sym :: Symbol) (dict :: TypeDict) :: * where
  Tag sym End = NotFound sym
  Tag sym (LiftTags rest) = Lift (Tag sym rest)
  Tag sym ((_ :: Named sym val) :+: rest) = val
  Tag sym (_ :+: rest) = Tag sym rest

type family Get (sym :: Symbol) (dict :: TypeDict) :: k where
  Get sym End = NotFound sym
  Get sym (LiftTags rest) = Get sym rest
  Get sym ((_ :: Named sym val) :+: rest) = val
  Get sym (_ :+: rest) = Get sym rest

d :: QuasiQuoter
d =
  QuasiQuoter
    { quoteType = \tag -> do
        d <- lookupTypeName "d"
        case d of
          Just d -> return $ AppT (AppT (ConT ''Tag) (LitT (StrTyLit tag))) (VarT d)
          Nothing -> error "d: type d not in scope"
    , quoteExp = \str -> do
        let (fnName, '|' : tag) = break (== '|') str
        d <- lookupTypeName "d"
        fn <- lookupValueName fnName
        case (d, fn) of
          (Nothing, _) -> error "d: type d not in scope"
          (_, Nothing) -> error $ "d: function " ++ fnName ++ " not in scope"
          (Just d, Just fn) ->
            return $
              AppTypeE (VarE fn) (AppT (AppT (ConT ''Tag) (LitT (StrTyLit tag))) (VarT d))
    , quoteDec = error "d can quote only types"
    , quotePat = error "d can quote only types"
    }

d' :: QuasiQuoter
d' =
  QuasiQuoter
    { quoteType = \tag -> do
        d <- lookupTypeName "d'"
        case d of
          Just d -> return $ AppT (AppT (ConT ''Tag) (LitT (StrTyLit tag))) (VarT d)
          Nothing -> error "d': type d' not in scope"
    , quoteExp = \str -> do
        let (fnName, '|' : tag) = break (== '|') str
        d <- lookupTypeName "d'"
        fn <- lookupValueName fnName
        case (d, fn) of
          (Nothing, _) -> error "d': type d' not in scope"
          (_, Nothing) -> error $ "d': function " ++ fnName ++ " not in scope"
          (Just d, Just fn) ->
            return $
              AppTypeE (VarE fn) (AppT (AppT (ConT ''Tag) (LitT (StrTyLit tag))) (VarT d))
    , quoteDec = error "d' can quote only types"
    , quotePat = error "d' can quote only types"
    }

g :: QuasiQuoter
g =
  QuasiQuoter
    { quoteType = \tag -> do
        d <- lookupTypeName "d"
        case d of
          Just d -> return $ AppT (AppT (ConT ''Get) (LitT (StrTyLit tag))) (VarT d)
          Nothing -> error "g: type d not in scope"
    , quoteExp = \str -> do
        let (fnName, '|' : tag) = break (== '|') str
        d <- lookupTypeName "d"
        fn <- lookupValueName fnName
        case (d, fn) of
          (Nothing, _) -> error "g: type d not in scope"
          (_, Nothing) -> error $ "g: function " ++ fnName ++ " not in scope"
          (Just d, Just fn) ->
            return $
              AppTypeE (VarE fn) (AppT (AppT (ConT ''Get) (LitT (StrTyLit tag))) (VarT d))
    , quoteDec = error "g can quote only types"
    , quotePat = error "g can quote only types"
    }

g' :: QuasiQuoter
g' =
  QuasiQuoter
    { quoteType = \tag -> do
        d <- lookupTypeName "d'"
        case d of
          Just d -> return $ AppT (AppT (ConT ''Get) (LitT (StrTyLit tag))) (VarT d)
          Nothing -> error "g': type d' not in scope"
    , quoteExp = \str -> do
        let (fnName, '|' : tag) = break (== '|') str
        d <- lookupTypeName "d'"
        fn <- lookupValueName fnName
        case (d, fn) of
          (Nothing, _) -> error "g': type d' not in scope"
          (_, Nothing) -> error $ "g': function " ++ fnName ++ " not in scope"
          (Just d, Just fn) ->
            return $
              AppTypeE (VarE fn) (AppT (AppT (ConT ''Get) (LitT (StrTyLit tag))) (VarT d))
    , quoteDec = error "g can quote only types"
    , quotePat = error "g can quote only types"
    }
