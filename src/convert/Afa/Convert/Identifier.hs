{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module Afa.Convert.Identifier where

import qualified Afa.Lib as Lib
import Data.String.Interpolate.IsString (i)
import qualified Data.Text as T
import Data.Word

class Identify a where
  identify :: a -> T.Text

instance Identify T.Text where
  identify = id

instance Identify Word32 where
  identify = T.pack . show

instance Identify Word8 where
  identify = T.pack . show

instance Identify q => Identify (Lib.AddInitQ q) where
  identify Lib.AddInitInit = "I"
  identify (Lib.AddInitOther q) = [i|O#{identify q}|]

instance Identify q => Identify (Lib.QomboQ q) where
  identify (Lib.QomboQ j q) = [i|#{j}_#{identify q}|]
