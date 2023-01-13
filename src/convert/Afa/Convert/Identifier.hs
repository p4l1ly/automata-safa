module Afa.Convert.Identifier where

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
