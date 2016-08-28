module Evaluate.Error where

import Data.Text (Text)
import qualified Data.Text as Text

data Error
  = FromMonadFail String

error2Text :: Error -> Text
error2Text (FromMonadFail s) = Text.pack s
