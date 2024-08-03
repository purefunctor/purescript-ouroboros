module PureScript.Surface.Error where

import Prelude

import PureScript.CST.Errors (RecoveredError)

newtype LowerError = LowerError RecoveredError

derive newtype instance Eq LowerError

class IntoLowerError e where
  intoLowerError ∷ e → LowerError

instance IntoLowerError Void where
  intoLowerError = absurd

instance IntoLowerError RecoveredError where
  intoLowerError = LowerError
