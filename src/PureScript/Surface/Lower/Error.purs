module PureScript.Surface.Lower.Error where

import Prelude

import PureScript.CST.Errors (RecoveredError)

class IntoRecoveredError e where
  intoRecoveredError ∷ e → RecoveredError

instance IntoRecoveredError Void where
  intoRecoveredError = absurd

instance IntoRecoveredError RecoveredError where
  intoRecoveredError = identity
