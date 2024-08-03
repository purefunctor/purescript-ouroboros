module PureScript.Diagnostics.Types where

import Prelude

import PureScript.CST.Errors (ParseError, RecoveredError)
import PureScript.Interface.Error (InterfaceError)

newtype Diagnostic = Diagnostic
  { kind ∷ DiagnosticKind
  }

derive newtype instance Eq Diagnostic
derive newtype instance Ord Diagnostic

data DiagnosticKind
  = DiagnosticParseError ParseError
  | DiagnosticRecoveredError RecoveredError
  | DiagnosticInterfaceError InterfaceError

derive instance Eq DiagnosticKind
derive instance Ord DiagnosticKind
