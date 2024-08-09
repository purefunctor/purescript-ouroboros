module PureScript.Interface.Error where

import Prelude

import PureScript.CST.Types (Ident, Proper)
import PureScript.Interface.Types (ConstructorKind, TypeKind, ValueKind)

data InterfaceError
  = MissingConstructor Proper
  | MissingType Proper
  | MissingValue Ident
  | DuplicateConstructor ConstructorKind ConstructorKind
  | DuplicateType TypeKind TypeKind
  | DuplicateValue ValueKind ValueKind

derive instance Eq InterfaceError
derive instance Ord InterfaceError
