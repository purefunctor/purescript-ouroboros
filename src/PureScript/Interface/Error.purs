module PureScript.Interface.Error where

import Prelude

import PureScript.CST.Types (Ident, Proper)

data InterfaceError
  = MissingMember Proper
  | MissingType Proper
  | MissingValue Ident

derive instance Eq InterfaceError
derive instance Ord InterfaceError
