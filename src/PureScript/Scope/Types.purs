module PureScript.Scope.Types where

import Prelude

import Foreign.Object (Object)
import PureScript.Interface.Types (Interface)
import PureScript.Surface.Types as SST

data ScopeNode
  = RootScope
  | TopLevel ScopeNode Interface
  | Binders ScopeNode (Object SST.BinderIndex)
  | LetBound ScopeNode (Object SST.LetBindingIndex)
  | TypeVar ScopeNode String SST.TypeVarBindingIndex
  | JoinScope ScopeNode ScopeNode

derive instance Eq ScopeNode
