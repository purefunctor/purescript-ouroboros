module PureScript.Scope.Types where

import Prelude

import Foreign.Object (Object)
import PureScript.Interface.Types (Interface)
import PureScript.Surface.Syntax.Tree as SST

data ScopeNode
  = RootScope
  | TopLevel ScopeNode Interface
  | Binders ScopeNode (Object SST.BinderId)
  | LetBound ScopeNode (Object SST.LetBindingId)
  | TypeVar ScopeNode String SST.TypeVarBindingId
  | JoinScope ScopeNode ScopeNode

derive instance Eq ScopeNode
