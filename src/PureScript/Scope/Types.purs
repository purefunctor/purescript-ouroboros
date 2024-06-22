module PureScript.Scope.Types where

import Foreign.Object (Object)
import PureScript.Surface.Types as SST

type BinderRef = SST.BinderIndex
type LetBindingRef = SST.LetBindingIndex

data ScopeNode
  = RootScope
  | Binders ScopeNode (Object BinderRef)
  | LetBound ScopeNode (Object LetBindingRef)
  | JoinScope ScopeNode ScopeNode
