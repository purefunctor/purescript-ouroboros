module PureScript.Scope.Types where

import Prelude

import Foreign.Object (Object)
import PureScript.Surface.Types as SST

type BinderRef = SST.BinderIndex
type LetBindingRef = SST.LetBindingIndex
type DeclarationRef = SST.DeclarationIndex
type TypeVarRef = SST.TypeVarBindingIndex

type TopLevelRefs =
  { values ∷ Object DeclarationRef
  }

data ScopeNode
  = RootScope
  | TopLevel ScopeNode TopLevelRefs
  | Binders ScopeNode (Object BinderRef)
  | LetBound ScopeNode (Object LetBindingRef)
  | TypeVar ScopeNode String TypeVarRef
  | JoinScope ScopeNode ScopeNode

derive instance Eq ScopeNode
