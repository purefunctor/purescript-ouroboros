module PureScript.Scope.Types where

import Prelude

import Foreign.Object (Object)
import PureScript.Surface.Types as SST

type BinderRef = SST.BinderIndex
type LetBindingRef = SST.LetBindingIndex
type DeclarationRef = SST.DeclarationIndex
type TypeVarRef = SST.TypeVarBindingIndex
type ConstructorRef = SST.ConstructorIndex
type NewtypeRef = SST.NewtypeIndex

newtype TopLevelRefs = TopLevelRefs
  { dataConstructors ∷ Object ConstructorRef
  , newtypeConstructors ∷ Object NewtypeRef
  , types ∷ Object DeclarationRef
  , values ∷ Object DeclarationRef
  }

derive instance Eq TopLevelRefs

data ScopeNode
  = RootScope
  | TopLevel ScopeNode TopLevelRefs
  | Binders ScopeNode (Object BinderRef)
  | LetBound ScopeNode (Object LetBindingRef)
  | TypeVar ScopeNode String TypeVarRef
  | JoinScope ScopeNode ScopeNode

derive instance Eq ScopeNode
