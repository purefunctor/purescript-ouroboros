module PureScript.Scope.Types where

import Data.Maybe (Maybe)
import Foreign.Object (Object)
import PureScript.Surface.Types as SST

type BinderRef = SST.BinderIndex

type LetBindingRef =
  { signatureIndex ∷ Maybe SST.LetBindingIndex
  , nameIndices ∷ Array SST.LetBindingIndex
  }

data ScopeNode
  = RootScope
  | Binders ScopeNode (Object BinderRef)
  | LetBound ScopeNode (Object LetBindingRef)
