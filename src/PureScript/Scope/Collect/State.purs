module PureScript.Scope.Collect.State where

import Prelude

import Control.Monad.ST (ST)
import Control.Monad.ST.Ref (STRef)
import Control.Monad.ST.Ref as STRef
import PureScript.Id (Id)
import PureScript.Id.STMap (STIdMap)
import PureScript.Id.STMap as STIdMap
import PureScript.Scope.Collect.Types (ScopeNodes(..))
import PureScript.Scope.Types (ScopeNode(..))
import PureScript.Surface.Syntax.Tree as SST
import Safe.Coerce (coerce)

type State r =
  { scope ∷ STRef r ScopeNode
  , expr ∷ STIdMap r SST.Expr ScopeNode
  , binder ∷ STIdMap r SST.Binder ScopeNode
  , type_ ∷ STIdMap r SST.Type ScopeNode
  }

empty ∷ ∀ r. ST r (State r)
empty = do
  scope ← STRef.new RootScope
  expr ← STIdMap.empty
  binder ← STIdMap.empty
  type_ ← STIdMap.empty
  pure { scope, expr, binder, type_ }

freeze ∷ ∀ r. State r → ST r ScopeNodes
freeze state = do
  expr ← STIdMap.freeze state.expr
  binder ← STIdMap.freeze state.binder
  type_ ← STIdMap.freeze state.type_
  pure $ coerce { expr, binder, type_ }

currentScope ∷ ∀ r. State r → ST r ScopeNode
currentScope state = STRef.read state.scope

pushScope ∷ ∀ r. State r → ScopeNode → ST r Unit
pushScope state scope = void $ STRef.write scope state.scope

assignScopeNode ∷ ∀ r t. (State r → STIdMap r t ScopeNode) → State r → Id t → ST r Unit
assignScopeNode get state id = do
  v ← currentScope state
  STIdMap.set id v (get state)

withRevertingScope ∷ ∀ r a. State r → ST r a → ST r a
withRevertingScope state action = do
  previousScope ← currentScope state
  result ← action
  pushScope state previousScope
  pure result