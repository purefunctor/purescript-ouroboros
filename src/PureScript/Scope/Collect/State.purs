module PureScript.Scope.Collect.State where

import Prelude

import Control.Monad.ST (ST)
import Control.Monad.ST.Ref (STRef)
import Control.Monad.ST.Ref as STRef
import PureScript.Id (Id(..), IdMap(..))
import PureScript.Scope.Collect.Types (ScopeNodes(..))
import PureScript.Scope.Types (ScopeNode(..))
import PureScript.Utils.Mutable.STIntMap (STIntMap)
import PureScript.Utils.Mutable.STIntMap as STIntMap
import Safe.Coerce (coerce)

type State r =
  { scope ∷ STRef r ScopeNode
  , expr ∷ STIntMap r ScopeNode
  , binder ∷ STIntMap r ScopeNode
  , type_ ∷ STIntMap r ScopeNode
  }

empty ∷ ∀ r. ST r (State r)
empty = do
  scope ← STRef.new RootScope
  expr ← STIntMap.empty
  binder ← STIntMap.empty
  type_ ← STIntMap.empty
  pure { scope, expr, binder, type_ }

freeze ∷ ∀ r. State r → ST r ScopeNodes
freeze state = do
  expr ← STIntMap.freeze state.expr
  binder ← STIntMap.freeze state.binder
  type_ ← STIntMap.freeze state.type_
  pure $ coerce { expr, binder, type_ }

currentScope ∷ ∀ r. State r → ST r ScopeNode
currentScope state = STRef.read state.scope

pushScope ∷ ∀ r. State r → ScopeNode → ST r Unit
pushScope state scope = void $ STRef.write scope state.scope

assignScopeNode ∷ ∀ r t. (State r → STIntMap r ScopeNode) → State r → Id t → ST r Unit
assignScopeNode get state (Id i) = do
  v ← currentScope state
  STIntMap.set i v (get state)

withRevertingScope ∷ ∀ r a. State r → ST r a → ST r a
withRevertingScope state action = do
  previousScope ← currentScope state
  result ← action
  pushScope state previousScope
  pure result