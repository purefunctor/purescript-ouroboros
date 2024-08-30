module PureScript.Scope.Collect.State where

import Prelude

import Control.Monad.ST (ST)
import Control.Monad.ST.Ref (STRef)
import Control.Monad.ST.Ref as STRef
import Data.HashMap (HashMap)
import Data.HashMap as HashMap
import PureScript.Id (Id)
import PureScript.Scope.Collect.Types (ScopeNodes(..))
import PureScript.Scope.Types (ScopeNode(..))
import PureScript.Surface.Syntax.Tree as SST
import Safe.Coerce (coerce)

type State r =
  { scope ∷ STRef r ScopeNode
  , expr ∷ STRef r (HashMap (Id SST.Expr) ScopeNode)
  , binder ∷ STRef r (HashMap (Id SST.Binder) ScopeNode)
  , type_ ∷ STRef r (HashMap (Id SST.Type) ScopeNode)
  }

empty ∷ ∀ r. ST r (State r)
empty = do
  scope ← STRef.new RootScope
  expr ← STRef.new HashMap.empty
  binder ← STRef.new HashMap.empty
  type_ ← STRef.new HashMap.empty
  pure { scope, expr, binder, type_ }

freeze ∷ ∀ r. State r → ST r ScopeNodes
freeze state = do
  expr ← STRef.read state.expr
  binder ← STRef.read state.binder
  type_ ← STRef.read state.type_
  pure $ coerce { expr, binder, type_ }

currentScope ∷ ∀ r. State r → ST r ScopeNode
currentScope state = STRef.read state.scope

pushScope ∷ ∀ r. State r → ScopeNode → ST r Unit
pushScope state scope = void $ STRef.write scope state.scope

assignScopeNode ∷ ∀ r t. (State r → STRef r (HashMap (Id t) ScopeNode)) → State r → Id t → ST r Unit
assignScopeNode get state id = do
  v ← currentScope state
  void $ STRef.modify (HashMap.insert id v) (get state)

withRevertingScope ∷ ∀ r a. State r → ST r a → ST r a
withRevertingScope state action = do
  previousScope ← currentScope state
  result ← action
  pushScope state previousScope
  pure result