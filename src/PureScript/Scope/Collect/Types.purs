module PureScript.Scope.Collect.Types where

import Prelude

import Data.Maybe (Maybe(..))
import Partial.Unsafe (unsafeCrashWith)
import PureScript.Id (Id, IdMap)
import PureScript.Id as IdMap
import PureScript.Scope.Types (ScopeNode)
import PureScript.Surface.Syntax.Tree as SST

type ScopeNodesInner =
  { expr ∷ IdMap SST.Expr ScopeNode
  , binder ∷ IdMap SST.Binder ScopeNode
  , type_ ∷ IdMap SST.Type ScopeNode
  }

newtype ScopeNodes = ScopeNodes ScopeNodesInner

derive newtype instance Eq ScopeNodes

getScopeNode ∷ ∀ t. (ScopeNodesInner → IdMap t ScopeNode) → Id t → ScopeNodes → ScopeNode
getScopeNode get id (ScopeNodes scopeNodes) = case IdMap.get id (get scopeNodes) of
  Just scopeNode →
    scopeNode
  Nothing →
    unsafeCrashWith "invariant violated: missing ScopeNode"

getExprScopeNode ∷ Id SST.Expr → ScopeNodes → ScopeNode
getExprScopeNode = getScopeNode _.expr

getBinderScopeNode ∷ Id SST.Binder → ScopeNodes → ScopeNode
getBinderScopeNode = getScopeNode _.binder

getTypeScopeNode ∷ Id SST.Type → ScopeNodes → ScopeNode
getTypeScopeNode = getScopeNode _.type_