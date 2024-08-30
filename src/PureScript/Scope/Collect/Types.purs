module PureScript.Scope.Collect.Types where

import Prelude

import Data.HashMap (HashMap)
import Data.HashMap as HashMap
import Data.Maybe (Maybe(..))
import Partial.Unsafe (unsafeCrashWith)
import PureScript.Id (Id)
import PureScript.Scope.Types (ScopeNode)
import PureScript.Surface.Syntax.Tree as SST

type ScopeNodesInner =
  { expr ∷ HashMap (Id SST.Expr) ScopeNode
  , binder ∷ HashMap (Id SST.Binder) ScopeNode
  , type_ ∷ HashMap (Id SST.Type) ScopeNode
  }

newtype ScopeNodes = ScopeNodes ScopeNodesInner

derive newtype instance Eq ScopeNodes

getScopeNode ∷ ∀ t. (ScopeNodesInner → HashMap (Id t) ScopeNode) → Id t → ScopeNodes → ScopeNode
getScopeNode get id (ScopeNodes scopeNodes) = case HashMap.lookup id (get scopeNodes) of
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