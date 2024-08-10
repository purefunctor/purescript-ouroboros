module PureScript.Scope.Types where

import Prelude

import Data.Maybe (Maybe(..))
import Foreign.Object (Object)
import Foreign.Object as Object
import PureScript.CST.Types (Ident(..))
import PureScript.Driver.Query.Stable (FileId)
import PureScript.Interface.Types (Export, Interface(..), ValueKind)
import PureScript.Surface.Syntax.Tree as SST

data ScopeNode
  = RootScope
  | Binders ScopeNode (Object SST.BinderId)
  | LetBound ScopeNode (Object SST.LetBindingId)
  | TypeVar ScopeNode String SST.TypeVarBindingId
  | JoinScope ScopeNode ScopeNode

derive instance Eq ScopeNode

type OnScopeNode r =
  { onBinders ∷ Object SST.BinderId → Maybe r
  , onLetBound ∷ Object SST.LetBindingId → Maybe r
  , onTypeVar ∷ String → SST.TypeVarBindingId → Maybe r
  }

defaultOnScopeNode ∷ ∀ r. OnScopeNode r
defaultOnScopeNode =
  { onBinders: \_ → Nothing
  , onLetBound: \_ → Nothing
  , onTypeVar: \_ _ → Nothing
  }

searchCore ∷ ∀ r. OnScopeNode r → ScopeNode → Maybe r
searchCore k n = go n
  where
  orGo ∷ ScopeNode → Maybe r → Maybe r
  orGo parent = case _ of
    v@(Just _) → v
    Nothing → go parent

  go ∷ ScopeNode → Maybe r
  go = case _ of
    RootScope →
      Nothing
    Binders parent binders →
      k.onBinders binders # orGo parent
    LetBound parent letBound →
      k.onLetBound letBound # orGo parent
    TypeVar parent varName varId →
      k.onTypeVar varName varId # orGo parent
    JoinScope leftParent rightParent →
      Nothing # orGo leftParent # orGo rightParent

data ExprIdentResolution
  = ExprIdentBinder SST.BinderId
  | ExprIdentLetBound SST.LetBindingId
  | ExprIdentLocal (Export ValueKind)
  | ExprIdentImport FileId (Export ValueKind)

scopeNodeExprIdent ∷ Ident → ScopeNode → Maybe ExprIdentResolution
scopeNodeExprIdent (Ident i) = do
  searchCore $ defaultOnScopeNode
    { onBinders = Object.lookup i >=> ExprIdentBinder >>> Just
    , onLetBound = Object.lookup i >=> ExprIdentLetBound >>> Just
    }

interfaceExprIdent ∷ Ident → Maybe FileId → Interface → Maybe ExprIdentResolution
interfaceExprIdent (Ident ident) maybeFileId (Interface { values }) = do
  valueKind ← Object.lookup ident values
  case maybeFileId of
    Just fileId →
      pure $ ExprIdentImport fileId valueKind
    Nothing →
      pure $ ExprIdentLocal valueKind
