module PureScript.Scope.Resolve where

import Prelude

import Control.Alt ((<|>))
import Control.Monad.ST (ST)
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import PureScript.CST.Types (Ident, ModuleName)
import PureScript.Driver.Query.Stable (FileId)
import PureScript.Interface.Collect as InterfaceCollect
import PureScript.Scope.Collect as ScopeCollect
import PureScript.Scope.Collect.Types (getExprScopeNode)
import PureScript.Scope.Resolve.State as State
import PureScript.Scope.Resolve.Types (Resolutions)
import PureScript.Scope.Types
  ( ExprIdentResolution
  , ScopeNode
  , interfaceExprIdent
  , scopeNodeExprIdent
  )
import PureScript.Surface.Syntax.Traversal
  ( OnPureScript
  , Rewrite
  , defaultVisitorM
  , topDownTraversal
  , traverseModule
  )
import PureScript.Surface.Syntax.Tree (Annotation(..), Expr(..), Module, QualifiedName(..))

type Result = Resolutions

unqualifiedExprIdent
  ∷ ∀ r. Ident → ScopeNode → InterfaceCollect.Result → ST r (Maybe ExprIdentResolution)
unqualifiedExprIdent exprName scopeNode { interface } = do
  let
    fromScopeNode ∷ Maybe ExprIdentResolution
    fromScopeNode = scopeNodeExprIdent exprName scopeNode

    fromInterface ∷ Maybe ExprIdentResolution
    fromInterface = interfaceExprIdent exprName Nothing interface

  pure $ fromScopeNode <|> fromInterface

qualifiedExprIdent
  ∷ ∀ r. Input r → ModuleName → Ident → ST r (Maybe ExprIdentResolution)
qualifiedExprIdent input importPrefix exprName = do
  input.lookupModule importPrefix >>= case _ of
    Just fileId → do
      { interface } ← input.lookupInterface fileId
      pure $ interfaceExprIdent exprName (Just fileId) interface
    Nothing →
      pure Nothing

type Input r =
  { lookupModule ∷ ModuleName → ST r (Maybe FileId)
  , lookupSurface ∷ FileId → ST r Module
  , lookupInterface ∷ FileId → ST r InterfaceCollect.Result
  , lookupScopeNode ∷ FileId → ST r ScopeCollect.Result
  }

resolveModule ∷ ∀ r. Input r → FileId → ST r Result
resolveModule input fileId = do
  state ← State.empty
  fileSurface ← input.lookupSurface fileId
  fileScopeNode ← input.lookupScopeNode fileId
  fileInterface ← input.lookupInterface fileId

  let
    traversal ∷ { | OnPureScript (Rewrite (ST r)) }
    traversal = topDownTraversal $ defaultVisitorM
      { onExpr = case _ of
          e@(ExprIdent (Annotation { id }) (QualifiedName { moduleName, name })) → do
            let
              scopeNode ∷ ScopeNode
              scopeNode = getExprScopeNode id fileScopeNode

            maybeKind ← case moduleName of
              Nothing →
                unqualifiedExprIdent name scopeNode fileInterface
              Just importPrefix →
                qualifiedExprIdent input importPrefix name

            for_ maybeKind \kind →
              State.insertResolution _.exprIdent state id kind

            pure e
          e →
            pure e
      }
  traverseModule traversal fileSurface *> State.freeze state