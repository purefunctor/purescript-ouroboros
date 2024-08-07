module PureScript.Scope.Resolve where

import Prelude

import Control.Monad.ST (ST)
import PureScript.Id (IdMap)
import PureScript.Scope.Types (ScopeNode)
import PureScript.Surface.Syntax.Traversal
  ( OnPureScript
  , Rewrite
  , defaultVisitorM
  , topDownTraversal
  , traverseModule
  )
import PureScript.Surface.Syntax.Tree (Expr(..), Module)

resolveModule ∷ ∀ r. IdMap Expr ScopeNode → Module → ST r Unit
resolveModule _ m = do
  let
    traversal ∷ { | OnPureScript (Rewrite (ST r)) }
    traversal = topDownTraversal $ defaultVisitorM
      { onExpr = case _ of
          e@(ExprIdent _ _) →
            pure e
          e →
            pure e
      }
  void $ traverseModule traversal m
