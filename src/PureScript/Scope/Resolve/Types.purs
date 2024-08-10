module PureScript.Scope.Resolve.Types where

import PureScript.Id.Map (IdMap)
import PureScript.Scope.Types (ExprIdentResolution)
import PureScript.Surface.Syntax.Tree (Expr)

type Resolutions =
  { exprIdent ∷ IdMap Expr ExprIdentResolution
  }