module PureScript.Scope.Resolve.Types where

import Data.HashMap (HashMap)
import PureScript.Id (Id)
import PureScript.Scope.Types (ExprIdentResolution)
import PureScript.Surface.Syntax.Tree (Expr)

type Resolutions =
  { exprIdent ∷ HashMap (Id Expr) ExprIdentResolution
  }