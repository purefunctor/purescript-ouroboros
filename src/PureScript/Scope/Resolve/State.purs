module PureScript.Scope.Resolve.State where

import Prelude

import Control.Monad.ST (ST)
import PureScript.Id (Id)
import PureScript.Id.STMap (STIdMap)
import PureScript.Id.STMap as STIdMap
import PureScript.Scope.Resolve.Types (Resolutions)
import PureScript.Scope.Types (ExprIdentResolution)
import PureScript.Surface.Syntax.Tree as SST
import Safe.Coerce (coerce)

type State r =
  { exprIdent ∷ STIdMap r SST.Expr ExprIdentResolution
  }

empty ∷ ∀ r. ST r (State r)
empty = do
  exprIdent ← STIdMap.empty
  pure { exprIdent }

insertResolution ∷ ∀ r t v. (State r → STIdMap r t v) → State r → Id t → v → ST r Unit
insertResolution get state id resolution = STIdMap.set id resolution (get state)

freeze ∷ ∀ r. State r → ST r Resolutions
freeze state = do
  exprIdent ← STIdMap.freeze state.exprIdent
  pure $ coerce { exprIdent }