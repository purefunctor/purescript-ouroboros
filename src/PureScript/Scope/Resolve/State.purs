module PureScript.Scope.Resolve.State where

import Prelude

import Control.Monad.ST (ST)
import PureScript.Id (Id(..), IdMap(..))
import PureScript.Scope.Resolve.Types (Resolutions)
import PureScript.Scope.Types (ExprIdentResolution)
import PureScript.Utils.Mutable.STIntMap (STIntMap)
import PureScript.Utils.Mutable.STIntMap as STIntMap
import Safe.Coerce (coerce)

type State r =
  { exprIdent ∷ STIntMap r ExprIdentResolution
  }

empty ∷ ∀ r. ST r (State r)
empty = do
  exprIdent ← STIntMap.empty
  pure { exprIdent }

insertResolution ∷ ∀ r t v. (State r → STIntMap r v) → State r → Id t → v → ST r Unit
insertResolution get state (Id i) v = STIntMap.set i v (get state)

freeze ∷ ∀ r. State r → ST r Resolutions
freeze state = do
  exprIdent ← STIntMap.freeze state.exprIdent
  pure $ coerce { exprIdent }