module PureScript.Scope.Resolve.State where

import Prelude

import Control.Monad.ST (ST)
import Control.Monad.ST.Ref (STRef)
import Control.Monad.ST.Ref as STRef
import Data.HashMap (HashMap)
import Data.HashMap as HashMap
import PureScript.Id (Id)
import PureScript.Scope.Resolve.Types (Resolutions)
import PureScript.Scope.Types (ExprIdentResolution)
import PureScript.Surface.Syntax.Tree as SST
import Safe.Coerce (coerce)

type State r =
  { exprIdent ∷ STRef r (HashMap (Id SST.Expr) ExprIdentResolution)
  }

empty ∷ ∀ r. ST r (State r)
empty = do
  exprIdent ← STRef.new HashMap.empty
  pure { exprIdent }

insertResolution ∷ ∀ r t v. (State r → STRef r (HashMap (Id t) v)) → State r → Id t → v → ST r Unit
insertResolution get state id resolution = void $ STRef.modify (HashMap.insert id resolution)
  (get state)

freeze ∷ ∀ r. State r → ST r Resolutions
freeze state = do
  exprIdent ← STRef.read state.exprIdent
  pure $ coerce { exprIdent }