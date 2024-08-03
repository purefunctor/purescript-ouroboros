module Test.PureScript.Scope where

import Prelude

import Control.Monad.ST.Global (toEffect)
import Data.Tuple.Nested ((/\))
import Effect.Class (liftEffect)
import Node.Path (FilePath)
import Node.Path as Path
import PureScript.Debug (inspect)
import PureScript.Interface.Collect (collectInterface)
import PureScript.Scope.Collect (collectModule)
import Test.PureScript.Surface (lowerTotal)
import Test.Snapshot (SnapshotSpec, findInputs, makeSnapshotsNamed)
import Test.Spec (describe)

scopeGlob ∷ FilePath
scopeGlob = Path.concat [ "test", "snapshots", "scope", "*.input" ]

spec ∷ SnapshotSpec Unit
spec = do
  scopeInputs ← findInputs scopeGlob
  describe "PureScript.Scope" do
    makeSnapshotsNamed scopeInputs $ do
      [ "collectModule" /\ \inputFile → do
          liftEffect $ toEffect do
            { surface } ← lowerTotal inputFile
            { interface } ← collectInterface surface
            scope ← collectModule surface interface
            pure $ inspect scope
      ]
