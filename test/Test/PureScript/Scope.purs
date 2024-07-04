module Test.PureScript.Scope where

import Prelude

import Control.Monad.ST.Global (toEffect)
import Data.Tuple.Nested ((/\))
import Effect.Class (liftEffect)
import Node.Path (FilePath)
import Node.Path as Path
import PureScript.Debug (inspect)
import PureScript.Scope.Collect (collectModule)
import PureScript.Surface.Lower (lowerModule)
import Test.Snapshot (SnapshotSpec, findInputs, makeSnapshotsNamed)
import Test.Spec (describe)
import Test.Utils (parseTotal)

scopeGlob ∷ FilePath
scopeGlob = Path.concat [ "test", "snapshots", "scope", "*.input" ]

spec ∷ SnapshotSpec Unit
spec = do
  scopeInputs ← findInputs scopeGlob
  describe "PureScript.Scope" do
    makeSnapshotsNamed scopeInputs $ do
      [ "collectModule" /\ \inputFile → do
          liftEffect $ toEffect do
            let cst = parseTotal inputFile
            { surface } ← lowerModule cst
            scope ← collectModule surface
            pure $ inspect scope
      ]
