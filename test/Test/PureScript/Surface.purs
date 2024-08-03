module Test.PureScript.Surface where

import Prelude

import Control.Monad.ST.Global (toEffect)
import Data.Tuple.Nested ((/\))
import Effect.Class (liftEffect)
import Node.Path (FilePath)
import Node.Path as Path
import PureScript.Debug (inspect)
import PureScript.Interface.Collect (collectInterface)
import PureScript.Surface.Lower (lowerModule)
import Test.Snapshot (SnapshotSpec, findInputs, makeSnapshotsNamed)
import Test.Spec (describe)
import Test.Utils (parseTotal)

surfaceGlob ∷ FilePath
surfaceGlob = Path.concat [ "test", "snapshots", "surface", "*.input" ]

interfaceGlob ∷ FilePath
interfaceGlob = Path.concat [ "test", "snapshots", "interface", "*.input" ]

spec ∷ SnapshotSpec Unit
spec = do
  surfaceInputs ← findInputs surfaceGlob
  interfaceInputs ← findInputs interfaceGlob
  describe "PureScript.Surface" do
    makeSnapshotsNamed surfaceInputs $
      [ "lowerModule" /\ \inputFile → do
          liftEffect $ toEffect do
            lower ← lowerModule $ parseTotal inputFile
            pure $ inspect lower
      ]
    makeSnapshotsNamed interfaceInputs $
      [ "collectInterface" /\ \inputFile → do
          liftEffect $ toEffect do
            { surface } ← lowerModule $ parseTotal inputFile
            interface ← collectInterface surface
            pure $ inspect interface
      ]
