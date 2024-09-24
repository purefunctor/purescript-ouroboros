module Test.PureScript.Surface where

import Prelude

import Control.Monad.ST.Global (toEffect)
import Data.Tuple.Nested ((/\))
import Effect.Class (liftEffect)
import Node.Path (FilePath)
import Node.Path as Path
import PureScript.Debug (inspect)
import Test.Common (lowerTotal)
import Test.Snapshot (SnapshotSpec, findInputs, makeSnapshotsNamed)
import Test.Spec (describe)

surfaceGlob ∷ FilePath
surfaceGlob = Path.concat [ "test", "snapshots", "surface", "*.input" ]

spec ∷ SnapshotSpec Unit
spec = do
  surfaceInputs ← findInputs surfaceGlob
  describe "PureScript.Surface" do
    makeSnapshotsNamed surfaceInputs $
      [ "lowerModule" /\ \inputFile → do
          liftEffect $ toEffect do
            lower ← lowerTotal inputFile
            pure $ inspect lower
      ]
