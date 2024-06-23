module Test.PureScript.Surface where

import Prelude

import Data.Tuple.Nested ((/\))
import Node.Path (FilePath)
import Node.Path as Path
import Test.Snapshot (SnapshotSpec, findInputs, makeSnapshotsNamed)
import Test.Spec (describe)

glob ∷ FilePath
glob = Path.concat [ "test", "snapshots", "surface", "*.input" ]

spec ∷ SnapshotSpec Unit
spec = do
  inputPaths <- findInputs glob
  describe "PureScript.Surface" do
    makeSnapshotsNamed inputPaths $
      [ "lowerModule" /\ \inputFile ->
          pure inputFile
      ]
