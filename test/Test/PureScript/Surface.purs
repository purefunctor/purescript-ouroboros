module Test.PureScript.Surface where

import Prelude

import Control.Monad.ST.Global (toEffect)
import Data.Either (Either(..))
import Data.Tuple.Nested ((/\))
import Effect.Class (liftEffect)
import Node.Path (FilePath)
import Node.Path as Path
import Partial.Unsafe (unsafeCrashWith)
import PureScript.CST.Types as CST
import PureScript.Debug (inspect)
import PureScript.Driver.Files (ParsedFile(..), parseFile)
import PureScript.Surface.Interface (collectInterface)
import PureScript.Surface.Lower (lowerModule)
import Test.Snapshot (SnapshotSpec, findInputs, makeSnapshotsNamed)
import Test.Spec (describe)

surfaceGlob ∷ FilePath
surfaceGlob = Path.concat [ "test", "snapshots", "surface", "*.input" ]

interfaceGlob ∷ FilePath
interfaceGlob = Path.concat [ "test", "snapshots", "interface", "*.input" ]

parseTotal ∷ String → CST.Module Void
parseTotal source = case parseFile source of
  Left _ →
    unsafeCrashWith "Invalid!"
  Right parsedFile → case parsedFile of
    ParsedTotal m →
      m
    ParsedPartial _ _ →
      unsafeCrashWith "Invalid!"

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
            pure $ inspect $ collectInterface surface
      ]
