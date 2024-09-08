module Test.PureScript.Surface where

import Prelude

import Control.Monad.ST (ST)
import Control.Monad.ST.Global (toEffect)
import Data.Either (Either(..))
import Data.Tuple.Nested ((/\))
import Effect.Class (liftEffect)
import Node.Path (FilePath)
import Node.Path as Path
import Partial.Unsafe (unsafeCrashWith)
import PureScript.Debug (inspect)
import PureScript.Driver.Files (ParsedFile(..), parseFile)
import PureScript.Interface.Collect (collectInterface)
import PureScript.Interface.Collect as InterfaceCollect
import PureScript.Surface.Lower (Result, lowerModule)
import Test.Snapshot (SnapshotSpec, findInputs, makeSnapshotsNamed)
import Test.Spec (describe)

lowerTotal ∷ ∀ r. String → ST r Result
lowerTotal = parseFile >>> case _ of
  Left _ →
    unsafeCrashWith "Oops! Fixture is invalid!"
  Right parsedFile →
    case parsedFile of
      ParsedTotal m →
        lowerModule m
      ParsedPartial m _ →
        lowerModule m

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
            lower ← lowerTotal inputFile
            pure $ inspect lower
      ]
    makeSnapshotsNamed interfaceInputs $
      [ "collectInterface" /\ \inputFile → do
          liftEffect $ toEffect do
            { surface } ← lowerTotal inputFile
            let
              input ∷ ∀ r. InterfaceCollect.Input r
              input =
                { lookupModule: \_ → unsafeCrashWith "unimplemented!"
                , lookupInterface: \_ → unsafeCrashWith "unimplemented!"
                }
            interface ← collectInterface input surface
            pure $ inspect interface
      ]
