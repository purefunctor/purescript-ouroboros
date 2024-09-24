module Test.PureScript.Interface where

import Prelude

import Control.Monad.ST.Global (toEffect)
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested ((/\))
import Effect.Class (liftEffect)
import Node.Path (FilePath)
import Node.Path as Path
import Partial.Unsafe (unsafeCrashWith)
import PureScript.CST.Types (ModuleName(..))
import PureScript.Debug (inspect)
import PureScript.Driver.Query.Stable (FileId)
import PureScript.Id (Id(..))
import PureScript.Interface.Collect as InterfaceCollect
import Test.Common (lowerTotal)
import Test.Snapshot (SnapshotSpec, findInputs, makeSnapshotsNamed)
import Test.Spec (describe)

libFileId ∷ FileId
libFileId = Id 0

libSource ∷ String
libSource =
  """module Lib where

data Maybe a = Just a | Nothing

life = 42"""

hidFileId ∷ FileId
hidFileId = Id 1

hidSource ∷ String
hidSource =
  """module Hid (notLife) where

data Either a b = Left a | Right b

notLife = 42"""

dupSource ∷ String
dupSource =
  """module Dup where

data Maybe a = Just a | Nothing
"""

dupFileId ∷ FileId
dupFileId = Id 2

input ∷ ∀ r. InterfaceCollect.Input r
input =
  { lookupModule: case _ of
      ModuleName "Lib" →
        pure $ Just libFileId
      ModuleName "Hid" →
        pure $ Just hidFileId
      ModuleName "Dup" →
        pure $ Just dupFileId
      _ →
        pure Nothing
  , lookupInterface: \id → do
      { surface } ← lowerTotal case id of
        _ | id == libFileId → libSource
        _ | id == hidFileId → hidSource
        _ | id == dupFileId → dupSource
        _ → unsafeCrashWith "Invalid ID!"
      InterfaceCollect.collectInterface input surface
  }

interfaceGlob ∷ FilePath
interfaceGlob = Path.concat [ "test", "snapshots", "interface", "*.input" ]

spec ∷ SnapshotSpec Unit
spec = do
  interfaceInputs ← findInputs interfaceGlob
  describe "PureScript.Interface" do
    makeSnapshotsNamed interfaceInputs $
      [ "collectInterface" /\ \inputFile → do
          liftEffect $ toEffect do
            { surface } ← lowerTotal inputFile
            interface ← InterfaceCollect.collectInterface input surface
            pure $ inspect interface
      ]
