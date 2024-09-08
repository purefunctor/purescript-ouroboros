module Test.PureScript.Scope where

import Prelude

import Control.Monad.ST.Global (toEffect)
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested ((/\))
import Effect.Class (liftEffect)
import Node.Path (FilePath)
import Node.Path as Path
import Partial.Unsafe (unsafeCrashWith)
import PureScript.Debug (inspect)
import PureScript.Driver.Query.Stable (FileId)
import PureScript.Id (Id(..))
import PureScript.Interface.Collect (collectInterface)
import PureScript.Interface.Collect as CollectInterface
import PureScript.Scope.Collect (collectModule)
import PureScript.Scope.Resolve (resolveModule)
import PureScript.Scope.Resolve as ScopeResolve
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
            scope ← collectModule surface
            pure $ inspect scope
      , "resolveModule" /\ \inputFile → do
          liftEffect $ toEffect do
            { surface } ← lowerTotal inputFile
            let
              interfaceInput ∷ CollectInterface.Input _
              interfaceInput =
                { lookupModule: \_ → unsafeCrashWith "unimplemented!"
                , lookupInterface: \_ → unsafeCrashWith "unimplemented!"
                }
            interface ← collectInterface interfaceInput surface
            scopeNode ← collectModule surface

            let
              id ∷ FileId
              id = Id 0

              resolveInput ∷ ScopeResolve.Input _
              resolveInput =
                { lookupModule: \_ → pure Nothing
                , lookupSurface: \_ → pure surface
                , lookupInterface: \_ → pure interface
                , lookupScopeNode: \_ → pure scopeNode
                }

            resolution ← resolveModule resolveInput id
            pure $ inspect resolution
      ]
