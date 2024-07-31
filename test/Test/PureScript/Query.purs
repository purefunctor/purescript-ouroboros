module Test.PureScript.Query where

import Prelude

import Control.Monad.ST.Global (toEffect)
import Data.Either (Either(..))
import Effect.Class (liftEffect)
import Partial.Unsafe (unsafeCrashWith)
import PureScript.Driver.Files (ParsedFile, parseFile)
import PureScript.Driver.Query.Engine (Engine(..))
import PureScript.Driver.Query.Engine as Engine
import PureScript.Driver.Query.Stats as Stats
import PureScript.Driver.StringInterner (Id(..))
import Test.Snapshot (SnapshotSpec)
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldEqual)

parseTotal ∷ String → ParsedFile
parseTotal = parseFile >>> case _ of
  Left _ →
    unsafeCrashWith "Oops! Fixture is invalid!"
  Right parsedFile →
    parsedFile

spec ∷ SnapshotSpec Unit
spec = do
  describe "PureScript.Driver.Query" do

    describe "Non-Semantic Edits" do
      let
        baseModule = parseTotal "module Main where\nmain = pure unit"
        editedModule = parseTotal "module Main where\n\nmain = pure unit"
        otherModule = parseTotal "module Library where\nlife = 42"

      it "should miss on full lowering" do
        stat ← liftEffect $ toEffect do
          engine@(Engine { stats }) ← Engine.empty

          Engine.inputSet @"parsedFile" engine (Id 0) baseModule
          _ ← Engine.queryGet @"surfaceFull" engine (Id 0)

          Engine.inputSet @"parsedFile" engine (Id 0) editedModule
          _ ← Engine.queryGet @"surfaceFull" engine (Id 0)

          Stats.getStat @"surfaceFull" stats

        stat `shouldEqual` { hit: 0, miss: 2 }

      it "should miss on partial lowering" do
        stat ← liftEffect $ toEffect do
          engine@(Engine { stats }) ← Engine.empty

          Engine.inputSet @"parsedFile" engine (Id 0) baseModule
          _ ← Engine.queryGet @"surface" engine (Id 0)

          Engine.inputSet @"parsedFile" engine (Id 0) editedModule
          _ ← Engine.queryGet @"surface" engine (Id 0)

          Stats.getStat @"surface" stats

        stat `shouldEqual` { hit: 0, miss: 2 }

      it "should hit on scope graphs v1" do
        stat <- liftEffect $ toEffect do
          engine@(Engine { stats }) ← Engine.empty

          Engine.inputSet @"parsedFile" engine (Id 0) baseModule
          _ ← Engine.queryGet @"scopeGraph" engine (Id 0)

          Engine.inputSet @"parsedFile" engine (Id 0) editedModule
          _ ← Engine.queryGet @"scopeGraph" engine (Id 0)

          Stats.getStat @"scopeGraph" stats
        
        stat `shouldEqual` { hit: 1, miss: 1 }

      it "should hit on scope graphs v2" do
        stat <- liftEffect $ toEffect do
          engine@(Engine { stats }) <- Engine.empty

          Engine.inputSet @"parsedFile" engine (Id 0) baseModule
          _ ← Engine.queryGet @"scopeGraph" engine (Id 0)

          Engine.inputSet @"parsedFile" engine (Id 1) otherModule
          _ ← Engine.queryGet @"scopeGraph" engine (Id 0)
        
          Stats.getStat @"scopeGraph" stats
        
        stat `shouldEqual` { hit: 1, miss: 1 }

    describe "Semantic Edits" do
      let
        baseModule = parseTotal "module Main where\nmain = pure unit"
        editedModule = parseTotal "module Main where\nmain = pure unit\nlife = 42"

      it "should miss on scope graphs" do
        stat <- liftEffect $ toEffect do
          engine@(Engine { stats }) <- Engine.empty

          Engine.inputSet @"parsedFile" engine (Id 0) baseModule
          _ <- Engine.queryGet @"scopeGraph" engine (Id 0)

          Engine.inputSet @"parsedFile" engine (Id 0) editedModule
          _ <- Engine.queryGet @"scopeGraph" engine (Id 0)

          Stats.getStat @"scopeGraph" stats
        
        stat `shouldEqual` { hit: 0, miss: 2 }
