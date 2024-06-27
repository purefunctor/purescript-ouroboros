module Test.PureScript.Driver where

import Prelude

import Effect.Class (liftEffect)
import PureScript.CST.Types (ModuleName(..))
import PureScript.Driver.Core
  ( createModule
  , defaultState
  , deleteModule
  , editModule
  , getModuleContents
  , getModuleFromPath
  , renameModule
  )
import PureScript.Driver.GraphMap (hasNode)
import PureScript.Driver.Interner (getModuleName)
import Safe.Coerce (coerce)
import Test.Snapshot (SnapshotSpec)
import Test.Spec (describe, it)
import Test.Spec.Assertions (expectError, shouldEqual)

basicModule ∷ String
basicModule = "module Main where\n"

testModule ∷ String
testModule = "module Test where\n"

spec ∷ SnapshotSpec Unit
spec = do
  describe "PureScript.Driver.Core" do
    it "creates files" do
      void $ liftEffect do
        state ← defaultState
        createModule state "Main.purs" basicModule
        moduleIndex ← getModuleFromPath state "Main.purs"
        contents ← getModuleContents state moduleIndex
        contents.filePath `shouldEqual` "Main.purs"
        contents.fileSource `shouldEqual` basicModule
        hasBasicNode ← hasNode state.moduleGraph moduleIndex
        hasBasicNode `shouldEqual` true
    it "edits files" do
      void $ liftEffect do
        state ← defaultState
        createModule state "Main.purs" basicModule
        editModule state "Main.purs" testModule
        moduleIndex ← getModuleFromPath state "Main.purs"
        contents ← getModuleContents state moduleIndex
        contents.filePath `shouldEqual` "Main.purs"
        contents.fileSource `shouldEqual` testModule
        moduleName ← getModuleName state.moduleNameInterner moduleIndex
        coerce moduleName `shouldEqual` "Test"
    it "renames files" do
      void $ liftEffect do
        state ← defaultState
        createModule state "Main.purs" basicModule
        renameModule state "Main.purs" "Test.purs"
        moduleIndex ← getModuleFromPath state "Test.purs"
        contents ← getModuleContents state moduleIndex
        contents.filePath `shouldEqual` "Test.purs"
        contents.fileSource `shouldEqual` basicModule
    it "removes files" do
      void $ liftEffect do
        state ← defaultState
        createModule state "Main.purs" basicModule
        deleteModule state "Main.purs"
        expectError $ getModuleFromPath state "Main.purs"
