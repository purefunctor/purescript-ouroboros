module Test.PureScript.Driver where

import Prelude

import Control.Monad.ST (ST)
import Control.Monad.ST.Global (Global, toEffect)
import Data.Maybe (fromJust)
import Effect.Class (liftEffect)
import Partial.Unsafe (unsafePartial)
import PureScript.CST.Types (ModuleName(..))
import PureScript.Driver.Core
  ( Driver(..)
  , createModule
  , deleteModule
  , editModule
  , emptyDriver
  , getModuleContents
  , getModuleFromPath
  , renameModule
  )
import PureScript.Driver.Interner (ModuleNameIndex)
import PureScript.Driver.Interner as ModuleNameInterner
import PureScript.Driver.Query (QueryEngine(..))
import PureScript.Utils.Mutable.GraphMap (SCC(..))
import PureScript.Utils.Mutable.GraphMap as GraphMap
import PureScript.Utils.Mutable.JsMap as JsMap
import Safe.Coerce (coerce)
import Test.Snapshot (SnapshotSpec)
import Test.Spec (describe, it)
import Test.Spec.Assertions (expectError, shouldEqual)

basicModule ∷ String
basicModule = "module Main where\n"

testModule ∷ String
testModule = "module Test where\n"

hasNode ∷ Driver → ModuleNameIndex → ST Global Boolean
hasNode (Driver { moduleGraph }) = GraphMap.hasNode moduleGraph

getModuleName ∷ Driver → ModuleNameIndex → ST Global ModuleName
getModuleName (Driver { queryEngine: QueryEngine { moduleNameInterner } }) =
  ModuleNameInterner.getModuleName moduleNameInterner

getModuleIndex ∷ Driver → ModuleName → ST Global ModuleNameIndex
getModuleIndex (Driver { queryEngine: QueryEngine { moduleNameInterner } }) =
  ModuleNameInterner.internModuleName moduleNameInterner

getScc ∷ Driver → ModuleNameIndex → ST Global (Array (SCC ModuleNameIndex))
getScc (Driver { moduleScc }) moduleNameIndex =
  unsafePartial $ fromJust <$> JsMap.get moduleNameIndex moduleScc

spec ∷ SnapshotSpec Unit
spec = do
  describe "PureScript.Driver.Core" do
    it "creates files" do
      void $ liftEffect do
        state ← emptyDriver
        createModule state "Main.purs" basicModule
        moduleIndex ← getModuleFromPath state "Main.purs"
        contents ← getModuleContents state moduleIndex
        contents.filePath `shouldEqual` "Main.purs"
        contents.fileSource `shouldEqual` basicModule
        hasBasicNode ← toEffect $ hasNode state moduleIndex
        hasBasicNode `shouldEqual` true
    it "edits files" do
      void $ liftEffect do
        state ← emptyDriver
        createModule state "Main.purs" basicModule
        editModule state "Main.purs" testModule
        moduleIndex ← getModuleFromPath state "Main.purs"
        contents ← getModuleContents state moduleIndex
        contents.filePath `shouldEqual` "Main.purs"
        contents.fileSource `shouldEqual` testModule
        moduleName ← toEffect $ getModuleName state moduleIndex
        coerce moduleName `shouldEqual` "Test"
    it "renames files" do
      void $ liftEffect do
        state ← emptyDriver
        createModule state "Main.purs" basicModule
        renameModule state "Main.purs" "Test.purs"
        moduleIndex ← getModuleFromPath state "Test.purs"
        contents ← getModuleContents state moduleIndex
        contents.filePath `shouldEqual` "Test.purs"
        contents.fileSource `shouldEqual` basicModule
    it "removes files" do
      void $ liftEffect do
        state ← emptyDriver
        createModule state "Main.purs" basicModule
        deleteModule state "Main.purs"
        expectError $ getModuleFromPath state "Main.purs"
    it "tracks cycles" do
      void $ liftEffect do
        driver ← emptyDriver

        createModule driver "A.purs" "module A where\n"
        aIdx ← getModuleFromPath driver "A.purs"
        aScc ← toEffect $ getScc driver aIdx
        aScc `shouldEqual` [ AcyclicSCC aIdx ]

        createModule driver "B.purs" "module B where\nimport A"
        bIdx ← getModuleFromPath driver "B.purs"
        aScc' ← toEffect $ getScc driver aIdx
        aScc' `shouldEqual` [ AcyclicSCC aIdx, AcyclicSCC bIdx ]
        bScc ← toEffect $ getScc driver bIdx
        bScc `shouldEqual` [ AcyclicSCC aIdx, AcyclicSCC bIdx ]

        createModule driver "C.purs" "module C where\nimport D"
        cIdx ← getModuleFromPath driver "C.purs"
        dIdx ← toEffect $ getModuleIndex driver (ModuleName "D")
        cScc ← toEffect $ getScc driver cIdx
        cScc `shouldEqual` [ AcyclicSCC dIdx, AcyclicSCC cIdx ]

        createModule driver "D.purs" "module D where\nimport C"
        cScc' ← toEffect $ getScc driver cIdx
        cScc' `shouldEqual` [ CyclicSCC [ cIdx, dIdx ] ]
        dScc ← toEffect $ getScc driver dIdx
        dScc `shouldEqual` [ CyclicSCC [ cIdx, dIdx ] ]
