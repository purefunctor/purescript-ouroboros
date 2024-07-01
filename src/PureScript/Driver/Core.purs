module PureScript.Driver.Core where

import Prelude

import Control.Monad.ST.Global (Global, toEffect)
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Effect (Effect)
import Effect.Exception (throw)
import PureScript.CST.Parser.Monad (PositionedError)
import PureScript.CST.Types (ModuleName(..))
import PureScript.Driver.Files (ParsedFile, parseFile, parsedImports, parsedModuleName)
import PureScript.Driver.Interner
  ( ModuleNameIndex
  , ModuleNameInterner
  , changeModuleName
  , emptyInterner
  , internModuleName
  , removeModuleName
  )
import PureScript.Utils.Mutable.GraphMap (GraphMap, addEdge, addNode, clearEdges, emptyGraphMap)
import PureScript.Utils.Mutable.JsMap (JsMap)
import PureScript.Utils.Mutable.JsMap as JsMap
import PureScript.Utils.Mutable.Object (MutableObject)
import PureScript.Utils.Mutable.Object as MutableObject
import Safe.Coerce (coerce)

type Contents =
  { filePath ∷ String
  , fileSource ∷ String
  , fileParsed ∷ ParsedFile
  }

type State =
  { moduleNameInterner ∷ ModuleNameInterner Global
  , moduleGraph ∷ GraphMap Global ModuleNameIndex
  , moduleContents ∷ JsMap Global ModuleNameIndex Contents
  , pathToModule ∷ MutableObject Global String ModuleNameIndex
  }

defaultState ∷ Effect State
defaultState = do
  moduleNameInterner ← toEffect emptyInterner
  moduleGraph ← toEffect emptyGraphMap
  moduleContents ← toEffect JsMap.empty
  pathToModule ← toEffect MutableObject.empty
  pure { moduleNameInterner, moduleGraph, moduleContents, pathToModule }

createModuleNode ∷ State → ModuleName → Effect ModuleNameIndex
createModuleNode { moduleNameInterner, moduleGraph } moduleName = toEffect do
  moduleNameIndex ← internModuleName moduleNameInterner moduleName
  addNode moduleGraph moduleNameIndex
  pure moduleNameIndex

updateImportEdges ∷ State → ModuleNameIndex → Set ModuleName → Effect Unit
updateImportEdges state@{ moduleGraph } moduleNameIndex moduleImports = do
  toEffect $ clearEdges moduleGraph moduleNameIndex
  for_ moduleImports \moduleImport → do
    importedIndex ← createModuleNode state moduleImport
    toEffect $ addEdge moduleGraph moduleNameIndex importedIndex

getModuleFromPath ∷ State → String → Effect ModuleNameIndex
getModuleFromPath { pathToModule } filePath = do
  toEffect (MutableObject.peek filePath pathToModule) >>= case _ of
    Just moduleNameIndex →
      pure moduleNameIndex
    Nothing →
      throw $ "invariant violated: filePath does not exist"

getModuleContents ∷ State → ModuleNameIndex → Effect Contents
getModuleContents { moduleContents } moduleNameIndex = do
  toEffect (JsMap.get moduleNameIndex moduleContents) >>= case _ of
    Just oldContents →
      pure oldContents
    Nothing →
      throw $ "invariant violated: moduleNameIndex does not exist"

createModule ∷ State → String → String → Effect Unit
createModule state@{ moduleContents, pathToModule } filePath fileSource = do
  let
    parseResult ∷ Either PositionedError ParsedFile
    parseResult = parseFile fileSource
  case parseResult of
    Left _ →
      pure unit
    Right parsedFile → do
      let
        moduleName ∷ ModuleName
        moduleName = parsedModuleName parsedFile

        moduleImports ∷ Set ModuleName
        moduleImports = parsedImports parsedFile

        contents ∷ Contents
        contents = { filePath, fileSource, fileParsed: parsedFile }

      moduleNameIndex ← createModuleNode state moduleName
      toEffect $ MutableObject.poke filePath moduleNameIndex pathToModule

      toEffect $ JsMap.set moduleNameIndex contents moduleContents
      updateImportEdges state moduleNameIndex moduleImports

editModule ∷ State → String → String → Effect Unit
editModule state@{ moduleNameInterner, moduleContents } filePath fileSource = do
  let
    parseResult ∷ Either PositionedError ParsedFile
    parseResult = parseFile fileSource
  case parseResult of
    Left _ →
      pure unit
    Right newParsed → do
      moduleNameIndex ← getModuleFromPath state filePath
      { fileParsed: oldParsed } ← getModuleContents state moduleNameIndex

      let
        oldModuleName ∷ ModuleName
        oldModuleName = parsedModuleName oldParsed

        newModuleName ∷ ModuleName
        newModuleName = parsedModuleName newParsed

        newModuleImports ∷ Set ModuleName
        newModuleImports = parsedImports newParsed

        contents ∷ Contents
        contents = { filePath, fileSource, fileParsed: newParsed }

      unless (oldModuleName == newModuleName) do
        toEffect $ changeModuleName moduleNameInterner moduleNameIndex newModuleName

      toEffect $ JsMap.set moduleNameIndex contents moduleContents
      updateImportEdges state moduleNameIndex newModuleImports

deleteModule ∷ State → String → Effect Unit
deleteModule state@{ moduleNameInterner, moduleContents, pathToModule } filePath = do
  moduleNameIndex ← getModuleFromPath state filePath

  toEffect do
    changeModuleName moduleNameInterner moduleNameIndex (coerce "?")
    removeModuleName moduleNameInterner moduleNameIndex

    JsMap.delete moduleNameIndex moduleContents
    MutableObject.delete filePath pathToModule

renameModule ∷ State → String → String → Effect Unit
renameModule state@{ moduleContents, pathToModule } oldFilePath newFilePath = do
  moduleNameIndex ← getModuleFromPath state oldFilePath

  toEffect do
    MutableObject.delete oldFilePath pathToModule
    MutableObject.poke newFilePath moduleNameIndex pathToModule

  contents ← getModuleContents state moduleNameIndex
  toEffect $ JsMap.set moduleNameIndex (contents { filePath = newFilePath }) moduleContents
