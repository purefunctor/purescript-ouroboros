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
  , changeModuleName
  , internModuleName
  , removeModuleName
  )
import PureScript.Driver.Query (QueryEngine(..), emptyQueryEngine)
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

newtype Driver = Driver
  { queryEngine ∷ QueryEngine Global
  , moduleGraph ∷ GraphMap Global ModuleNameIndex
  , moduleContents ∷ JsMap Global ModuleNameIndex Contents
  , pathToModule ∷ MutableObject Global String ModuleNameIndex
  }

emptyDriver ∷ Effect Driver
emptyDriver = do
  queryEngine ← toEffect emptyQueryEngine
  moduleGraph ← toEffect emptyGraphMap
  moduleContents ← toEffect JsMap.empty
  pathToModule ← toEffect MutableObject.empty
  pure $ Driver
    { queryEngine, moduleGraph, moduleContents, pathToModule }

createModuleNode ∷ Driver → ModuleName → Effect ModuleNameIndex
createModuleNode
  (Driver { queryEngine: QueryEngine { moduleNameInterner }, moduleGraph })
  moduleName =
  toEffect do
    moduleNameIndex ← internModuleName moduleNameInterner moduleName
    addNode moduleGraph moduleNameIndex
    pure moduleNameIndex

updateImportEdges ∷ Driver → ModuleNameIndex → Set ModuleName → Effect Unit
updateImportEdges driver@(Driver { moduleGraph }) moduleNameIndex moduleImports = do
  toEffect $ clearEdges moduleGraph moduleNameIndex
  for_ moduleImports \moduleImport → do
    importedIndex ← createModuleNode driver moduleImport
    toEffect $ addEdge moduleGraph moduleNameIndex importedIndex

getModuleFromPath ∷ Driver → String → Effect ModuleNameIndex
getModuleFromPath (Driver { pathToModule }) filePath = do
  toEffect (MutableObject.peek filePath pathToModule) >>= case _ of
    Just moduleNameIndex →
      pure moduleNameIndex
    Nothing →
      throw $ "invariant violated: filePath does not exist"

getModuleContents ∷ Driver → ModuleNameIndex → Effect Contents
getModuleContents (Driver { moduleContents }) moduleNameIndex = do
  toEffect (JsMap.get moduleNameIndex moduleContents) >>= case _ of
    Just oldContents →
      pure oldContents
    Nothing →
      throw $ "invariant violated: moduleNameIndex does not exist"

createModule ∷ Driver → String → String → Effect Unit
createModule driver@(Driver { moduleContents, pathToModule }) filePath fileSource = do
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

      moduleNameIndex ← createModuleNode driver moduleName
      toEffect $ MutableObject.poke filePath moduleNameIndex pathToModule

      toEffect $ JsMap.set moduleNameIndex contents moduleContents
      updateImportEdges driver moduleNameIndex moduleImports

editModule ∷ Driver → String → String → Effect Unit
editModule
  driver@(Driver { queryEngine: QueryEngine { moduleNameInterner }, moduleContents })
  filePath
  fileSource = do
  let
    parseResult ∷ Either PositionedError ParsedFile
    parseResult = parseFile fileSource
  case parseResult of
    Left _ →
      pure unit
    Right newParsed → do
      moduleNameIndex ← getModuleFromPath driver filePath
      { fileParsed: oldParsed } ← getModuleContents driver moduleNameIndex

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
      updateImportEdges driver moduleNameIndex newModuleImports

deleteModule ∷ Driver → String → Effect Unit
deleteModule
  driver@(Driver { queryEngine: QueryEngine { moduleNameInterner }, moduleContents, pathToModule })
  filePath = do
  moduleNameIndex ← getModuleFromPath driver filePath

  toEffect do
    changeModuleName moduleNameInterner moduleNameIndex (coerce "?")
    removeModuleName moduleNameInterner moduleNameIndex

    JsMap.delete moduleNameIndex moduleContents
    MutableObject.delete filePath pathToModule

renameModule ∷ Driver → String → String → Effect Unit
renameModule driver@(Driver { moduleContents, pathToModule }) oldFilePath newFilePath = do
  moduleNameIndex ← getModuleFromPath driver oldFilePath

  toEffect do
    MutableObject.delete oldFilePath pathToModule
    MutableObject.poke newFilePath moduleNameIndex pathToModule

  contents ← getModuleContents driver moduleNameIndex
  toEffect $ JsMap.set moduleNameIndex (contents { filePath = newFilePath }) moduleContents
