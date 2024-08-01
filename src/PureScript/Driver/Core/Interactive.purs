module PureScript.Driver.Core.Interactive where

import Prelude

import Control.Monad.ST (ST)
import Control.Monad.ST.Ref (STRef)
import Control.Monad.ST.Ref as STRef
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Traversable (for_)
import Partial.Unsafe (unsafeCrashWith)
import PureScript.CST.Types (ModuleName)
import PureScript.Diagnostic.Types (Diagnostic(..), DiagnosticKind(..))
import PureScript.Driver.Files (ParsedFile, parseFile, parsedImports, parsedModuleName)
import PureScript.Driver.Query.Engine (Engine(..))
import PureScript.Driver.Query.Engine as Engine
import PureScript.Driver.Query.Stable (ModuleNameId)
import PureScript.Driver.Query.Stable as Stable
import PureScript.Utils.Mutable.GraphMap (GraphMap)
import PureScript.Utils.Mutable.GraphMap as GraphMap

newtype Interactive r = Interactive
  { engine ∷ Engine r
  , graph ∷ GraphMap r ModuleNameId
  , diagnostics ∷ STRef r (Set Diagnostic)
  }

updateGraph ∷ ∀ r. Interactive r → ModuleNameId → ParsedFile → ST r Unit
updateGraph (Interactive { engine: Engine { stable }, graph }) moduleNameId parsedFile = do
  GraphMap.addNode graph moduleNameId
  let
    imports ∷ Set ModuleName
    imports = parsedImports parsedFile
  for_ imports \importedModuleName → do
    importedModuleNameId ← Stable.internModule stable importedModuleName
    GraphMap.addNode graph importedModuleNameId
    GraphMap.addEdge graph moduleNameId importedModuleNameId

updateDiagnostics ∷ ∀ r. Interactive r → Diagnostic → ST r Unit
updateDiagnostics (Interactive { diagnostics }) diagnostic =
  void $ STRef.modify (Set.insert diagnostic) diagnostics

createFile ∷ ∀ r. Interactive r → String → String → ST r Unit
createFile interactive@(Interactive { engine: engine@(Engine { stable }) }) filePath fileSource = do
  case parseFile fileSource of
    Left { error } →
      updateDiagnostics interactive $
        Diagnostic { kind: DiagnosticParseError error }
    Right parsedFile → do
      let
        moduleName ∷ ModuleName
        moduleName = parsedModuleName parsedFile
      { moduleNameId, fileId } ← Stable.stabilize stable filePath moduleName
      Engine.inputSet @"parsedFile" engine fileId parsedFile
      updateGraph interactive moduleNameId parsedFile

editFile ∷ ∀ r. Interactive r → String → String → ST r Unit
editFile interactive@(Interactive { engine: engine@(Engine { stable }) }) filePath fileSource = do
  Stable.lookupFileId stable filePath >>= case _ of
    Just fileId → do
      oldParsedFile ← Engine.inputGet @"parsedFile" engine fileId
      let
        oldModuleName ∷ ModuleName
        oldModuleName = parsedModuleName oldParsedFile
      moduleNameId ← Stable.lookupModuleNameId stable oldModuleName >>= case _ of
        Just moduleNameId →
          pure moduleNameId
        Nothing →
          unsafeCrashWith "invariant violated: oldModuleName should have been stabilized."
      case parseFile fileSource of
        Left { error } →
          updateDiagnostics interactive $
            Diagnostic { kind: DiagnosticParseError error }
        Right parsedFile → do
          let
            moduleName ∷ ModuleName
            moduleName = parsedModuleName parsedFile
          Engine.inputSet @"parsedFile" engine fileId parsedFile
          Stable.editModule stable moduleNameId moduleName
          updateGraph interactive moduleNameId parsedFile
    Nothing →
      createFile interactive filePath fileSource

renameFile ∷ ∀ r. Interactive r → String → String → ST r Unit
renameFile (Interactive { engine: Engine { stable } }) oldFilePath newFilePath = do
  Stable.lookupFileId stable oldFilePath >>= case _ of
    Just oldFileId →
      Stable.editFilePath stable oldFileId newFilePath
    Nothing →
      unsafeCrashWith "invariant violated: oldFilePath should have been stabilized."
