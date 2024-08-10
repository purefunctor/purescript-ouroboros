module PureScript.Driver.Query.Stable where

import Prelude

import Control.Monad.ST (ST)
import Data.Maybe (Maybe(..))
import PureScript.CST.Types (ModuleName(..))
import PureScript.Driver.StringInterner (Interner)
import PureScript.Driver.StringInterner as Interner
import PureScript.Id (Id)
import PureScript.Utils.Mutable.JsMap (JsMap)
import PureScript.Utils.Mutable.JsMap as JsMap

type ModuleNameId = Id ModuleName
type FileId = Id String

newtype Stable r = Stable
  { moduleNames ∷ Interner r ModuleName
  , filePaths ∷ Interner r String
  , pathsOfModule ∷ JsMap r ModuleNameId FileId
  }

empty ∷ ∀ r. ST r (Stable r)
empty = do
  moduleNames ← Interner.empty
  filePaths ← Interner.empty
  pathsOfModule ← JsMap.empty
  pure $ Stable { moduleNames, filePaths, pathsOfModule }

stabilize
  ∷ ∀ r. Stable r → String → ModuleName → ST r { moduleNameId ∷ ModuleNameId, fileId ∷ FileId }
stabilize (Stable { moduleNames, filePaths, pathsOfModule }) filePath moduleName = do
  moduleNameId ← Interner.intern moduleNames moduleName
  fileId ← Interner.intern filePaths filePath
  JsMap.set moduleNameId fileId pathsOfModule
  pure { moduleNameId, fileId }

internModule ∷ ∀ r. Stable r → ModuleName → ST r ModuleNameId
internModule (Stable { moduleNames }) moduleName =
  Interner.intern moduleNames moduleName

editModule ∷ ∀ r. Stable r → ModuleNameId → ModuleName → ST r Unit
editModule (Stable { moduleNames }) moduleNameId moduleName =
  Interner.rename moduleNames moduleNameId moduleName

editFilePath ∷ ∀ r. Stable r → FileId → String → ST r Unit
editFilePath (Stable { filePaths }) fileId filePath =
  Interner.rename filePaths fileId filePath

lookupModuleNameId ∷ ∀ r. Stable r → ModuleName → ST r (Maybe ModuleNameId)
lookupModuleNameId (Stable { moduleNames }) moduleName =
  Interner.lookup moduleNames moduleName

lookupFileId ∷ ∀ r. Stable r → String → ST r (Maybe FileId)
lookupFileId (Stable { filePaths }) filePath =
  Interner.lookup filePaths filePath

lookupFileIdOfModuleName ∷ ∀ r. Stable r → ModuleName → ST r (Maybe FileId)
lookupFileIdOfModuleName (Stable { moduleNames, pathsOfModule }) moduleName = do
  Interner.lookup moduleNames moduleName >>= case _ of
    Just moduleNameId →
      JsMap.get moduleNameId pathsOfModule
    Nothing →
      pure Nothing