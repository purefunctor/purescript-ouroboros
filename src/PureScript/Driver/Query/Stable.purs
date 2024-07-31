module PureScript.Driver.Query.Stable where

import Prelude

import Control.Monad.ST (ST)
import PureScript.CST.Types (ModuleName(..))
import PureScript.Driver.StringInterner (Id, Interner)
import PureScript.Driver.StringInterner as Interner
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

editModule ∷ ∀ r. Stable r → ModuleNameId → ModuleName → ST r Unit
editModule (Stable { moduleNames }) moduleNameId moduleName =
  Interner.rename moduleNames moduleNameId moduleName

editFilePath ∷ ∀ r. Stable r → FileId → String → ST r Unit
editFilePath (Stable { filePaths }) fileId filePath =
  Interner.rename filePaths fileId filePath
