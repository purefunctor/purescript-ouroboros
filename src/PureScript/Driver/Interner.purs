module PureScript.Driver.Interner where

import Prelude

import Control.Monad.ST (ST)
import Data.Maybe (Maybe(..))
import Partial.Unsafe (unsafeCrashWith)
import PureScript.CST.Types (ModuleName(..))
import PureScript.Utils.Mutable.Array (MutableArray)
import PureScript.Utils.Mutable.Array as MutableArray
import PureScript.Utils.Mutable.Object (MutableObject)
import PureScript.Utils.Mutable.Object as MutableObject
import Safe.Coerce (coerce)

newtype ModuleNameIndex = ModuleNameIndex Int

newtype ModuleNameInterner r = ModuleNameInterner
  { array ∷ MutableArray r ModuleName
  , index ∷ MutableObject r ModuleName ModuleNameIndex
  }

emptyInterner ∷ ∀ r. ST r (ModuleNameInterner r)
emptyInterner = do
  array ← MutableArray.empty
  index ← MutableObject.empty
  pure $ ModuleNameInterner { array, index }

internModuleName ∷ ∀ r. ModuleNameInterner r → ModuleName → ST r ModuleNameIndex
internModuleName (ModuleNameInterner { array, index }) moduleName = do
  mModuleNameIndex ← MutableObject.peek moduleName index
  case mModuleNameIndex of
    Just moduleNameIndex →
      pure moduleNameIndex
    Nothing → do
      moduleNameIndex ← coerce $ MutableArray.push moduleName array
      MutableObject.poke moduleName moduleNameIndex index
      pure moduleNameIndex

getModuleName ∷ ∀ r. ModuleNameInterner r → ModuleNameIndex → ST r ModuleName
getModuleName (ModuleNameInterner { array }) moduleNameIndex = do
  MutableArray.peek moduleNameIndex array >>= case _ of
    Just moduleName →
      pure moduleName
    Nothing →
      unsafeCrashWith "invariant violated: invalid moduleNameIndex"

removeModuleName ∷ ∀ r. ModuleNameInterner r → ModuleNameIndex → ST r Unit
removeModuleName interner@(ModuleNameInterner { index }) moduleNameIndex = do
  moduleName ← getModuleName interner moduleNameIndex
  MutableObject.delete moduleName index

changeModuleName ∷ ∀ r. ModuleNameInterner r → ModuleNameIndex → ModuleName → ST r Unit
changeModuleName interner@(ModuleNameInterner { array, index }) moduleNameIndex newModuleName = do
  oldModuleName ← getModuleName interner moduleNameIndex
  MutableObject.delete oldModuleName index
  MutableArray.poke moduleNameIndex newModuleName array
  MutableObject.poke newModuleName moduleNameIndex index
