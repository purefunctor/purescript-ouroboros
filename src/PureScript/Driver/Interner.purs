module PureScript.Driver.Interner where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Exception (throw)
import PureScript.CST.Types (ModuleName(..))
import PureScript.Utils.Mutable.Array (MutableArray)
import PureScript.Utils.Mutable.Array as MutableArray
import PureScript.Utils.Mutable.Object (MutableObject)
import PureScript.Utils.Mutable.Object as MutableObject
import Safe.Coerce (coerce)

newtype ModuleNameIndex = ModuleNameIndex Int

newtype ModuleNameInterner = ModuleNameInterner
  { array ∷ MutableArray ModuleName
  , index ∷ MutableObject ModuleName ModuleNameIndex
  }

emptyInterner ∷ Effect ModuleNameInterner
emptyInterner = do
  array ← MutableArray.empty
  index ← MutableObject.empty
  pure $ ModuleNameInterner { array, index }

internModuleName ∷ ModuleNameInterner → ModuleName → Effect ModuleNameIndex
internModuleName (ModuleNameInterner { array, index }) moduleName = do
  mModuleNameIndex ← MutableObject.peek moduleName index
  case mModuleNameIndex of
    Just moduleNameIndex →
      pure moduleNameIndex
    Nothing → do
      moduleNameIndex ← coerce $ MutableArray.push moduleName array
      MutableObject.poke moduleName moduleNameIndex index
      pure moduleNameIndex

getModuleName ∷ ModuleNameInterner → ModuleNameIndex → Effect ModuleName
getModuleName (ModuleNameInterner { array }) moduleNameIndex = do
  MutableArray.peek moduleNameIndex array >>= case _ of
    Just moduleName →
      pure moduleName
    Nothing →
      throw $ "invariant violated: invalid moduleNameIndex"

removeModuleName ∷ ModuleNameInterner → ModuleNameIndex → Effect Unit
removeModuleName interner@(ModuleNameInterner { index }) moduleNameIndex = do
  moduleName ← getModuleName interner moduleNameIndex
  MutableObject.delete moduleName index

changeModuleName ∷ ModuleNameInterner → ModuleNameIndex → ModuleName → Effect Unit
changeModuleName interner@(ModuleNameInterner { array, index }) moduleNameIndex newModuleName = do
  oldModuleName ← getModuleName interner moduleNameIndex
  MutableObject.delete oldModuleName index
  MutableArray.poke moduleNameIndex newModuleName array
  MutableObject.poke newModuleName moduleNameIndex index
