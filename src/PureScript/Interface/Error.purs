module PureScript.Interface.Error where

import Prelude

import Data.Maybe (Maybe(..))
import PureScript.CST.Types (Ident, Proper)
import PureScript.Interface.Types (ConstructorKind, TypeKind, ValueKind)
import PureScript.Surface.Syntax.Tree (ModuleImportId)

data InterfaceError
  = MissingConstructor Proper
  | MissingType Proper
  | MissingValue Ident
  | DuplicateConstructor (DuplicateOf ConstructorKind)
  | DuplicateType (DuplicateOf TypeKind)
  | DuplicateValue (DuplicateOf ValueKind)

type DuplicateOf a =
  { old ∷ { importId ∷ Maybe ModuleImportId, kind ∷ a }
  , new ∷ { importId ∷ Maybe ModuleImportId, kind ∷ a }
  }

localDuplicateOf ∷ ∀ a. a → a → DuplicateOf a
localDuplicateOf old new =
  { old: { importId: Nothing, kind: old }
  , new: { importId: Nothing, kind: new }
  }

localDuplicateConstructor ∷ ConstructorKind → ConstructorKind → InterfaceError
localDuplicateConstructor old new = DuplicateConstructor $ localDuplicateOf old new

localDuplicateType ∷ TypeKind → TypeKind → InterfaceError
localDuplicateType old new = DuplicateType $ localDuplicateOf old new

localDuplicateValue ∷ ValueKind → ValueKind → InterfaceError
localDuplicateValue old new = DuplicateValue $ localDuplicateOf old new

derive instance Eq InterfaceError
derive instance Ord InterfaceError
