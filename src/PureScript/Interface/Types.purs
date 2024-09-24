module PureScript.Interface.Types where

import Prelude

import Data.Maybe (Maybe(..))
import Foreign.Object (Object)
import PureScript.CST.Types (Proper)
import PureScript.Surface.Syntax.Tree (ModuleImportId)
import PureScript.Surface.Syntax.Tree as SST

data ImportKind
  = ImportKindOpen
  | ImportKindClosed { hiding ∷ Boolean, explicit ∷ Boolean }

derive instance Eq ImportKind
derive instance Ord ImportKind

data BindingKind
  = BindingKindOpen
  | BindingKindExported
  | BindingKindHidden
  | BindingKindImported
      { importId ∷ ModuleImportId
      , importKind :: ImportKind
      , importExported :: Boolean
      }

derive instance Eq BindingKind
derive instance Ord BindingKind

bindingKindImportId ∷ BindingKind → Maybe ModuleImportId
bindingKindImportId = case _ of
  BindingKindImported { importId } →
    Just importId
  _ →
    Nothing

bindingKindIsExported ∷ BindingKind → Boolean
bindingKindIsExported = case _ of
  BindingKindOpen →
    true
  BindingKindExported →
    true
  _ →
    false

newtype Binding a = Binding { kind ∷ BindingKind, id ∷ a }

derive newtype instance Eq a ⇒ Eq (Binding a)
derive newtype instance Ord a ⇒ Ord (Binding a)

data ConstructorKind
  = ConstructorKindData Proper SST.ConstructorId
  | ConstructorKindNewtype Proper SST.NewtypeId

derive instance Eq ConstructorKind
derive instance Ord ConstructorKind

constructorTypeName ∷ ConstructorKind → Proper
constructorTypeName = case _ of
  ConstructorKindData name _ → name
  ConstructorKindNewtype name _ → name

data TypeKind
  = TypeKindData SST.DeclarationId
  | TypeKindSynoynm SST.DeclarationId
  | TypeKindNewtype SST.DeclarationId
  | TypeKindClass SST.DeclarationId

derive instance Eq TypeKind
derive instance Ord TypeKind

data ValueKind
  = ValueKindValue SST.DeclarationId
  | ValueKindMethod Proper SST.ClassMethodId

derive instance Eq ValueKind
derive instance Ord ValueKind

newtype Interface = Interface
  { constructors ∷ Object (Binding ConstructorKind)
  , types ∷ Object (Binding TypeKind)
  , values ∷ Object (Binding ValueKind)
  }

derive instance Eq Interface
derive instance Ord Interface
