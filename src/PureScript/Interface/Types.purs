module PureScript.Interface.Types where

import Prelude

import Foreign.Object (Object)
import PureScript.CST.Types (Proper)
import PureScript.Surface.Syntax.Tree as SST

data BindingKind
  = BindingKindOpen
  | BindingKindExported
  | BindingKindHidden

derive instance Eq BindingKind
derive instance Ord BindingKind

newtype Binding a = Binding { kind ∷ BindingKind, id ∷ a }

derive newtype instance Eq a ⇒ Eq (Binding a)
derive newtype instance Ord a ⇒ Ord (Binding a)

exportToLocal ∷ ∀ a. Binding a → a
exportToLocal (Binding { id }) = id

data ConstructorKind
  = ConstructorKindData Proper SST.ConstructorId
  | ConstructorKindNewtype Proper SST.NewtypeId

derive instance Eq ConstructorKind
derive instance Ord ConstructorKind

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
