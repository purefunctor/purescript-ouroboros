module PureScript.Interface.Types where

import Prelude

import Foreign.Object (Object)
import PureScript.CST.Types (Proper)
import PureScript.Surface.Syntax.Tree as SST

data ExportKind
  = ExportKindOpen
  | ExportKindExported
  | ExportKindHidden

derive instance Eq ExportKind
derive instance Ord ExportKind

newtype Export id = Export { kind ∷ ExportKind, id ∷ id }

derive newtype instance Eq id ⇒ Eq (Export id)
derive newtype instance Ord id ⇒ Ord (Export id)

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
  { constructors ∷ Object (Export ConstructorKind)
  , types ∷ Object (Export TypeKind)
  , values ∷ Object (Export ValueKind)
  }

derive instance Eq Interface
derive instance Ord Interface