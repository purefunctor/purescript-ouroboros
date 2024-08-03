module PureScript.Interface.Types where

import Prelude

import Foreign.Object (Object)
import PureScript.CST.Types (Ident, Proper)
import PureScript.Surface.Syntax.Tree as SST

newtype Interface = Interface
  { dataConstructors ∷ Object SST.ConstructorId
  , newtypeConstructors ∷ Object SST.NewtypeId
  , classMethods ∷ Object SST.ClassMethodId
  , types ∷ Object SST.DeclarationId
  , values ∷ Object SST.DeclarationId
  , constructorsOfData ∷ Object (Array Proper)
  , methodsOfClass ∷ Object (Array Ident)
  }

derive instance Eq Interface

newtype Exported = Exported
  { dataConstructors ∷ Object Unit
  , newtypeConstructors ∷ Object Unit
  , classMethods ∷ Object Unit
  , types ∷ Object Unit
  , values ∷ Object Unit
  }

derive instance Eq Exported
