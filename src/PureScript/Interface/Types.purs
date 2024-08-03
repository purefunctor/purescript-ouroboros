module PureScript.Interface.Types where

import Prelude

import Foreign.Object (Object)
import PureScript.CST.Types (Ident, Proper)
import PureScript.Surface.Types as SST

newtype Interface = Interface
  { dataConstructors ∷ Object SST.ConstructorIndex
  , newtypeConstructors ∷ Object SST.NewtypeIndex
  , classMethods ∷ Object SST.ClassMethodIndex
  , types ∷ Object SST.DeclarationIndex
  , values ∷ Object SST.DeclarationIndex
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
