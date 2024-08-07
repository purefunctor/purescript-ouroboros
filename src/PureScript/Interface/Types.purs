module PureScript.Interface.Types where

import Prelude

import Data.Maybe (Maybe)
import Foreign.Object (Object)
import Foreign.Object as Object
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

lookupClassMethod ∷ String → Interface → Maybe SST.ClassMethodId
lookupClassMethod name (Interface { classMethods }) = Object.lookup name classMethods

lookupValue ∷ String → Interface → Maybe SST.DeclarationId
lookupValue name (Interface { values }) = Object.lookup name values

newtype Exported = Exported
  { dataConstructors ∷ Object Unit
  , newtypeConstructors ∷ Object Unit
  , classMethods ∷ Object Unit
  , types ∷ Object Unit
  , values ∷ Object Unit
  }

derive instance Eq Exported
