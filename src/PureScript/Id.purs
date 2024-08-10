module PureScript.Id where

import Prelude

newtype Id ∷ Type → Type
newtype Id t = Id Int

derive newtype instance Eq (Id t)
derive newtype instance Ord (Id t)