module PureScript.Id where

import Prelude

import Data.Hashable (class Hashable)

newtype Id ∷ Type → Type
newtype Id t = Id Int

derive newtype instance Eq (Id t)
derive newtype instance Ord (Id t)
derive newtype instance Hashable (Id t)