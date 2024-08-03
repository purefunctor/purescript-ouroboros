module PureScript.Id where

import Prelude

import PureScript.Utils.Immutable.IntMap (IntMap)

newtype Id ∷ Type → Type
newtype Id t = Id Int

derive newtype instance Eq (Id t)
derive newtype instance Ord (Id t)

newtype IdMap ∷ Type → Type → Type
newtype IdMap t v = IdMap (IntMap v)

derive newtype instance Eq v ⇒ Eq (IdMap t v)
derive newtype instance Ord v ⇒ Ord (IdMap t v)
