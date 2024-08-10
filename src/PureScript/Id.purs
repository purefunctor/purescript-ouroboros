module PureScript.Id where

import Prelude

import Data.Maybe (Maybe)
import PureScript.Utils.Immutable.IntMap (IntMap)
import PureScript.Utils.Immutable.IntMap as IntMap

newtype Id ∷ Type → Type
newtype Id t = Id Int

derive newtype instance Eq (Id t)
derive newtype instance Ord (Id t)

newtype IdMap ∷ Type → Type → Type
newtype IdMap t v = IdMap (IntMap v)

derive newtype instance Eq v ⇒ Eq (IdMap t v)
derive newtype instance Ord v ⇒ Ord (IdMap t v)

get ∷ ∀ t v. Id t → IdMap t v → Maybe v
get (Id i) (IdMap m) = IntMap.get i m