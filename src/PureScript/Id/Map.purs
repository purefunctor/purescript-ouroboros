module PureScript.Id.Map where

import Prelude

import Data.Maybe (Maybe)
import PureScript.Id (Id(..))
import PureScript.Utils.Immutable.IntMap (IntMap)
import PureScript.Utils.Immutable.IntMap as IntMap

newtype IdMap ∷ Type → Type → Type
newtype IdMap t v = IdMap (IntMap v)

derive newtype instance Eq v ⇒ Eq (IdMap t v)
derive newtype instance Ord v ⇒ Ord (IdMap t v)

get ∷ ∀ t v. Id t → IdMap t v → Maybe v
get (Id i) (IdMap m) = IntMap.get i m
