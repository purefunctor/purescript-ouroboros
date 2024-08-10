module PureScript.Id.STMap where

import Prelude

import Control.Monad.ST (Region, ST)
import PureScript.Id (Id(..))
import PureScript.Id.Map (IdMap(..))
import PureScript.Utils.Mutable.STIntMap (STIntMap)
import PureScript.Utils.Mutable.STIntMap as STIntMap
import Safe.Coerce (coerce)

newtype STIdMap ∷ Region → Type → Type → Type
newtype STIdMap r t v = STIdMap (STIntMap r v)

empty ∷ ∀ r t v. ST r (STIdMap r t v)
empty = STIdMap <$> STIntMap.empty

set ∷ ∀ r t v. Id t → v → STIdMap r t v → ST r Unit
set (Id i) v (STIdMap m) = STIntMap.set i v m

freeze ∷ ∀ r t v. STIdMap r t v → ST r (IdMap t v)
freeze (STIdMap m) = coerce $ STIntMap.freeze m