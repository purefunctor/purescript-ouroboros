module PureScript.Utils.Mutable.STIntMap where

import Prelude

import Control.Monad.ST (Region, ST)
import Control.Monad.ST.Uncurried
  ( STFn1
  , STFn2
  , STFn3
  , STFn4
  , runSTFn1
  , runSTFn2
  , runSTFn3
  , runSTFn4
  )
import Data.Maybe (Maybe(..))
import PureScript.Utils.Immutable.IntMap (IntMap)

foreign import data STIntMap ∷ Region → Type → Type

type role STIntMap nominal representational

foreign import empty ∷ ∀ r v. ST r (STIntMap r v)

foreign import setImpl ∷ ∀ r v. STFn3 Int v (STIntMap r v) r Unit

foreign import getImpl ∷ ∀ r v m. STFn4 (v → m) m Int (STIntMap r v) r m

foreign import hasImpl ∷ ∀ r v. STFn2 Int (STIntMap r v) r Boolean

foreign import deleteImpl ∷ ∀ r v. STFn2 Int (STIntMap r v) r Unit

foreign import clearImpl ∷ ∀ r v. STFn1 (STIntMap r v) r Unit

foreign import freezeImpl ∷ ∀ r v. STFn1 (STIntMap r v) r (IntMap v)

set ∷ ∀ r v. Int → v → STIntMap r v → ST r Unit
set = runSTFn3 setImpl

get ∷ ∀ r v. Int → STIntMap r v → ST r (Maybe v)
get = runSTFn4 getImpl Just Nothing

has ∷ ∀ r v. Int → STIntMap r v → ST r Boolean
has = runSTFn2 hasImpl

delete ∷ ∀ r v. Int → STIntMap r v → ST r Unit
delete = runSTFn2 deleteImpl

clear ∷ ∀ r v. STIntMap r v → ST r Unit
clear = runSTFn1 clearImpl

freeze ∷ ∀ r v. STIntMap r v → ST r (IntMap v)
freeze = runSTFn1 freezeImpl
