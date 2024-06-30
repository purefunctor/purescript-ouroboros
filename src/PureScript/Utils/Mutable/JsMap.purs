module PureScript.Utils.Mutable.JsMap where

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

foreign import data JsMap ∷ Region → Type → Type → Type

foreign import empty ∷ ∀ r k v. ST r (JsMap r k v)

foreign import setImpl ∷ ∀ r k v. STFn3 k v (JsMap r k v) r Unit

foreign import getImpl ∷ ∀ r k v m. STFn4 (v → m) m k (JsMap r k v) r m

foreign import hasImpl ∷ ∀ r k v. STFn2 k (JsMap r k v) r Boolean

foreign import deleteImpl ∷ ∀ r k v. STFn2 k (JsMap r k v) r Unit

foreign import clearImpl ∷ ∀ r k v. STFn1 (JsMap r k v) r Unit

foreign import forEachImpl ∷ ∀ r k v. STFn2 (JsMap r k v) (k → v → ST r Unit) r Unit

set ∷ ∀ r k v. k → v → JsMap r k v → ST r Unit
set = runSTFn3 setImpl

get ∷ ∀ r k v. k → JsMap r k v → ST r (Maybe v)
get = runSTFn4 getImpl Just Nothing

has ∷ ∀ r k v. k → JsMap r k v → ST r Boolean
has = runSTFn2 hasImpl

delete ∷ ∀ r k v. k → JsMap r k v → ST r Unit
delete = runSTFn2 deleteImpl

clear ∷ ∀ r k v. JsMap r k v → ST r Unit
clear = runSTFn1 clearImpl

forEach ∷ ∀ r k v. JsMap r k v → (k → v → ST r Unit) → ST r Unit
forEach = runSTFn2 forEachImpl
