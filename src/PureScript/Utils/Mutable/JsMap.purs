module PureScript.Utils.Mutable.JsMap where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Uncurried
  ( EffectFn1
  , EffectFn2
  , EffectFn3
  , EffectFn4
  , runEffectFn1
  , runEffectFn2
  , runEffectFn3
  , runEffectFn4
  )

foreign import data JsMap ∷ Type → Type → Type

foreign import empty ∷ ∀ k v. Effect (JsMap k v)

foreign import setImpl ∷ ∀ k v. EffectFn3 k v (JsMap k v) Unit

foreign import getImpl ∷ ∀ k v r. EffectFn4 (v → r) r k (JsMap k v) r

foreign import hasImpl ∷ ∀ k v. EffectFn2 k (JsMap k v) Boolean

foreign import deleteImpl ∷ ∀ k v. EffectFn2 k (JsMap k v) Unit

foreign import clearImpl ∷ ∀ k v. EffectFn1 (JsMap k v) Unit

foreign import forEachImpl ∷ ∀ k v. EffectFn2 (JsMap k v) (k → v → Effect Unit) Unit

set ∷ ∀ k v. k → v → JsMap k v → Effect Unit
set = runEffectFn3 setImpl

get ∷ ∀ k v. k → JsMap k v → Effect (Maybe v)
get = runEffectFn4 getImpl Just Nothing

has ∷ ∀ k v. k → JsMap k v → Effect Boolean
has = runEffectFn2 hasImpl

delete ∷ ∀ k v. k → JsMap k v → Effect Unit
delete = runEffectFn2 deleteImpl

clear ∷ ∀ k v. JsMap k v → Effect Unit
clear = runEffectFn1 clearImpl

forEach ∷ ∀ k v. JsMap k v → (k → v → Effect Unit) → Effect Unit
forEach = runEffectFn2 forEachImpl
