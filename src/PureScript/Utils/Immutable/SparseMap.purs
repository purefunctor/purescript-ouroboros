module PureScript.Utils.Immutable.SparseMap where

import Prelude

import Control.Monad.ST (ST)
import PureScript.Utils.Mutable.Array (MutableArray)
import PureScript.Utils.Mutable.Array as MutableArray

newtype SparseMap ∷ Type → Type → Type
newtype SparseMap k v = SparseMap (Array v)

derive newtype instance Eq v ⇒ Eq (SparseMap k v)

ofMutable ∷ ∀ k v r. MutableArray r v → ST r (SparseMap k v)
ofMutable = map SparseMap <<< MutableArray.unsafeFreeze
