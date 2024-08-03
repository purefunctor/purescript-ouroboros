module PureScript.Utils.Immutable.IntMap where

import Prelude

import Data.Array as Array
import Data.Function.Uncurried (Fn2, Fn3, Fn4, Fn8, mkFn2, runFn2, runFn3, runFn4, runFn8)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))

foreign import data IntMap ∷ Type → Type

type role IntMap representational

foreign import eqIntMapImpl
  ∷ ∀ a
  . Fn3
      (Fn2 a a Boolean) -- eq
      (IntMap a) -- xs
      (IntMap a) -- ys
      Boolean

foreign import ordIntMapImpl
  ∷ ∀ a
  . Fn8
      (Fn2 Int Int Ordering) -- compareKey
      (Fn2 a a Ordering) -- compareValue
      Ordering -- LT
      Ordering -- EQ
      Ordering -- GT
      (Fn2 Ordering Ordering Ordering) -- append
      (IntMap a) -- xs
      (IntMap a) -- ys
      Ordering

instance Eq v ⇒ Eq (IntMap v) where
  eq = runFn3 eqIntMapImpl (mkFn2 eq)

instance Ord v ⇒ Ord (IntMap v) where
  compare = runFn8 ordIntMapImpl (mkFn2 compare) (mkFn2 compare) LT EQ GT (mkFn2 append)

foreign import fromArrayImpl
  ∷ ∀ a. Fn2 (Tuple Int a → { key ∷ Int, value ∷ a }) (Array (Tuple Int a)) (IntMap a)

foreign import toArrayImpl
  ∷ ∀ a. Fn2 (Fn2 Int a (Tuple Int a)) (IntMap a) (Array (Tuple Int a))

fromArray ∷ ∀ a. Ord a ⇒ Array (Tuple Int a) → IntMap a
fromArray = do
  let
    fromTuple ∷ Tuple Int a → { key ∷ Int, value ∷ a }
    fromTuple (Tuple key value) = { key, value }
  runFn2 fromArrayImpl fromTuple <<< Array.sort

toArray ∷ ∀ a. IntMap a → Array (Tuple Int a)
toArray = runFn2 toArrayImpl (mkFn2 Tuple)

foreign import getImpl ∷ ∀ a m. Fn4 (a → m a) (m a) Int (IntMap a) (m a)

get ∷ ∀ a. Int → IntMap a → Maybe a
get = runFn4 getImpl Just Nothing
