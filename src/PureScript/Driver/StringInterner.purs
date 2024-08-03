module PureScript.Driver.StringInterner where

import Prelude

import Control.Monad.ST (Region, ST)
import Data.Maybe (Maybe(..))
import Partial.Unsafe (unsafeCrashWith)
import PureScript.Id (Id(..))
import PureScript.Utils.Mutable.Array (MutableArray)
import PureScript.Utils.Mutable.Array as MutableArray
import PureScript.Utils.Mutable.Object (MutableObject)
import PureScript.Utils.Mutable.Object as MutableObject
import Safe.Coerce (class Coercible, coerce)

newtype Interner ∷ Region → Type → Type
newtype Interner r t = Interner
  { array ∷ MutableArray r t
  , index ∷ MutableObject r t (Id t)
  }

empty ∷ ∀ r t. ST r (Interner r t)
empty = do
  array ← MutableArray.empty
  index ← MutableObject.empty
  pure $ Interner { array, index }

intern ∷ ∀ r t. Coercible t String ⇒ Interner r t → t → ST r (Id t)
intern (Interner { array, index }) t = do
  mId ← MutableObject.peek t index
  case mId of
    Just id →
      pure id
    Nothing → do
      id ← coerce $ MutableArray.push t array
      MutableObject.poke t id index
      pure id

get ∷ ∀ r t. Interner r t → Id t → ST r t
get (Interner { array }) i = do
  MutableArray.peek i array >>= case _ of
    Just t →
      pure t
    Nothing →
      unsafeCrashWith "invariant violated: invalid id"

lookup ∷ ∀ r t. Coercible t String ⇒ Interner r t → t → ST r (Maybe (Id t))
lookup (Interner { index }) t = MutableObject.peek t index

delete ∷ ∀ r t. Coercible t String ⇒ Interner r t → Id t → ST r Unit
delete interner@(Interner { index }) i = do
  t ← get interner i
  MutableObject.delete t index

rename ∷ ∀ r t. Coercible t String ⇒ Interner r t → Id t → t → ST r Unit
rename interner@(Interner { array, index }) i t' = do
  t ← get interner i
  MutableObject.delete t index
  MutableArray.poke i t' array
