module PureScript.Utils.Mutable.Object where

import Prelude

import Control.Monad.ST (Region, ST)
import Data.Maybe (Maybe)
import Foreign.Object (Object)
import Foreign.Object.ST (STObject)
import Foreign.Object.ST as STObject
import Foreign.Object.ST.Unsafe as STObjectUnsafe
import Prim.Coerce (class Coercible)
import Safe.Coerce (coerce)

newtype MutableObject ∷ Region → Type → Type → Type
newtype MutableObject r k v = MutableObject (STObject r v)

empty ∷ ∀ r @k v. ST r (MutableObject r k v)
empty = MutableObject <$> STObject.new

peek ∷ ∀ r k v. Coercible k String ⇒ k → MutableObject r k v → ST r (Maybe v)
peek key (MutableObject inner) = STObject.peek (coerce key) inner

poke ∷ ∀ r k v. Coercible k String ⇒ k → v → MutableObject r k v → ST r Unit
poke key value (MutableObject inner) = void $ STObject.poke (coerce key) value inner

delete ∷ ∀ r k v. Coercible k String ⇒ k → MutableObject r k v → ST r Unit
delete key (MutableObject inner) = void $ STObject.delete (coerce key) inner

unsafeFreeze ∷ ∀ r k v. Coercible k String ⇒ MutableObject r k v → ST r (Object v)
unsafeFreeze (MutableObject inner) = STObjectUnsafe.unsafeFreeze inner
