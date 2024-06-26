module PureScript.Utils.Mutable.Object where

import Prelude

import Control.Monad.ST.Global (Global, toEffect)
import Data.Maybe (Maybe)
import Effect (Effect)
import Foreign.Object (Object)
import Foreign.Object.ST (STObject)
import Foreign.Object.ST as STObject
import Foreign.Object.ST.Unsafe as STObjectUnsafe
import Prim.Coerce (class Coercible)
import Safe.Coerce (coerce)

newtype MutableObject ∷ Type → Type → Type
newtype MutableObject k v = MutableObject (STObject Global v)

empty ∷ ∀ k v. Effect (MutableObject k v)
empty = toEffect $ MutableObject <$> STObject.new

peek ∷ ∀ k v. Coercible k String ⇒ k → MutableObject k v → Effect (Maybe v)
peek key (MutableObject inner) = toEffect $ STObject.peek (coerce key) inner

poke ∷ ∀ k v. Coercible k String ⇒ k → v → MutableObject k v → Effect Unit
poke key value (MutableObject inner) = toEffect $ void $ STObject.poke (coerce key) value inner

delete ∷ ∀ k v. Coercible k String ⇒ k → MutableObject k v → Effect Unit
delete key (MutableObject inner) = toEffect $ void $ STObject.delete (coerce key) inner

unsafeFreeze ∷ ∀ k v. Coercible k String ⇒ MutableObject k v → Effect (Object v)
unsafeFreeze (MutableObject inner) = toEffect $ STObjectUnsafe.unsafeFreeze inner
