module PureScript.Utils.Mutable.Array where

import Prelude

import Control.Monad.ST.Global (Global, toEffect)
import Data.Array.ST (STArray)
import Data.Array.ST as STArray
import Data.Array.ST.Partial as STArrayPartial
import Data.Maybe (Maybe)
import Effect (Effect)
import Partial.Unsafe (unsafePartial)
import Prim.Coerce (class Coercible)
import Safe.Coerce (coerce)

newtype MutableArray ∷ Type → Type
newtype MutableArray v = MutableArray (STArray Global v)

empty ∷ ∀ v. Effect (MutableArray v)
empty = toEffect $ MutableArray <$> STArray.new

peek ∷ ∀ i v. Coercible i Int ⇒ i → MutableArray v → Effect (Maybe v)
peek index (MutableArray inner) = toEffect $ STArray.peek (coerce index) inner

poke ∷ ∀ i v. Coercible i Int ⇒ i → v → MutableArray v → Effect Unit
poke index value (MutableArray inner) =
  unsafePartial $ toEffect $ void $ STArrayPartial.poke (coerce index) value inner

push ∷ ∀ v. v → MutableArray v → Effect Int
push value (MutableArray inner) = (_ - 1) <$> toEffect (STArray.push value inner)
