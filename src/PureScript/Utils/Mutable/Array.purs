module PureScript.Utils.Mutable.Array where

import Prelude

import Control.Monad.ST (Region, ST)
import Data.Array.ST (STArray)
import Data.Array.ST as STArray
import Data.Array.ST.Partial as STArrayPartial
import Data.Maybe (Maybe)
import Partial.Unsafe (unsafePartial)
import Prim.Coerce (class Coercible)
import Safe.Coerce (coerce)

newtype MutableArray ∷ Region → Type → Type
newtype MutableArray r v = MutableArray (STArray r v)

empty ∷ ∀ r v. ST r (MutableArray r v)
empty = MutableArray <$> STArray.new

peek ∷ ∀ r i v. Coercible i Int ⇒ i → MutableArray r v → ST r (Maybe v)
peek index (MutableArray inner) = STArray.peek (coerce index) inner

poke ∷ ∀ r i v. Coercible i Int ⇒ i → v → MutableArray r v → ST r Unit
poke index value (MutableArray inner) =
  unsafePartial $ void $ STArrayPartial.poke (coerce index) value inner

push ∷ ∀ r v. v → MutableArray r v → ST r Int
push value (MutableArray inner) = (_ - 1) <$> STArray.push value inner

pop ∷ ∀ r v. MutableArray r v → ST r (Maybe v)
pop (MutableArray inner) = STArray.pop inner

last ∷ ∀ r v. MutableArray r v → ST r (Maybe v)
last (MutableArray inner) = do
  length ← STArray.length inner
  STArray.peek (length - 1) inner

unsafeFreeze ∷ ∀ r v. MutableArray r v → ST r (Array v)
unsafeFreeze (MutableArray inner) = STArray.unsafeFreeze inner
