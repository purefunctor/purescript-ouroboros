module PureScript.Surface.Interface where

import Prelude

import Control.Monad.ST (ST)
import Control.Monad.ST as ST
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Foreign.Object (Object)
import Foreign.Object as Object
import PureScript.CST.Types (Ident(..))
import PureScript.Surface.Types as SST
import PureScript.Utils.Mutable.Array as MutableArray
import PureScript.Utils.Mutable.Object as MutableObject
import Safe.Coerce (class Coercible, coerce)

newtype Interface = Interface
  { values ∷ Object SST.DeclarationIndex
  }

derive instance Eq Interface

data InterfaceError = MissingValue Ident

derive instance Eq InterfaceError

type InterfaceWithErrors =
  { interface ∷ Interface
  , errors ∷ Array InterfaceError
  }

checkExports ∷ Interface → Maybe (NonEmptyArray SST.Export) → Array InterfaceError
checkExports (Interface { values }) = case _ of
  Nothing →
    []
  Just exportList → ST.run do
    errorsRaw ← MutableArray.empty

    let
      check ∷ ∀ k v. Coercible k String ⇒ k → Object v → InterfaceError → ST _ Unit
      check i k e =
        unless (Object.member (coerce i) k) do
          void $ MutableArray.push e errorsRaw

    for_ exportList case _ of
      SST.ExportValue i →
        check i values (MissingValue i)
      _ →
        pure unit

    MutableArray.unsafeFreeze errorsRaw

collectInterface ∷ SST.Module → InterfaceWithErrors
collectInterface (SST.Module { exports, declarations }) = ST.run do
  valuesRaw ← MutableObject.empty

  for_ declarations case _ of
    SST.DeclarationValue (SST.Annotation { index }) i _ _ →
      MutableObject.poke i index valuesRaw
    _ →
      pure unit

  interface ← coerce do
    { values: _ } <$> MutableObject.unsafeFreeze valuesRaw

  let
    errors ∷ Array InterfaceError
    errors = checkExports interface exports

  pure { interface, errors }
