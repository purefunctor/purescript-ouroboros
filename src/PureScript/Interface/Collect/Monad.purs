-- @inline export ask always
-- @inline export addError always
module PureScript.Interface.Collect.Monad where

import Prelude

import Control.Monad.ST (Region, ST)
import Control.Monad.ST.Class (liftST)
import Data.Maybe (Maybe(..))
import PureScript.CST.Types (Ident(..), ModuleName(..), Proper(..))
import PureScript.Interface.Error (DuplicateOf, InterfaceError(..))
import PureScript.Interface.Types (Binding(..), ConstructorKind, TypeKind, ValueKind, bindingKindImportId)
import PureScript.Monad.Reader (Reader)
import PureScript.Monad.Reader as Reader
import PureScript.Utils.Mutable.Array (MutableArray)
import PureScript.Utils.Mutable.Array as MutableArray
import PureScript.Utils.Mutable.Object (MutableObject)
import PureScript.Utils.Mutable.Object as MutableObject
import Safe.Coerce (class Coercible)

type BindingMap r k v = MutableObject r k (Binding v)

type BindingKinds r =
  { constructors ∷ BindingMap r Proper ConstructorKind
  , types ∷ BindingMap r Proper TypeKind
  , values ∷ BindingMap r Ident ValueKind
  }

type Environment r =
  { unqualified ∷ BindingKinds r
  , qualified ∷ MutableObject r ModuleName (BindingKinds r)
  , errors ∷ MutableArray r InterfaceError
  }

type InterfaceM ∷ Region → Type → Type
type InterfaceM r = Reader r (Environment r)

type InsertOrErrorFn r k v = Maybe ModuleName → k → Binding v → InterfaceM r Unit

insertOrError
  ∷ ∀ k v r
  . Coercible k String
  ⇒ (BindingKinds r → MutableObject r k (Binding v))
  → (Binding v → Binding v → InterfaceError)
  → InsertOrErrorFn r k v
insertOrError f e prefix key new = do
  { unqualified, qualified, errors } ← Reader.ask
  m ← case prefix of
    Just prefix' →
      liftST $ MutableObject.peek prefix' qualified >>= case _ of
        Just m →
          pure $ f m
        Nothing → do
          m ← { constructors: _, types: _, values: _ }
            <$> MutableObject.empty
            <*> MutableObject.empty
            <*> MutableObject.empty
          MutableObject.poke prefix' m qualified
          pure $ f m
    Nothing →
      pure $ f unqualified
  liftST $ MutableObject.peek key m >>= case _ of
    Nothing →
      MutableObject.poke key new m
    Just old →
      void $ MutableArray.push (e old new) errors

makeErrorFn ∷ ∀ a. (DuplicateOf a → InterfaceError) → Binding a → Binding a → InterfaceError
makeErrorFn f = case _, _ of
  Binding old, Binding new → f
    { old: { importId: bindingKindImportId old.kind, kind: old.id }
    , new: { importId: bindingKindImportId new.kind, kind: new.id }
    }

insertOrErrorConstructor ∷ ∀ r. InsertOrErrorFn r Proper ConstructorKind
insertOrErrorConstructor = insertOrError _.constructors $ makeErrorFn DuplicateConstructor

insertOrErrorType ∷ ∀ r. InsertOrErrorFn r Proper TypeKind
insertOrErrorType = insertOrError _.types $ makeErrorFn DuplicateType

insertOrErrorValue ∷ ∀ r. InsertOrErrorFn r Ident ValueKind
insertOrErrorValue = insertOrError _.values $ makeErrorFn DuplicateValue

run ∷ ∀ r a. InterfaceM r a → ST r a
run action = do
  unqualified ← { constructors: _, types: _, values: _ }
    <$> MutableObject.empty
    <*> MutableObject.empty
    <*> MutableObject.empty
  qualified ← MutableObject.empty
  environment ← { unqualified, qualified, errors: _ }
    <$> MutableArray.empty
  Reader.runReader action environment

ask ∷ ∀ r. InterfaceM r (Environment r)
ask = Reader.ask

addError ∷ ∀ r. InterfaceError → InterfaceM r Unit
addError error = do
  { errors } ← Reader.ask
  void $ liftST $ MutableArray.push error errors
