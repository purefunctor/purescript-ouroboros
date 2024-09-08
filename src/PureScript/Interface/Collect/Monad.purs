-- @inline export ask always
-- @inline export addError always
module PureScript.Interface.Collect.Monad where

import Prelude

import Control.Monad.ST (Region, ST)
import Control.Monad.ST.Class (liftST)
import Data.Maybe (Maybe(..))
import PureScript.CST.Types (Ident(..), Proper(..))
import PureScript.Interface.Error (InterfaceError(..))
import PureScript.Interface.Types (ConstructorKind, Export(..), ExportKind, TypeKind, ValueKind)
import PureScript.Monad.Reader (Reader)
import PureScript.Monad.Reader as Reader
import PureScript.Utils.Mutable.Array (MutableArray)
import PureScript.Utils.Mutable.Array as MutableArray
import PureScript.Utils.Mutable.Object (MutableObject)
import PureScript.Utils.Mutable.Object as MutableObject
import Safe.Coerce (class Coercible)

type Environment r =
  { constructors ∷ MutableObject r Proper (Export ConstructorKind)
  , types ∷ MutableObject r Proper (Export TypeKind)
  , values ∷ MutableObject r Ident (Export ValueKind)
  , errors ∷ MutableArray r InterfaceError
  }

type InterfaceM ∷ Region → Type → Type
type InterfaceM r = Reader r (Environment r)

type InsertOrErrorFn r k v = k → v → ExportKind → InterfaceM r Unit

insertOrError
  ∷ ∀ k v r
  . Coercible k String
  ⇒ (Environment r → MutableObject r k (Export v))
  → (v → v → InterfaceError)
  → InsertOrErrorFn r k v
insertOrError f e k v x = do
  state@{ errors } ← Reader.ask
  let
    m ∷ MutableObject r k (Export v)
    m = f state
  liftST $ MutableObject.peek k m >>= case _ of
    Nothing →
      MutableObject.poke k (Export { kind: x, id: v }) m
    Just (Export { id: v' }) →
      void $ MutableArray.push (e v v') errors

insertOrErrorConstructor ∷ ∀ r. InsertOrErrorFn r Proper ConstructorKind
insertOrErrorConstructor = insertOrError _.constructors DuplicateConstructor

insertOrErrorType ∷ ∀ r. InsertOrErrorFn r Proper TypeKind
insertOrErrorType = insertOrError _.types DuplicateType

insertOrErrorValue ∷ ∀ r. InsertOrErrorFn r Ident ValueKind
insertOrErrorValue = insertOrError _.values DuplicateValue

run ∷ ∀ r a. InterfaceM r a → ST r a
run action = do
  environment ←
    { constructors: _
    , types: _
    , values: _
    , errors: _
    } <$> MutableObject.empty
      <*> MutableObject.empty
      <*> MutableObject.empty
      <*> MutableArray.empty
  Reader.runReader action environment

ask ∷ ∀ r. InterfaceM r (Environment r)
ask = Reader.ask

addError ∷ ∀ r. InterfaceError → InterfaceM r Unit
addError error = do
  { errors } ← Reader.ask
  void $ liftST $ MutableArray.push error errors
