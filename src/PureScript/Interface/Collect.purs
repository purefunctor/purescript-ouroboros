module PureScript.Interface.Collect where

import Prelude

import Control.Monad.ST (ST)
import Control.Monad.ST.Class (liftST)
import Data.Array as Array
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Foldable (for_, traverse_)
import Data.FoldableWithIndex (forWithIndex_)
import Data.Maybe (Maybe(..), isNothing, maybe)
import Data.Traversable (traverse)
import Foreign.Object (Object)
import Foreign.Object as Object
import PureScript.CST.Types (Ident(..), ModuleName, Proper(..))
import PureScript.Driver.Query.Stable (FileId)
import PureScript.Interface.Collect.Monad as Monad
import PureScript.Interface.Error (InterfaceError(..))
import PureScript.Interface.Types (ConstructorKind(..), ExportKind(..), Interface(..), TypeKind(..), ValueKind(..))
import PureScript.Surface.Syntax.Tree as SST
import PureScript.Utils.Mutable.Array as MutableArray
import PureScript.Utils.Mutable.Object as MutableObject
import Safe.Coerce (coerce)

newtype ExportMap = ExportMap
  { types ∷ Object (Maybe SST.DataMembers)
  , values ∷ Object Unit
  }

inferExportMap ∷ ∀ r. NonEmptyArray SST.Export → ST r ExportMap
inferExportMap exports = do
  typesRaw ← MutableObject.empty
  valuesRaw ← MutableObject.empty

  for_ exports case _ of
    SST.ExportValue name →
      MutableObject.poke name unit valuesRaw
    SST.ExportType name memberList → do
      MutableObject.poke name memberList typesRaw
    SST.ExportClass name → do
      MutableObject.poke name Nothing typesRaw
    _ → do
      pure unit

  map ExportMap $ { types: _, values: _ }
    <$> MutableObject.unsafeFreeze typesRaw
    <*> MutableObject.unsafeFreeze valuesRaw

constructorExportKind ∷ Proper → Proper → Maybe ExportMap → ExportKind
constructorExportKind (Proper dataName) constructorName = maybe ExportKindOpen case _ of
  ExportMap { types } → case Object.lookup dataName types of
    Nothing →
      ExportKindHidden
    -- T
    Just Nothing →
      ExportKindHidden
    -- T(..)
    Just (Just SST.DataAll) →
      ExportKindExported
    -- T(U, V)
    Just (Just (SST.DataEnumerated dataMembers)) →
      maybe ExportKindHidden (const ExportKindExported)
        $ Array.find (eq constructorName) dataMembers

typeExportKind ∷ Proper → Maybe ExportMap → ExportKind
typeExportKind (Proper typeName) = maybe ExportKindOpen case _ of
  ExportMap { types } →
    if Object.member typeName types then
      ExportKindExported
    else
      ExportKindHidden

valueExportKind ∷ Ident → Maybe ExportMap → ExportKind
valueExportKind (Ident valueName) = maybe ExportKindOpen case _ of
  ExportMap { values } →
    if Object.member valueName values then
      ExportKindExported
    else
      ExportKindHidden

type Input r =
  { lookupModule ∷ ModuleName → ST r (Maybe FileId)
  , lookupInterface ∷ FileId → ST r Result
  }

type Result =
  { interface ∷ Interface
  , errors ∷ Array InterfaceError
  }

collectInterface ∷ ∀ r. Input r → SST.Module → ST r Result
collectInterface _ (SST.Module { exports, declarations }) = Monad.run do
  exportMap ← liftST $ traverse inferExportMap exports

  for_ declarations case _ of
    -- data Maybe a = Just a | Nothing
    SST.DeclarationData (SST.Annotation { id }) tName _ (SST.DataEquation { constructors }) → do
      let
        tKind ∷ TypeKind
        tKind = TypeKindData id

        tExportKind ∷ ExportKind
        tExportKind = typeExportKind tName exportMap
      Monad.insertOrErrorType tName tKind tExportKind

      for_ constructors $ traverse_ case _ of
        SST.DataConstructor { annotation: SST.Annotation { id: cId }, name: cName } → do
          let
            cKind ∷ ConstructorKind
            cKind = ConstructorKindData cName cId

            cExportKind ∷ ExportKind
            cExportKind = constructorExportKind tName cName exportMap
          Monad.insertOrErrorConstructor cName cKind cExportKind

    -- type Function a b = a -> b
    SST.DeclarationType (SST.Annotation { id }) tName _ _ → do
      let
        tKind ∷ TypeKind
        tKind = TypeKindSynoynm id

        tExportKind ∷ ExportKind
        tExportKind = typeExportKind tName exportMap
      Monad.insertOrErrorType tName tKind tExportKind

    -- newtype Identity a = Identity a
    SST.DeclarationNewtype (SST.Annotation { id }) tName _ (SST.NewtypeEquation { constructor }) → do
      let
        tKind ∷ TypeKind
        tKind = TypeKindNewtype id

        tExportKind ∷ ExportKind
        tExportKind = typeExportKind tName exportMap
      Monad.insertOrErrorType tName tKind tExportKind

      case constructor of
        SST.NewtypeConstructor { annotation: SST.Annotation { id: cId }, name: cName } → do
          let
            cKind ∷ ConstructorKind
            cKind = ConstructorKindNewtype cName cId

            cExportKind ∷ ExportKind
            cExportKind = constructorExportKind tName cName exportMap
          Monad.insertOrErrorConstructor cName cKind cExportKind

    -- class Functor f where map :: forall a b. (a -> b) -> f a -> f b
    SST.DeclarationClass (SST.Annotation { id }) tName _ (SST.ClassEquation { methods }) → do
      let
        tKind ∷ TypeKind
        tKind = TypeKindClass id

        tExportKind ∷ ExportKind
        tExportKind = typeExportKind tName exportMap
      Monad.insertOrErrorType tName tKind tExportKind

      for_ methods $ traverse_ case _ of
        SST.ClassMethod { annotation: SST.Annotation { id: mId }, name: mName } → do
          let
            vKind ∷ ValueKind
            vKind = ValueKindMethod tName mId

            vExportKind ∷ ExportKind
            vExportKind = valueExportKind mName exportMap
          Monad.insertOrErrorValue mName vKind vExportKind

    -- life = 42
    SST.DeclarationValue (SST.Annotation { id }) vName _ _ → do
      let
        vKind ∷ ValueKind
        vKind = ValueKindValue id

        vExportKind ∷ ExportKind
        vExportKind = valueExportKind vName exportMap
      Monad.insertOrErrorValue vName vKind vExportKind

    _ →
      pure unit

  for_ exportMap case _ of
    ExportMap { types: exMapTypes, values: exMapValues } → do
      forWithIndex_ exMapTypes \name members → do
        { constructors, types } ← Monad.ask
        typeExport ← liftST $ MutableObject.peek (coerce name) types
        when (isNothing typeExport) do
          Monad.addError (MissingType (coerce name))
        for_ members case _ of
          SST.DataAll →
            pure unit
          SST.DataEnumerated dataMembers →
            for_ dataMembers \dataMember → do
              constructorExport ← liftST $ MutableObject.peek (coerce dataMember) constructors
              when (isNothing constructorExport) do
                Monad.addError (MissingConstructor (coerce dataMember))
      forWithIndex_ exMapValues \name _ → do
        { values } ← Monad.ask
        valueExport ← liftST $ MutableObject.peek (coerce name) values
        when (isNothing valueExport) do
          Monad.addError (MissingValue (coerce name))

  { constructors, types, values, errors } ← Monad.ask

  interface ← liftST $ { constructors: _, types: _, values: _ }
    <$> MutableObject.unsafeFreeze constructors
    <*> MutableObject.unsafeFreeze types
    <*> MutableObject.unsafeFreeze values

  liftST $ { interface: Interface interface, errors: _ }
    <$> MutableArray.unsafeFreeze errors
