module PureScript.Interface.Collect where

import Prelude

import Control.Monad.ST (ST)
import Data.Array as Array
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Foldable (for_)
import Data.FoldableWithIndex (forWithIndex_)
import Data.Maybe (Maybe(..), maybe)
import Data.Traversable (traverse, traverse_)
import Foreign.Object (Object)
import Foreign.Object as Object
import PureScript.CST.Types (Ident(..), Proper(..))
import PureScript.Interface.Error (InterfaceError(..))
import PureScript.Interface.Types
  ( ConstructorKind(..)
  , Export(..)
  , ExportKind(..)
  , Interface(..)
  , TypeKind(..)
  , ValueKind(..)
  )
import PureScript.Surface.Syntax.Tree as SST
import PureScript.Utils.Mutable.Array as MutableArray
import PureScript.Utils.Mutable.Object (MutableObject)
import PureScript.Utils.Mutable.Object as MutableObject
import Safe.Coerce (class Coercible, coerce)

type Result =
  { interface ∷ Interface
  , errors ∷ Array InterfaceError
  }

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

collectInterface ∷ ∀ r. SST.Module → ST r Result
collectInterface (SST.Module { exports, declarations }) = do
  exportMap ← traverse inferExportMap exports
  constructorsRaw ← MutableObject.empty
  typesRaw ← MutableObject.empty
  valuesRaw ← MutableObject.empty
  errorsRaw ← MutableArray.empty

  let
    insertOrError
      ∷ ∀ k v
      . Coercible k String
      ⇒ k
      → v
      → ExportKind
      → (v → v → InterfaceError)
      → MutableObject r k (Export v)
      → ST r Unit
    insertOrError k v x e m =
      MutableObject.peek k m >>= case _ of
        Nothing → do
          MutableObject.poke k (Export { kind: x, id: v }) m
        Just (Export { id: v' }) → do
          void $ MutableArray.push (e v v') errorsRaw

    collectDataCtor ∷ Proper → SST.DataConstructor → _
    collectDataCtor typeName = case _ of
      SST.DataConstructor { annotation: SST.Annotation { id }, name } → do
        let
          constructorKind ∷ ConstructorKind
          constructorKind = ConstructorKindData typeName id

          exportKind ∷ ExportKind
          exportKind = constructorExportKind typeName name exportMap
        insertOrError name constructorKind exportKind DuplicateConstructor constructorsRaw

    collectNewtypeCtor ∷ Proper → SST.NewtypeConstructor → _
    collectNewtypeCtor typeName = case _ of
      SST.NewtypeConstructor { annotation: SST.Annotation { id }, name } → do
        let
          constructorKind ∷ ConstructorKind
          constructorKind = ConstructorKindNewtype typeName id

          exportKind ∷ ExportKind
          exportKind = constructorExportKind typeName name exportMap
        insertOrError name constructorKind exportKind DuplicateConstructor constructorsRaw

    collectClassMethod ∷ Proper → SST.ClassMethod → _
    collectClassMethod typeName = case _ of
      SST.ClassMethod { annotation: SST.Annotation { id }, name } → do
        let
          valueKind ∷ ValueKind
          valueKind = ValueKindMethod typeName id

          exportKind ∷ ExportKind
          exportKind = valueExportKind name exportMap
        insertOrError name valueKind exportKind DuplicateValue valuesRaw

  for_ declarations case _ of
    SST.DeclarationData (SST.Annotation { id }) name _ (SST.DataEquation { constructors }) → do
      let
        typeKind ∷ TypeKind
        typeKind = TypeKindData id

        exportKind ∷ ExportKind
        exportKind = typeExportKind name exportMap
      insertOrError name typeKind exportKind DuplicateType typesRaw
      traverse_ (traverse_ $ collectDataCtor name) constructors
    SST.DeclarationType (SST.Annotation { id }) name _ _ → do
      let
        typeKind ∷ TypeKind
        typeKind = TypeKindSynoynm id

        exportKind ∷ ExportKind
        exportKind = typeExportKind name exportMap
      insertOrError name typeKind exportKind DuplicateType typesRaw
    SST.DeclarationNewtype (SST.Annotation { id }) name _ (SST.NewtypeEquation { constructor }) → do
      let
        typeKind ∷ TypeKind
        typeKind = TypeKindNewtype id

        exportKind ∷ ExportKind
        exportKind = typeExportKind name exportMap
      insertOrError name typeKind exportKind DuplicateType typesRaw
      collectNewtypeCtor name constructor
    SST.DeclarationClass (SST.Annotation { id }) name _ (SST.ClassEquation { methods }) → do
      let
        typeKind ∷ TypeKind
        typeKind = TypeKindClass id

        exportKind ∷ ExportKind
        exportKind = typeExportKind name exportMap
      insertOrError name typeKind exportKind DuplicateType typesRaw
      traverse_ (traverse_ $ collectClassMethod name) methods
    SST.DeclarationValue (SST.Annotation { id }) name _ _ → do
      let
        valueKind ∷ ValueKind
        valueKind = ValueKindValue id

        exportKind ∷ ExportKind
        exportKind = valueExportKind name exportMap
      insertOrError name valueKind exportKind DuplicateValue valuesRaw
    _ →
      pure unit

  constructors ← MutableObject.unsafeFreeze constructorsRaw
  types ← MutableObject.unsafeFreeze typesRaw
  values ← MutableObject.unsafeFreeze valuesRaw

  for_ exportMap case _ of
    ExportMap { types: exMapTypes, values: exMapValues } → do
      forWithIndex_ exMapTypes \name members → do
        unless (Object.member name types) do
          void $ MutableArray.push (MissingType (coerce name)) errorsRaw
        for_ members case _ of
          SST.DataAll →
            pure unit
          SST.DataEnumerated dataEnumerated →
            for_ dataEnumerated \dataMember → do
              unless (Object.member (coerce dataMember) constructors) do
                void $ MutableArray.push (MissingConstructor dataMember) errorsRaw
      forWithIndex_ exMapValues \name _ →
        unless (Object.member name values) do
          void $ MutableArray.push (MissingValue (coerce name)) errorsRaw

  errors ← MutableArray.unsafeFreeze errorsRaw

  let
    interface ∷ Interface
    interface = Interface { constructors, types, values }

  pure $ { interface, errors }