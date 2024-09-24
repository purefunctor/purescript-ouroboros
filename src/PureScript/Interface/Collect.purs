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
import Partial.Unsafe (unsafeCrashWith)
import PureScript.CST.Types (Ident(..), ModuleName, Proper(..))
import PureScript.Driver.Query.Stable (FileId)
import PureScript.Interface.Collect.Monad (InterfaceM)
import PureScript.Interface.Collect.Monad as Monad
import PureScript.Interface.Error (InterfaceError(..))
import PureScript.Interface.Types
  ( Binding(..)
  , BindingKind(..)
  , ConstructorKind(..)
  , ImportKind(..)
  , Interface(..)
  , TypeKind(..)
  , ValueKind(..)
  , bindingKindIsExported
  , constructorTypeName
  )
import PureScript.Surface.Syntax.Tree (ModuleImportId)
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

constructorBindingKind ∷ Proper → Proper → Maybe ExportMap → BindingKind
constructorBindingKind (Proper dataName) constructorName = maybe BindingKindOpen case _ of
  ExportMap { types } → case Object.lookup dataName types of
    Nothing →
      BindingKindHidden
    -- T
    Just Nothing →
      BindingKindHidden
    -- T(..)
    Just (Just SST.DataAll) →
      BindingKindExported
    -- T(U, V)
    Just (Just (SST.DataEnumerated dataMembers)) →
      maybe BindingKindHidden (const BindingKindExported)
        $ Array.find (eq constructorName) dataMembers

typeBindingKind ∷ Proper → Maybe ExportMap → BindingKind
typeBindingKind (Proper typeName) = maybe BindingKindOpen case _ of
  ExportMap { types } →
    if Object.member typeName types then
      BindingKindExported
    else
      BindingKindHidden

valueBindingKind ∷ Ident → Maybe ExportMap → BindingKind
valueBindingKind (Ident valueName) = maybe BindingKindOpen case _ of
  ExportMap { values } →
    if Object.member valueName values then
      BindingKindExported
    else
      BindingKindHidden

type Input r =
  { lookupModule ∷ ModuleName → ST r (Maybe FileId)
  , lookupInterface ∷ FileId → ST r Result
  }

type Result =
  { interface ∷ Interface
  , errors ∷ Array InterfaceError
  }

newtype ImportMap = ImportMap
  { types ∷ Object (Maybe SST.DataMembers)
  , values ∷ Object Unit
  }

inferImportMap ∷ ∀ r. NonEmptyArray SST.Import → ST r ImportMap
inferImportMap imports = do
  typesRaw ← MutableObject.empty
  valuesRaw ← MutableObject.empty

  for_ imports case _ of
    SST.ImportValue name →
      MutableObject.poke name unit valuesRaw
    SST.ImportOp _ →
      unsafeCrashWith "todo: ImportOp"
    SST.ImportType name memberList →
      MutableObject.poke name memberList typesRaw
    SST.ImportTypeOp _ →
      unsafeCrashWith "todo: ImportTypeOp"
    SST.ImportClass name →
      MutableObject.poke name Nothing typesRaw
    SST.ImportNotImplemented →
      pure unit

  map ImportMap $ { types: _, values: _ }
    <$> MutableObject.unsafeFreeze typesRaw
    <*> MutableObject.unsafeFreeze valuesRaw

type ImportConstructorFn a = ModuleImportId → Proper → Binding a → Boolean → Maybe ImportMap → Binding a

importConstructorBinding ∷ ImportConstructorFn ConstructorKind
importConstructorBinding importId cName (Binding { kind: bKind, id }) hiding importMap = do
  let
    importExported ∷ Boolean
    importExported = bindingKindIsExported bKind

    tName ∷ Proper
    tName = constructorTypeName id

    importKind ∷ ImportKind
    importKind = importMap # maybe ImportKindOpen case _ of
      ImportMap { types } → ImportKindClosed
        { hiding
        , explicit: case Object.lookup (coerce tName) types of
            Nothing →
              false
            Just Nothing →
              false
            Just (Just SST.DataAll) →
              true
            Just (Just (SST.DataEnumerated dataMembers)) →
              Array.elem cName dataMembers
        }

  Binding { kind: BindingKindImported { importId, importKind, importExported }, id }

importConstructorType ∷ ImportConstructorFn TypeKind
importConstructorType importId tName (Binding { kind: bKind, id }) hiding importMap = do
  let
    importExported ∷ Boolean
    importExported = bindingKindIsExported bKind

    importKind ∷ ImportKind
    importKind = importMap # maybe ImportKindOpen case _ of
      ImportMap { types } → ImportKindClosed { hiding, explicit: Object.member (coerce tName) types }

  Binding { kind: BindingKindImported { importId, importKind, importExported }, id }

importConstructorValue ∷ ImportConstructorFn ValueKind
importConstructorValue importId vName (Binding { kind: bKind, id }) hiding importMap = do
  let
    importExported ∷ Boolean
    importExported = bindingKindIsExported bKind

    importKind ∷ ImportKind
    importKind = importMap # maybe ImportKindOpen case _ of
      ImportMap { values } → ImportKindClosed { hiding, explicit: Object.member (coerce vName) values }

  Binding { kind: BindingKindImported { importId, importKind, importExported }, id }

collectImport ∷ ∀ r. Input r → SST.ModuleImport → InterfaceM r Unit
collectImport input (SST.ModuleImport { annotation: SST.Annotation { id }, name, importList, qualified }) = do
  let
    { hiding, imports } = case importList of
      Just (SST.ImportList { hiding, imports }) →
        { hiding, imports: Just imports }
      Nothing →
        { hiding: false, imports: Nothing }
  importMap ← liftST $ traverse inferImportMap imports
  maybeImportFileId ← liftST $ input.lookupModule name
  for_ maybeImportFileId \importFileId → do
    { interface: Interface interface } ← liftST $ input.lookupInterface importFileId
    forWithIndex_ interface.constructors \k v → do
      Monad.insertOrErrorConstructor qualified (coerce k) $ importConstructorBinding id (coerce k) v hiding importMap
    forWithIndex_ interface.types \k v →
      Monad.insertOrErrorType qualified (coerce k) $ importConstructorType id (coerce k) v hiding importMap
    forWithIndex_ interface.values \k v →
      Monad.insertOrErrorValue qualified (coerce k) $ importConstructorValue id (coerce k) v hiding importMap

collectInterface ∷ ∀ r. Input r → SST.Module → ST r Result
collectInterface input (SST.Module { exports, imports, declarations }) = Monad.run do
  traverse_ (collectImport input) imports

  exportMap ← liftST $ traverse inferExportMap exports

  for_ declarations case _ of
    -- data Maybe a = Just a | Nothing
    SST.DeclarationData (SST.Annotation { id }) tName _ (SST.DataEquation { constructors }) → do
      Monad.insertOrErrorType Nothing tName $ Binding
        { kind: typeBindingKind tName exportMap
        , id: TypeKindData id
        }

      for_ constructors $ traverse_ case _ of
        SST.DataConstructor { annotation: SST.Annotation { id: cId }, name: cName } → do
          Monad.insertOrErrorConstructor Nothing cName $ Binding
            { kind: constructorBindingKind tName cName exportMap
            , id: ConstructorKindData tName cId
            }

    -- type Function a b = a -> b
    SST.DeclarationType (SST.Annotation { id }) tName _ _ → do
      Monad.insertOrErrorType Nothing tName $ Binding
        { kind: typeBindingKind tName exportMap
        , id: TypeKindSynoynm id
        }

    -- newtype Identity a = Identity a
    SST.DeclarationNewtype (SST.Annotation { id }) tName _ (SST.NewtypeEquation { constructor }) → do
      Monad.insertOrErrorType Nothing tName $ Binding
        { kind: typeBindingKind tName exportMap
        , id: TypeKindNewtype id
        }

      case constructor of
        SST.NewtypeConstructor { annotation: SST.Annotation { id: cId }, name: cName } → do
          Monad.insertOrErrorConstructor Nothing cName $ Binding
            { kind: constructorBindingKind tName cName exportMap
            , id: ConstructorKindNewtype tName cId
            }

    -- class Functor f where map :: forall a b. (a -> b) -> f a -> f b
    SST.DeclarationClass (SST.Annotation { id }) tName _ (SST.ClassEquation { methods }) → do
      Monad.insertOrErrorType Nothing tName $ Binding
        { kind: typeBindingKind tName exportMap
        , id: TypeKindClass id
        }

      for_ methods $ traverse_ case _ of
        SST.ClassMethod { annotation: SST.Annotation { id: mId }, name: mName } → do
          Monad.insertOrErrorValue Nothing mName $ Binding
            { kind: valueBindingKind mName exportMap
            , id: ValueKindMethod tName mId
            }

    -- life = 42
    SST.DeclarationValue (SST.Annotation { id }) vName _ _ → do
      Monad.insertOrErrorValue Nothing vName $ Binding
        { kind: valueBindingKind vName exportMap
        , id: ValueKindValue id
        }

    _ →
      pure unit

  for_ exportMap case _ of
    ExportMap { types: exMapTypes, values: exMapValues } → do
      forWithIndex_ exMapTypes \name members → do
        { unqualified: { constructors, types } } ← Monad.ask
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
        { unqualified: { values } } ← Monad.ask
        valueExport ← liftST $ MutableObject.peek (coerce name) values
        when (isNothing valueExport) do
          Monad.addError (MissingValue (coerce name))

  { unqualified: { constructors, types, values }, errors } ← Monad.ask

  interface ← liftST $ { constructors: _, types: _, values: _ }
    <$> MutableObject.unsafeFreeze constructors
    <*> MutableObject.unsafeFreeze types
    <*> MutableObject.unsafeFreeze values

  liftST $ { interface: Interface interface, errors: _ }
    <$> MutableArray.unsafeFreeze errors
