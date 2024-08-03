module PureScript.Interface.Collect where

import Prelude

import Control.Monad.ST (ST)
import Control.Monad.ST as ST
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Foldable (for_)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Traversable (traverse_)
import Foreign.Object (Object)
import Foreign.Object as Object
import PureScript.CST.Types (Ident(..), Proper(..))
import PureScript.Interface.Error (InterfaceError(..))
import PureScript.Interface.Types (Exported(..), Interface(..))
import PureScript.Surface.Syntax.Tree as SST
import PureScript.Utils.Mutable.Array (MutableArray)
import PureScript.Utils.Mutable.Array as MutableArray
import PureScript.Utils.Mutable.Object (MutableObject)
import PureScript.Utils.Mutable.Object as MutableObject
import Safe.Coerce (class Coercible, coerce)
import Unsafe.Coerce (unsafeCoerce)

type Result =
  { interface ∷ Interface
  , exported ∷ Exported
  , errors ∷ Array InterfaceError
  }

pokeMulti ∷ ∀ r k v. Coercible k String ⇒ k → v → MutableObject r k (MutableArray r v) → ST r Unit
pokeMulti k v o = do
  vs ← MutableObject.peek k o >>= case _ of
    Nothing → do
      vs ← MutableArray.empty
      MutableObject.poke k vs o
      pure vs
    Just vs →
      pure vs
  void $ MutableArray.push v vs

lookupMulti ∷ ∀ v. String → Object (Array v) → Array v
lookupMulti k o = fromMaybe [] $ Object.lookup k o

unsafeFreezeMultiValue
  ∷ ∀ r k v. Coercible k String ⇒ MutableObject r k (MutableArray r v) → ST r (Object (Array v))
unsafeFreezeMultiValue = pure <<< unsafeCoerce

collectExported ∷ ∀ r. Interface → Maybe (NonEmptyArray SST.Export) → ST r Result
collectExported interface@(Interface interfaceInner) exports = do
  dataConstructorsRaw ← MutableObject.empty
  newtypeConstructorsRaw ← MutableObject.empty
  classMethodsRaw ← MutableObject.empty
  typesRaw ← MutableObject.empty
  valuesRaw ← MutableObject.empty
  errorsRaw ← MutableArray.empty

  let
    check ∷ ∀ k. Coercible k String ⇒ k → _ → MutableObject r k Unit → _
    check name collection into error =
      if Object.member (coerce name) collection then
        MutableObject.poke name unit into
      else
        void $ MutableArray.push error errorsRaw

  for_ exports $ traverse_ case _ of
    SST.ExportValue name →
      check name interfaceInner.values valuesRaw (MissingValue name)
    SST.ExportType name memberList → do
      check name interfaceInner.types typesRaw (MissingType name)
      let
        members ∷ Array Proper
        members = case memberList of
          Nothing →
            []
          Just SST.DataAll →
            lookupMulti (coerce name) interfaceInner.constructorsOfData
          Just (SST.DataEnumerated enumerated) →
            enumerated
      for_ members \member →
        if Object.member (coerce member) interfaceInner.dataConstructors then
          MutableObject.poke member unit dataConstructorsRaw
        else if Object.member (coerce member) interfaceInner.newtypeConstructors then
          MutableObject.poke member unit newtypeConstructorsRaw
        else
          void $ MutableArray.push (MissingMember member) errorsRaw
    SST.ExportClass name → do
      check name interfaceInner.types typesRaw (MissingType name)
      let
        members ∷ Array Ident
        members = lookupMulti (coerce name) interfaceInner.methodsOfClass
      for_ members \member →
        MutableObject.poke member unit classMethodsRaw
    _ →
      pure unit

  exported ← map Exported do
    { dataConstructors: _
    , newtypeConstructors: _
    , classMethods: _
    , types: _
    , values: _
    } <$> MutableObject.unsafeFreeze dataConstructorsRaw
      <*> MutableObject.unsafeFreeze newtypeConstructorsRaw
      <*> MutableObject.unsafeFreeze classMethodsRaw
      <*> MutableObject.unsafeFreeze typesRaw
      <*> MutableObject.unsafeFreeze valuesRaw
  errors ← MutableArray.unsafeFreeze errorsRaw

  pure $ { interface, exported, errors }

checkExports ∷ Interface → Maybe (NonEmptyArray SST.Export) → Array InterfaceError
checkExports (Interface { dataConstructors, newtypeConstructors, types, values }) = case _ of
  Nothing →
    []
  Just exportList → ST.run do
    errorsRaw ← MutableArray.empty

    let
      check ∷ ∀ k v. Coercible k String ⇒ k → Object v → InterfaceError → ST _ Unit
      check name collection error =
        unless (Object.member (coerce name) collection) do
          void $ MutableArray.push error errorsRaw

      checkMembers ∷ Maybe SST.DataMembers → ST _ Unit
      checkMembers = traverse_ case _ of
        SST.DataAll →
          pure unit
        SST.DataEnumerated members →
          for_ members \member → do
            let
              isMember ∷ String → Boolean
              isMember = flip Object.member dataConstructors
                || flip Object.member newtypeConstructors
            unless (isMember (coerce member)) do
              void $ MutableArray.push (MissingMember member) errorsRaw

    for_ exportList case _ of
      SST.ExportType name members → do
        check name types (MissingType name)
        checkMembers members
      SST.ExportValue name →
        check name values (MissingValue name)
      _ →
        pure unit

    MutableArray.unsafeFreeze errorsRaw

collectInterface ∷ ∀ r. SST.Module → ST r Result
collectInterface (SST.Module { exports, declarations }) = do
  dataConstructorsRaw ← MutableObject.empty
  newtypeConstructorsRaw ← MutableObject.empty
  classMethodsRaw ← MutableObject.empty
  typesRaw ← MutableObject.empty
  valuesRaw ← MutableObject.empty
  constructorsOfDataRaw ← MutableObject.empty
  methodsOfClassRaw ← MutableObject.empty

  let
    collectDataCtor ∷ Proper → SST.DataConstructor → _
    collectDataCtor typeName = case _ of
      SST.DataConstructor { annotation: SST.Annotation { id }, name } → do
        MutableObject.poke name id dataConstructorsRaw
        pokeMulti typeName name constructorsOfDataRaw

    collectNewtypeCtor ∷ Proper → SST.NewtypeConstructor → _
    collectNewtypeCtor typeName = case _ of
      SST.NewtypeConstructor { annotation: SST.Annotation { id }, name } → do
        MutableObject.poke name id newtypeConstructorsRaw
        pokeMulti typeName name constructorsOfDataRaw

    collectMethod ∷ Proper → SST.ClassMethod → _
    collectMethod typeName = case _ of
      SST.ClassMethod { annotation: SST.Annotation { id }, name } → do
        MutableObject.poke name id classMethodsRaw
        pokeMulti typeName name methodsOfClassRaw

  for_ declarations case _ of
    SST.DeclarationData (SST.Annotation { id }) name _ (SST.DataEquation { constructors }) →
      do
        traverse_ (traverse_ $ collectDataCtor name) constructors
        MutableObject.poke name id typesRaw
    SST.DeclarationType (SST.Annotation { id }) name _ _ →
      MutableObject.poke name id typesRaw
    SST.DeclarationNewtype (SST.Annotation { id }) name _ (SST.NewtypeEquation { constructor }) →
      do
        collectNewtypeCtor name constructor
        MutableObject.poke name id typesRaw
    SST.DeclarationClass (SST.Annotation { id }) name _ (SST.ClassEquation { methods }) → do
      traverse_ (traverse_ $ collectMethod name) methods
      MutableObject.poke name id typesRaw
    SST.DeclarationValue (SST.Annotation { id }) name _ _ →
      MutableObject.poke name id valuesRaw
    SST.DeclarationNotImplemented _ →
      pure unit

  interface ← map Interface do
    { dataConstructors: _
    , newtypeConstructors: _
    , classMethods: _
    , types: _
    , values: _
    , constructorsOfData: _
    , methodsOfClass: _
    } <$> MutableObject.unsafeFreeze dataConstructorsRaw
      <*> MutableObject.unsafeFreeze newtypeConstructorsRaw
      <*> MutableObject.unsafeFreeze classMethodsRaw
      <*> MutableObject.unsafeFreeze typesRaw
      <*> MutableObject.unsafeFreeze valuesRaw
      <*> unsafeFreezeMultiValue constructorsOfDataRaw
      <*> unsafeFreezeMultiValue methodsOfClassRaw

  collectExported interface exports
