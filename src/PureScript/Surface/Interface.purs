module PureScript.Surface.Interface where

import Prelude

import Control.Monad.ST (ST)
import Control.Monad.ST as ST
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse_)
import Foreign.Object (Object)
import Foreign.Object as Object
import PureScript.CST.Types (Ident(..), Proper(..))
import PureScript.Surface.Types as SST
import PureScript.Utils.Mutable.Array as MutableArray
import PureScript.Utils.Mutable.Object as MutableObject
import Safe.Coerce (class Coercible, coerce)

newtype Interface = Interface
  { dataConstructors ∷ Object SST.ConstructorIndex
  , newtypeConstructors ∷ Object SST.NewtypeIndex
  , classMethods ∷ Object SST.ClassMethodIndex
  , types ∷ Object SST.DeclarationIndex
  , values ∷ Object SST.DeclarationIndex
  }

derive instance Eq Interface

data InterfaceError
  = MissingMember Proper
  | MissingType Proper
  | MissingValue Ident

derive instance Eq InterfaceError

type InterfaceWithErrors =
  { interface ∷ Interface
  , errors ∷ Array InterfaceError
  }

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

collectInterface ∷ SST.Module → InterfaceWithErrors
collectInterface (SST.Module { exports, declarations }) = ST.run do
  dataConstructorsRaw ← MutableObject.empty
  newtypeConstructorsRaw ← MutableObject.empty
  classMethodsRaw ← MutableObject.empty
  typesRaw ← MutableObject.empty
  valuesRaw ← MutableObject.empty

  let
    collectDataCtor ∷ SST.DataConstructor → _
    collectDataCtor = case _ of
      SST.DataConstructor { annotation: SST.Annotation { index }, name } →
        MutableObject.poke name index dataConstructorsRaw

    collectNewtypeCtor ∷ SST.NewtypeConstructor → _
    collectNewtypeCtor = case _ of
      SST.NewtypeConstructor { annotation: SST.Annotation { index }, name } →
        MutableObject.poke name index newtypeConstructorsRaw

    collectMethod ∷ SST.ClassMethod → _
    collectMethod = case _ of
      SST.ClassMethod { annotation: SST.Annotation { index }, name } →
        MutableObject.poke name index classMethodsRaw

  for_ declarations case _ of
    SST.DeclarationData (SST.Annotation { index }) name _ (SST.DataEquation { constructors }) →
      do
        traverse_ (traverse_ collectDataCtor) constructors
        MutableObject.poke name index typesRaw
    SST.DeclarationType (SST.Annotation { index }) name _ _ →
      MutableObject.poke name index typesRaw
    SST.DeclarationNewtype (SST.Annotation { index }) name _ (SST.NewtypeEquation { constructor }) →
      do
        collectNewtypeCtor constructor
        MutableObject.poke name index typesRaw
    SST.DeclarationClass (SST.Annotation { index }) name _ (SST.ClassEquation { methods }) → do
      traverse_ (traverse_ collectMethod) methods
      MutableObject.poke name index typesRaw
    SST.DeclarationValue (SST.Annotation { index }) name _ _ →
      MutableObject.poke name index valuesRaw
    SST.DeclarationNotImplemented _ →
      pure unit

  interface ← coerce do
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

  let
    errors ∷ Array InterfaceError
    errors = checkExports interface exports

  pure { interface, errors }
