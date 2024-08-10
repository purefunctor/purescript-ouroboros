module PureScript.Surface.Lower.State where

import Prelude

import Control.Monad.ST (Region, ST)
import Control.Monad.ST.Internal (STRef)
import Control.Monad.ST.Ref as STRef
import PureScript.CST.Errors (RecoveredError)
import PureScript.Id (Id(..))
import PureScript.Id.STMap (STIdMap)
import PureScript.Id.STMap as STIdMap
import PureScript.Surface.Lower.Error (class IntoRecoveredError, intoRecoveredError)
import PureScript.Surface.Lower.Types
  ( ErrorFieldGroup
  , FieldGroup
  , RecoveredErrors(..)
  , SourceRanges(..)
  )
import Safe.Coerce (coerce)

type MakeId ∷ Region → Type → Type → Type
type MakeId r t s = STRef r Int

type MakeSourceRange ∷ Region → Type → Type → Type
type MakeSourceRange r t s = STIdMap r t s

type MakeRecoveredError ∷ Region → Type → Type
type MakeRecoveredError r t = STIdMap r t RecoveredError

type IdFields r = FieldGroup (MakeId r)
type SourceRangeFields r = FieldGroup (MakeSourceRange r)
type RecoveredErrorFields r = ErrorFieldGroup (MakeRecoveredError r)

newtype State r = State
  { ids ∷ { | IdFields r }
  , sourceRanges ∷ { | SourceRangeFields r }
  , recoveredErrors ∷ { | RecoveredErrorFields r }
  }

empty ∷ ∀ r. ST r (State r)
empty = do
  ids ← do
    expr ← STRef.new 0
    binder ← STRef.new 0
    type_ ← STRef.new 0
    doStatement ← STRef.new 0
    letBinding ← STRef.new 0
    declaration ← STRef.new 0
    constructor ← STRef.new 0
    newtype_ ← STRef.new 0
    classMethod ← STRef.new 0
    typeVarBinding ← STRef.new 0
    pure
      { expr
      , binder
      , type: type_
      , doStatement
      , letBinding
      , declaration
      , constructor
      , newtype: newtype_
      , classMethod
      , typeVarBinding
      }
  sourceRanges ← do
    expr ← STIdMap.empty
    binder ← STIdMap.empty
    type_ ← STIdMap.empty
    doStatement ← STIdMap.empty
    letBinding ← STIdMap.empty
    declaration ← STIdMap.empty
    constructor ← STIdMap.empty
    newtype_ ← STIdMap.empty
    classMethod ← STIdMap.empty
    typeVarBinding ← STIdMap.empty
    pure
      { expr
      , binder
      , type: type_
      , doStatement
      , letBinding
      , declaration
      , constructor
      , newtype: newtype_
      , classMethod
      , typeVarBinding
      }
  recoveredErrors ← do
    expr ← STIdMap.empty
    binder ← STIdMap.empty
    type_ ← STIdMap.empty
    doStatement ← STIdMap.empty
    letBinding ← STIdMap.empty
    declaration ← STIdMap.empty
    pure
      { expr
      , binder
      , type: type_
      , doStatement
      , letBinding
      , declaration
      }
  pure $ State { ids, sourceRanges, recoveredErrors }

freeze ∷ ∀ r. State r → ST r { sourceRanges ∷ SourceRanges, recoveredErrors ∷ RecoveredErrors }
freeze (State { sourceRanges, recoveredErrors }) = do
  sourceRanges' ← do
    expr ← STIdMap.freeze sourceRanges.expr
    binder ← STIdMap.freeze sourceRanges.binder
    type_ ← STIdMap.freeze sourceRanges."type"
    doStatement ← STIdMap.freeze sourceRanges.doStatement
    letBinding ← STIdMap.freeze sourceRanges.letBinding
    declaration ← STIdMap.freeze sourceRanges.declaration
    constructor ← STIdMap.freeze sourceRanges.constructor
    newtype_ ← STIdMap.freeze sourceRanges."newtype"
    classMethod ← STIdMap.freeze sourceRanges.classMethod
    typeVarBinding ← STIdMap.freeze sourceRanges.typeVarBinding
    pure $ SourceRanges $ coerce
      { expr
      , binder
      , type: type_
      , doStatement
      , letBinding
      , declaration
      , constructor
      , newtype: newtype_
      , classMethod
      , typeVarBinding
      }
  recoveredErrors' ← do
    expr ← STIdMap.freeze recoveredErrors.expr
    binder ← STIdMap.freeze recoveredErrors.binder
    type_ ← STIdMap.freeze recoveredErrors."type"
    doStatement ← STIdMap.freeze recoveredErrors.doStatement
    letBinding ← STIdMap.freeze recoveredErrors.letBinding
    declaration ← STIdMap.freeze recoveredErrors.declaration
    pure $ RecoveredErrors $ coerce
      { expr
      , binder
      , type: type_
      , doStatement
      , letBinding
      , declaration
      }
  pure $ { sourceRanges: sourceRanges', recoveredErrors: recoveredErrors' }

nextId
  ∷ ∀ r t
  . ({ | IdFields r } → STRef r Int)
  → State r
  → ST r (Id t)
nextId get (State { ids }) = do
  let
    ref ∷ STRef r Int
    ref = get ids
  id ← STRef.read ref
  void $ STRef.modify (_ + 1) ref
  pure $ coerce id

insertSourceRange
  ∷ ∀ r s t
  . ({ | SourceRangeFields r } → STIdMap r t s)
  → State r
  → Id t
  → s
  → ST r Unit
insertSourceRange get (State { sourceRanges }) id sourceRange = do
  let
    ref ∷ STIdMap r t s
    ref = get sourceRanges
  STIdMap.set id sourceRange ref

insertError
  ∷ ∀ r e t
  . IntoRecoveredError e
  ⇒ ({ | RecoveredErrorFields r } → STIdMap r t RecoveredError)
  → State r
  → Id t
  → e
  → ST r Unit
insertError get (State { recoveredErrors }) id error = do
  let
    ref ∷ STIdMap r t RecoveredError
    ref = get recoveredErrors
  STIdMap.set id (intoRecoveredError error) ref
