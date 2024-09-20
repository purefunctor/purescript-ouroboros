module PureScript.Surface.Lower.State where

import Prelude

import Control.Monad.ST (Region, ST)
import Control.Monad.ST.Internal (STRef)
import Control.Monad.ST.Ref as STRef
import Data.HashMap (HashMap)
import Data.HashMap as HashMap
import PureScript.CST.Errors (RecoveredError)
import PureScript.Id (Id(..))
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
type MakeSourceRange r t s = STRef r (HashMap (Id t) s)

type MakeRecoveredError ∷ Region → Type → Type
type MakeRecoveredError r t = STRef r (HashMap (Id t) RecoveredError)

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
    moduleImport ← STRef.new 0
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
      , moduleImport
      }
  sourceRanges ← do
    expr ← STRef.new HashMap.empty
    binder ← STRef.new HashMap.empty
    type_ ← STRef.new HashMap.empty
    doStatement ← STRef.new HashMap.empty
    letBinding ← STRef.new HashMap.empty
    declaration ← STRef.new HashMap.empty
    constructor ← STRef.new HashMap.empty
    newtype_ ← STRef.new HashMap.empty
    classMethod ← STRef.new HashMap.empty
    typeVarBinding ← STRef.new HashMap.empty
    moduleImport ← STRef.new HashMap.empty
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
      , moduleImport
      }
  recoveredErrors ← do
    expr ← STRef.new HashMap.empty
    binder ← STRef.new HashMap.empty
    type_ ← STRef.new HashMap.empty
    doStatement ← STRef.new HashMap.empty
    letBinding ← STRef.new HashMap.empty
    declaration ← STRef.new HashMap.empty
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
    expr ← STRef.read sourceRanges.expr
    binder ← STRef.read sourceRanges.binder
    type_ ← STRef.read sourceRanges."type"
    doStatement ← STRef.read sourceRanges.doStatement
    letBinding ← STRef.read sourceRanges.letBinding
    declaration ← STRef.read sourceRanges.declaration
    constructor ← STRef.read sourceRanges.constructor
    newtype_ ← STRef.read sourceRanges."newtype"
    classMethod ← STRef.read sourceRanges.classMethod
    typeVarBinding ← STRef.read sourceRanges.typeVarBinding
    moduleImport ← STRef.read sourceRanges.moduleImport
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
      , moduleImport
      }
  recoveredErrors' ← do
    expr ← STRef.read recoveredErrors.expr
    binder ← STRef.read recoveredErrors.binder
    type_ ← STRef.read recoveredErrors."type"
    doStatement ← STRef.read recoveredErrors.doStatement
    letBinding ← STRef.read recoveredErrors.letBinding
    declaration ← STRef.read recoveredErrors.declaration
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
  . ({ | SourceRangeFields r } → STRef r (HashMap (Id t) s))
  → State r
  → Id t
  → s
  → ST r Unit
insertSourceRange get (State { sourceRanges }) id sourceRange = do
  let
    ref ∷ STRef r (HashMap (Id t) s)
    ref = get sourceRanges
  void $ STRef.modify (HashMap.insert id sourceRange) ref

insertError
  ∷ ∀ r e t
  . IntoRecoveredError e
  ⇒ ({ | RecoveredErrorFields r } → STRef r (HashMap (Id t) RecoveredError))
  → State r
  → Id t
  → e
  → ST r Unit
insertError get (State { recoveredErrors }) id error = do
  let
    ref ∷ STRef r (HashMap (Id t) RecoveredError)
    ref = get recoveredErrors
  void $ STRef.modify (HashMap.insert id (intoRecoveredError error)) ref
