module PureScript.Surface.Lower.State where

import Prelude

import Control.Monad.ST (Region, ST)
import Control.Monad.ST.Internal (STRef)
import Control.Monad.ST.Ref as STRef
import Data.Symbol (class IsSymbol)
import Prim.Row as Row
import PureScript.CST.Errors (RecoveredError)
import PureScript.Id (Id(..), IdMap(..))
import PureScript.Surface.Lower.Error (class IntoRecoveredError, intoRecoveredError)
import PureScript.Surface.Lower.Types
  ( ErrorFieldGroup
  , FieldGroup
  , RecoveredErrors(..)
  , SourceRanges(..)
  )
import PureScript.Utils.Mutable.STIntMap (STIntMap)
import PureScript.Utils.Mutable.STIntMap as STIntMap
import Record as Record
import Safe.Coerce (coerce)
import Type.Proxy (Proxy(..))

type MakeId ∷ Region → Type → Type → Type
type MakeId r t s = STRef r Int

type MakeSourceRange ∷ Region → Type → Type → Type
type MakeSourceRange r t s = STIntMap r s

type MakeRecoveredError ∷ Region → Type → Type
type MakeRecoveredError r t = STIntMap r RecoveredError

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
    expr ← STIntMap.empty
    binder ← STIntMap.empty
    type_ ← STIntMap.empty
    doStatement ← STIntMap.empty
    letBinding ← STIntMap.empty
    declaration ← STIntMap.empty
    constructor ← STIntMap.empty
    newtype_ ← STIntMap.empty
    classMethod ← STIntMap.empty
    typeVarBinding ← STIntMap.empty
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
    expr ← STIntMap.empty
    binder ← STIntMap.empty
    type_ ← STIntMap.empty
    doStatement ← STIntMap.empty
    letBinding ← STIntMap.empty
    declaration ← STIntMap.empty
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
    expr ← STIntMap.freeze sourceRanges.expr
    binder ← STIntMap.freeze sourceRanges.binder
    type_ ← STIntMap.freeze sourceRanges."type"
    doStatement ← STIntMap.freeze sourceRanges.doStatement
    letBinding ← STIntMap.freeze sourceRanges.letBinding
    declaration ← STIntMap.freeze sourceRanges.declaration
    constructor ← STIntMap.freeze sourceRanges.constructor
    newtype_ ← STIntMap.freeze sourceRanges."newtype"
    classMethod ← STIntMap.freeze sourceRanges.classMethod
    typeVarBinding ← STIntMap.freeze sourceRanges.typeVarBinding
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
    expr ← STIntMap.freeze recoveredErrors.expr
    binder ← STIntMap.freeze recoveredErrors.binder
    type_ ← STIntMap.freeze recoveredErrors."type"
    doStatement ← STIntMap.freeze recoveredErrors.doStatement
    letBinding ← STIntMap.freeze recoveredErrors.letBinding
    declaration ← STIntMap.freeze recoveredErrors.declaration
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
  ∷ ∀ @n r t _t
  . IsSymbol n
  ⇒ Row.Cons n (STRef r Int) _t (IdFields r)
  ⇒ State r
  → ST r (Id t)
nextId (State { ids }) = do
  let
    ref ∷ STRef r Int
    ref = Record.get (Proxy ∷ _ n) ids
  id ← STRef.read ref
  void $ STRef.modify (_ + 1) ref
  pure $ coerce id

insertSourceRange
  ∷ ∀ @n r s t _t
  . IsSymbol n
  ⇒ Row.Cons n (STIntMap r s) _t (SourceRangeFields r)
  ⇒ State r
  → Id t
  → s
  → ST r Unit
insertSourceRange (State { sourceRanges }) id sourceRange = do
  let
    ref ∷ STIntMap r s
    ref = Record.get (Proxy ∷ _ n) sourceRanges
  STIntMap.set (coerce id) sourceRange ref

insertError
  ∷ ∀ @n r e t _t
  . IsSymbol n
  ⇒ Row.Cons n (STIntMap r RecoveredError) _t (RecoveredErrorFields r)
  ⇒ IntoRecoveredError e
  ⇒ State r
  → Id t
  → e
  → ST r Unit
insertError (State { recoveredErrors }) index error = do
  let
    ref ∷ STIntMap r RecoveredError
    ref = Record.get (Proxy ∷ _ n) recoveredErrors
  STIntMap.set (coerce index) (intoRecoveredError error) ref
