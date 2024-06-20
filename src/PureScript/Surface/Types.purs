module PureScript.Surface.Types where

import Prim hiding (Type)

import Data.Array.NonEmpty (NonEmptyArray)
import Data.Tuple (Tuple)
import Prim as Prim
import PureScript.CST.Types (Ident, IntValue, Label, Name, Operator, Proper, QualifiedName)

newtype Index ∷ Prim.Type → Prim.Type
newtype Index a = Index Int

newtype Annotation a = Annotation
  { index ∷ Index a
  }

type ExprAnnotation = Annotation Expr
type ExprIndex = Index Expr

data Expr
  = ExprHole ExprAnnotation (Name Ident)
  | ExprSection ExprAnnotation
  | ExprIdent ExprAnnotation (QualifiedName Ident)
  | ExprConstructor ExprAnnotation (QualifiedName Proper)
  | ExprBoolean ExprAnnotation Boolean
  | ExprChar ExprAnnotation Char
  | ExprString ExprAnnotation String
  | ExprInt ExprAnnotation IntValue
  | ExprNumber ExprAnnotation Number
  | ExprArray ExprAnnotation (Array Expr)
  | ExprRecord ExprAnnotation (Array (RecordLabeled Expr))
  | ExprParens ExprAnnotation Expr
  | ExprTyped ExprAnnotation Expr Type
  | ExprInfix ExprAnnotation Expr (NonEmptyArray (Tuple Expr Expr))
  | ExprOp ExprAnnotation Expr (NonEmptyArray (Tuple (QualifiedName Operator) Expr))
  | ExprOpName ExprAnnotation (QualifiedName Operator)
  | ExprNegate ExprAnnotation Expr
  | ExprRecordAccessor ExprAnnotation Expr (NonEmptyArray (Name Label))
  | ExprRecordUpdate ExprAnnotation Expr (NonEmptyArray RecordUpdate)
  | ExprApplication ExprAnnotation Expr (NonEmptyArray AppSpine)
  | ExprNotImplemented ExprAnnotation

data AppSpine
  = AppSpineTerm Expr
  | AppSpineNotImplemented

data RecordLabeled a
  = RecordPun (Name Ident)
  | RecordField (Name Label) a

data RecordUpdate
  = RecordUpdateLeaf (Name Label) Expr
  | RecordUpdateBranch (Name Label) (NonEmptyArray RecordUpdate)

type TypeAnnotation = Annotation Type
type TypeIndex = Index Type

data Type = TypeNotImplemented TypeAnnotation
