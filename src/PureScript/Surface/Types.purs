module PureScript.Surface.Types where

import Prelude
import Prim hiding (Row, Type)

import Data.Array.NonEmpty (NonEmptyArray)
import Data.Maybe (Maybe)
import Data.Tuple (Tuple)
import Prim as Prim
import PureScript.CST.Types (Ident, IntValue, Label, ModuleName, Operator, Proper)

newtype QualifiedName a = QualifiedName
  { moduleName ∷ Maybe ModuleName
  , name ∷ a
  }

derive newtype instance Eq a ⇒ Eq (QualifiedName a)

newtype Index ∷ Prim.Type → Prim.Type
newtype Index a = Index Int

derive newtype instance Eq (Index a)

newtype Annotation a = Annotation
  { index ∷ Index a
  }

derive newtype instance Eq (Annotation a)

newtype SparseMap ∷ Prim.Type → Prim.Type → Prim.Type
newtype SparseMap k v = SparseMap (Array v)

derive newtype instance Eq v ⇒ Eq (SparseMap k v)

newtype Module = Module
  { name ∷ ModuleName
  , imports ∷ Array Import
  , declarations ∷ Array Declaration
  }

derive newtype instance Eq Module

newtype Import = Import
  { name ∷ ModuleName
  }

derive newtype instance Eq Import

type DeclarationAnnotation = Annotation Declaration
type DeclarationIndex = Index Declaration

newtype ValueEquation = ValueEquation
  { binders ∷ Array Binder
  , guarded ∷ Guarded
  }

derive newtype instance Eq ValueEquation

data Declaration
  = DeclarationValue DeclarationAnnotation Ident (Maybe Type) (Array ValueEquation)
  | DeclarationNotImplemented DeclarationAnnotation

derive instance Eq Declaration

data TypeVarBinding a
  = TypeVarKinded Boolean a Type
  | TypeVarName Boolean a

derive instance Eq a ⇒ Eq (TypeVarBinding a)

data Guarded
  = Unconditional Where
  | Guarded (NonEmptyArray GuardedExpr)

derive instance Eq Guarded

data GuardedExpr = GuardedExpr (NonEmptyArray PatternGuard) Where

derive instance Eq GuardedExpr

data PatternGuard = PatternGuard (Maybe Binder) Expr

derive instance Eq PatternGuard

type LetBindingAnnotation = Annotation LetBinding
type LetBindingIndex = Index LetBinding

data LetBinding
  = LetBindingValue LetBindingAnnotation Ident (Maybe Type) (Array ValueEquation)
  | LetBindingPattern LetBindingAnnotation Binder Where
  | LetBindingNotImplemented LetBindingAnnotation

derive instance Eq LetBinding

data Where = Where Expr (Array LetBinding)

derive instance Eq Where

type ExprAnnotation = Annotation Expr
type ExprIndex = Index Expr

data Expr
  = ExprHole ExprAnnotation Ident
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
  | ExprRecordAccessor ExprAnnotation Expr (NonEmptyArray Label)
  | ExprRecordUpdate ExprAnnotation Expr (NonEmptyArray RecordUpdate)
  | ExprApplication ExprAnnotation Expr (NonEmptyArray AppSpine)
  | ExprLambda ExprAnnotation (NonEmptyArray Binder) Expr
  | ExprIfThenElse ExprAnnotation Expr Expr Expr
  | ExprCase
      ExprAnnotation
      (NonEmptyArray Expr)
      (NonEmptyArray (Tuple (NonEmptyArray Binder) Guarded))
  | ExprLet ExprAnnotation (NonEmptyArray LetBinding) Expr
  | ExprDo ExprAnnotation (NonEmptyArray DoStatement)
  | ExprAdo ExprAnnotation (Array DoStatement) Expr
  | ExprNotImplemented ExprAnnotation

derive instance Eq Expr

data AppSpine
  = AppTerm Expr
  | AppType Type

derive instance Eq AppSpine

data RecordLabeled a
  = RecordPun Ident
  | RecordField Label a

derive instance Eq a ⇒ Eq (RecordLabeled a)

data RecordUpdate
  = RecordUpdateLeaf Label Expr
  | RecordUpdateBranch Label (NonEmptyArray RecordUpdate)

derive instance Eq RecordUpdate

data DoStatement
  = DoLet (NonEmptyArray LetBinding)
  | DoDiscard Expr
  | DoBind Binder Expr
  | DoNotImplemented

derive instance Eq DoStatement

type BinderAnnotation = Annotation Binder
type BinderIndex = Index Binder

data Binder
  = BinderWildcard BinderAnnotation
  | BinderVar BinderAnnotation Ident
  | BinderNamed BinderAnnotation Ident Binder
  | BinderConstructor BinderAnnotation (QualifiedName Proper) (Array Binder)
  | BinderBoolean BinderAnnotation Boolean
  | BinderChar BinderAnnotation Char
  | BinderString BinderAnnotation String
  | BinderInt BinderAnnotation Boolean IntValue
  | BinderNumber BinderAnnotation Boolean Number
  | BinderArray BinderAnnotation (Array Binder)
  | BinderRecord BinderAnnotation (Array (RecordLabeled Binder))
  | BinderParens BinderAnnotation Binder
  | BinderTyped BinderAnnotation Binder Type
  | BinderOp BinderAnnotation Binder (NonEmptyArray (Tuple (QualifiedName Operator) Binder))
  | BinderNotImplemented BinderAnnotation

derive instance Eq Binder

type TypeAnnotation = Annotation Type
type TypeIndex = Index Type

data Type
  = TypeVar TypeAnnotation Ident
  | TypeConstructor TypeAnnotation (QualifiedName Proper)
  | TypeWildcard TypeAnnotation
  | TypeHole TypeAnnotation Ident
  | TypeString TypeAnnotation String
  | TypeInt TypeAnnotation Boolean IntValue
  | TypeRow TypeAnnotation Row
  | TypeRecord TypeAnnotation Row
  | TypeForall TypeAnnotation (NonEmptyArray (TypeVarBinding Ident)) Type
  | TypeKinded TypeAnnotation Type Type
  | TypeApp TypeAnnotation Type (NonEmptyArray Type)
  | TypeOp TypeAnnotation Type (NonEmptyArray (Tuple (QualifiedName Operator) Type))
  | TypeOpName TypeAnnotation (QualifiedName Operator)
  | TypeArrow TypeAnnotation Type Type
  | TypeArrowName TypeAnnotation
  | TypeConstrained TypeAnnotation Type Type
  | TypeParens TypeAnnotation Type
  | TypeNotImplemented TypeAnnotation

derive instance Eq Type

data Row = Row (Array (Tuple Label Type)) (Maybe Type)

derive instance Eq Row
