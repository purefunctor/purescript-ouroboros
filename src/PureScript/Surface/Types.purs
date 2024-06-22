module PureScript.Surface.Types where

import Prim hiding (Row, Type)

import Data.Array.NonEmpty (NonEmptyArray)
import Data.Maybe (Maybe)
import Data.Tuple (Tuple)
import Prim as Prim
import PureScript.CST.Types
  ( Ident
  , IntValue
  , Label
  , ModuleName
  , Name
  , Operator
  , Proper
  , QualifiedName
  )

newtype Index ∷ Prim.Type → Prim.Type
newtype Index a = Index Int

newtype Annotation a = Annotation
  { index ∷ Index a
  }

newtype Module = Module
  { name ∷ ModuleName
  , declarations ∷ Array Declaration
  }

type DeclarationAnnotation = Annotation Declaration
type DeclarationIndex = Index Declaration

newtype ValueEquation = ValueEquation
  { binders ∷ Array Binder
  , guarded ∷ Guarded
  }

data Declaration
  = DeclarationValue DeclarationAnnotation Ident (Maybe Type) (Array ValueEquation)
  | DeclarationNotImplemented DeclarationAnnotation

data TypeVarBinding a
  = TypeVarKinded a Type
  | TypeVarName a

data Guarded
  = Unconditional Where
  | Guarded (NonEmptyArray GuardedExpr)

data GuardedExpr = GuardedExpr (NonEmptyArray PatternGuard) Where

data PatternGuard = PatternGuard (Maybe Binder) Expr

type LetBindingAnnotation = Annotation LetBinding
type LetBindingIndex = Index LetBinding

data LetBinding
  = LetBindingValue LetBindingAnnotation Ident (Maybe Type) (Array ValueEquation)
  | LetBindingPattern LetBindingAnnotation Binder Where
  | LetBindingNotImplemented LetBindingAnnotation

data Where = Where Expr (Array LetBinding)

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

data AppSpine
  = AppTerm Expr
  | AppType Type

data RecordLabeled a
  = RecordPun (Name Ident)
  | RecordField (Name Label) a

data RecordUpdate
  = RecordUpdateLeaf (Name Label) Expr
  | RecordUpdateBranch (Name Label) (NonEmptyArray RecordUpdate)

data DoStatement
  = DoLet (NonEmptyArray LetBinding)
  | DoDiscard Expr
  | DoBind Binder Expr
  | DoNotImplemented

type BinderAnnotation = Annotation Binder
type BinderIndex = Index Binder

data Binder
  = BinderWildcard BinderAnnotation
  | BinderVar BinderAnnotation (Name Ident)
  | BinderNamed BinderAnnotation (Name Ident) Binder
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

type TypeAnnotation = Annotation Type
type TypeIndex = Index Type

data Type
  = TypeVar TypeAnnotation (Name Ident)
  | TypeConstructor TypeAnnotation (QualifiedName Proper)
  | TypeWildcard TypeAnnotation
  | TypeHole TypeAnnotation (Name Ident)
  | TypeString TypeAnnotation String
  | TypeInt TypeAnnotation Boolean IntValue
  | TypeRow TypeAnnotation Row
  | TypeRecord TypeAnnotation Row
  | TypeForall TypeAnnotation (NonEmptyArray (TypeVarBinding (Name Ident))) Type
  | TypeKinded TypeAnnotation Type Type
  | TypeApp TypeAnnotation Type (NonEmptyArray Type)
  | TypeOp TypeAnnotation Type (NonEmptyArray (Tuple (QualifiedName Operator) Type))
  | TypeOpName TypeAnnotation (QualifiedName Operator)
  | TypeArrow TypeAnnotation Type Type
  | TypeArrowName TypeAnnotation
  | TypeConstrained TypeAnnotation Type Type
  | TypeParens TypeAnnotation Type
  | TypeNotImplemented TypeAnnotation

data Row = Row (Array (Tuple (Name Label) Type)) (Maybe Type)
