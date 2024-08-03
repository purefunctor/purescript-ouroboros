module PureScript.Surface.Types where

import Prelude
import Prim hiding (Row, Type)

import Data.Array.NonEmpty (NonEmptyArray)
import Data.Maybe (Maybe)
import Data.Tuple (Tuple)
import Prim as Prim
import PureScript.CST.Types (Ident, IntValue, Label, ModuleName, Operator, Proper)
import PureScript.Id (Id)

newtype QualifiedName a = QualifiedName
  { moduleName ∷ Maybe ModuleName
  , name ∷ a
  }

derive newtype instance Eq a ⇒ Eq (QualifiedName a)

newtype Annotation a = Annotation
  { id ∷ Id a
  }

derive newtype instance Eq (Annotation a)

newtype Module = Module
  { name ∷ ModuleName
  , exports ∷ Maybe (NonEmptyArray Export)
  , imports ∷ Array Import
  , declarations ∷ Array Declaration
  }

derive newtype instance Eq Module

data Export
  = ExportValue Ident
  | ExportOp Operator
  | ExportType Proper (Maybe DataMembers)
  | ExportTypeOp Operator
  | ExportClass Proper
  | ExportModule ModuleName
  | ExportNotImplemented

derive instance Eq Export

data DataMembers
  = DataAll
  | DataEnumerated (Array Proper)

derive instance Eq DataMembers

newtype Import = Import
  { name ∷ ModuleName
  }

derive newtype instance Eq Import

type DeclarationAnnotation = Annotation Declaration
type DeclarationId = Id Declaration

newtype ValueEquation = ValueEquation
  { binders ∷ Array Binder
  , guarded ∷ Guarded
  }

derive newtype instance Eq ValueEquation

type ConstructorAnnotation = Annotation DataConstructor
type ConstructorId = Id DataConstructor

newtype DataConstructor = DataConstructor
  { annotation ∷ ConstructorAnnotation
  , name ∷ Proper
  , fields ∷ Array Type
  }

derive newtype instance Eq DataConstructor

newtype DataEquation = DataEquation
  { variables ∷ Array TypeVarBinding
  , constructors ∷ Maybe (NonEmptyArray DataConstructor)
  }

derive newtype instance Eq DataEquation

newtype TypeEquation = TypeEquation
  { variables ∷ Array TypeVarBinding
  , synonymTo ∷ Type
  }

derive newtype instance Eq TypeEquation

type NewtypeAnnotation = Annotation NewtypeConstructor
type NewtypeId = Id NewtypeConstructor

newtype NewtypeConstructor = NewtypeConstructor
  { annotation ∷ NewtypeAnnotation
  , name ∷ Proper
  , field ∷ Type
  }

derive newtype instance Eq NewtypeConstructor

newtype NewtypeEquation = NewtypeEquation
  { variables ∷ Array TypeVarBinding
  , constructor ∷ NewtypeConstructor
  }

derive newtype instance Eq NewtypeEquation

newtype ClassEquation = ClassEquation
  { variables ∷ Array TypeVarBinding
  , methods ∷ Maybe (NonEmptyArray ClassMethod)
  }

derive newtype instance Eq ClassEquation

type ClassMethodAnnotation = Annotation ClassMethod
type ClassMethodId = Id ClassMethod

newtype ClassMethod = ClassMethod
  { annotation ∷ ClassMethodAnnotation
  , name ∷ Ident
  , signature ∷ Type
  }

derive newtype instance Eq ClassMethod

data Declaration
  = DeclarationData DeclarationAnnotation Proper (Maybe Type) DataEquation
  | DeclarationType DeclarationAnnotation Proper (Maybe Type) TypeEquation
  | DeclarationNewtype DeclarationAnnotation Proper (Maybe Type) NewtypeEquation
  | DeclarationClass DeclarationAnnotation Proper (Maybe Type) ClassEquation
  | DeclarationValue DeclarationAnnotation Ident (Maybe Type) (Array ValueEquation)
  | DeclarationNotImplemented DeclarationAnnotation

derive instance Eq Declaration

type TypeVarBindingAnnotation = Annotation TypeVarBinding
type TypeVarBindingId = Id TypeVarBinding

data TypeVarBinding
  = TypeVarKinded TypeVarBindingAnnotation Boolean Ident Type
  | TypeVarName TypeVarBindingAnnotation Boolean Ident

derive instance Eq TypeVarBinding

data Guarded
  = Unconditional Where
  | Guarded (NonEmptyArray GuardedExpr)

derive instance Eq Guarded

data GuardedExpr = GuardedExpr (NonEmptyArray PatternGuard) Where

derive instance Eq GuardedExpr

data PatternGuard = PatternGuard (Maybe Binder) Expr

derive instance Eq PatternGuard

type LetBindingAnnotation = Annotation LetBinding
type LetBindingId = Id LetBinding

data LetBinding
  = LetBindingValue LetBindingAnnotation Ident (Maybe Type) (Array ValueEquation)
  | LetBindingPattern LetBindingAnnotation Binder Where
  | LetBindingError LetBindingAnnotation
  | LetBindingNotImplemented LetBindingAnnotation

derive instance Eq LetBinding

data Where = Where Expr (Array LetBinding)

derive instance Eq Where

type ExprAnnotation = Annotation Expr
type ExprId = Id Expr

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
  | ExprError ExprAnnotation
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

type DoStatementAnnotation = Annotation DoStatement
type DoStatementId = Id DoStatement

data DoStatement
  = DoLet DoStatementAnnotation (NonEmptyArray LetBinding)
  | DoDiscard DoStatementAnnotation Expr
  | DoBind DoStatementAnnotation Binder Expr
  | DoError DoStatementAnnotation
  | DoNotImplemented DoStatementAnnotation

derive instance Eq DoStatement

type BinderAnnotation = Annotation Binder
type BinderId = Id Binder

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
  | BinderError BinderAnnotation
  | BinderNotImplemented BinderAnnotation

derive instance Eq Binder

type TypeAnnotation = Annotation Type
type TypeId = Id Type

data Type
  = TypeVar TypeAnnotation Ident
  | TypeConstructor TypeAnnotation (QualifiedName Proper)
  | TypeWildcard TypeAnnotation
  | TypeHole TypeAnnotation Ident
  | TypeString TypeAnnotation String
  | TypeInt TypeAnnotation Boolean IntValue
  | TypeRow TypeAnnotation Row
  | TypeRecord TypeAnnotation Row
  | TypeForall TypeAnnotation (NonEmptyArray TypeVarBinding) Type
  | TypeKinded TypeAnnotation Type Type
  | TypeApp TypeAnnotation Type (NonEmptyArray Type)
  | TypeOp TypeAnnotation Type (NonEmptyArray (Tuple (QualifiedName Operator) Type))
  | TypeOpName TypeAnnotation (QualifiedName Operator)
  | TypeArrow TypeAnnotation Type Type
  | TypeArrowName TypeAnnotation
  | TypeConstrained TypeAnnotation Type Type
  | TypeParens TypeAnnotation Type
  | TypeError TypeAnnotation
  | TypeNotImplemented TypeAnnotation

derive instance Eq Type

newtype Row = Row
  { labels ∷ Array (Tuple Label Type)
  , tail ∷ Maybe Type
  }

derive newtype instance Eq Row
