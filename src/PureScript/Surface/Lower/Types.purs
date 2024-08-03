module PureScript.Surface.Lower.Types where

import Prelude

import Data.Maybe (Maybe)
import PureScript.CST.Errors (RecoveredError)
import PureScript.CST.Types (SourceRange)
import PureScript.Id (IdMap)
import PureScript.Surface.Syntax.Tree as SST

type SigDefSourceRange =
  { signature ∷ Maybe SourceRange
  , definitions ∷ Array SourceRange
  }

data LetBindingSourceRange
  = LetBindingNameSourceRange SigDefSourceRange
  | LetBindingPatternSourceRange SourceRange
  | LetBindingErrorSourceRange SourceRange

derive instance Eq LetBindingSourceRange

data DeclarationSourceRange
  = DeclarationDataSourceRange SigDefSourceRange
  | DeclarationValueSourceRange SigDefSourceRange
  | DeclarationErrorSourceRange SourceRange

derive instance Eq DeclarationSourceRange

type FieldGroup ∷ (Type → Type → Type) → Row Type
type FieldGroup f =
  ( expr ∷ f SST.Expr SourceRange
  , binder ∷ f SST.Binder SourceRange
  , type ∷ f SST.Type SourceRange
  , doStatement ∷ f SST.DoStatement SourceRange
  , letBinding ∷ f SST.LetBinding LetBindingSourceRange
  , declaration ∷ f SST.Declaration DeclarationSourceRange
  , constructor ∷ f SST.DataConstructor SourceRange
  , newtype ∷ f SST.NewtypeConstructor SourceRange
  , classMethod ∷ f SST.ClassMethod SourceRange
  , typeVarBinding ∷ f SST.TypeVarBinding SourceRange
  )

type ErrorFieldGroup ∷ (Type → Type) → Row Type
type ErrorFieldGroup f =
  ( expr ∷ f SST.Expr
  , binder ∷ f SST.Binder
  , type ∷ f SST.Type
  , doStatement ∷ f SST.DoStatement
  , letBinding ∷ f SST.LetBinding
  , declaration ∷ f SST.Declaration
  )

type MakeSourceRange t s = IdMap t s
type MakeRecoveredError t = IdMap t RecoveredError

newtype SourceRanges = SourceRanges
  { | FieldGroup MakeSourceRange
  }

derive newtype instance Eq SourceRanges

newtype RecoveredErrors = RecoveredErrors
  { | ErrorFieldGroup MakeRecoveredError
  }

derive newtype instance Eq RecoveredErrors
