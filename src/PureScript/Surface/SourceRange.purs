module PureScript.Surface.SourceRange where

import Prelude

import Data.Maybe (Maybe)
import PureScript.CST.Types as CST

type SigDefSourceRange =
  { signature ∷ Maybe CST.SourceRange
  , definitions ∷ Array CST.SourceRange
  }

data LetBindingSourceRange
  = LetBindingNameSourceRange SigDefSourceRange
  | LetBindingPatternSourceRange CST.SourceRange
  | LetBindingErrorSourceRange CST.SourceRange

derive instance Eq LetBindingSourceRange

data DeclarationSourceRange
  = DeclarationDataSourceRange SigDefSourceRange
  | DeclarationValueSourceRange SigDefSourceRange
  | DeclarationErrorSourceRange CST.SourceRange

derive instance Eq DeclarationSourceRange