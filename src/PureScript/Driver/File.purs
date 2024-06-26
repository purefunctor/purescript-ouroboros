module PureScript.Driver.Files where

import Prelude

import Data.Array.NonEmpty (NonEmptyArray)
import Data.Either (Either(..))
import Data.Set (Set)
import Data.Set as Set
import PureScript.CST (RecoveredParserResult(..))
import PureScript.CST as CST
import PureScript.CST.Parser (Recovered)
import PureScript.CST.Parser.Monad (PositionedError)
import PureScript.CST.Types (ImportDecl(..), Module(..), ModuleHeader(..), ModuleName, Name(..))

data ParsedFile
  = ParsedTotal (Module Void)
  | ParsedPartial (Recovered Module) (NonEmptyArray PositionedError)

parseFile ∷ String → Either PositionedError ParsedFile
parseFile source = do
  case CST.parseModule source of
    ParseSucceeded m →
      Right $ ParsedTotal m
    ParseSucceededWithErrors m e →
      Right $ ParsedPartial m e
    ParseFailed e →
      Left e

parsedModuleName ∷ ParsedFile → ModuleName
parsedModuleName = case _ of
  ParsedTotal m → do
    getModuleName m
  ParsedPartial m _ → do
    getModuleName m
  where
  getModuleName ∷ ∀ a. Module a → ModuleName
  getModuleName (Module { header: ModuleHeader { name: Name { name } } }) = name

parsedImports ∷ ParsedFile → Set ModuleName
parsedImports = case _ of
  ParsedTotal m → do
    Set.fromFoldable $ getImportedNames m
  ParsedPartial m _ → do
    Set.fromFoldable $ getImportedNames m
  where
  getImportedNames ∷ ∀ a. Module a → Array ModuleName
  getImportedNames (Module { header: ModuleHeader { imports } }) = imports <#> case _ of
    ImportDecl { module: Name { name } } → name
