module Test.Utils where

import Prelude

import Data.Either (Either(..))
import Partial.Unsafe (unsafeCrashWith)
import PureScript.CST.Types as CST
import PureScript.Driver.Files (ParsedFile(..), parseFile)

parseTotal ∷ String → CST.Module Void
parseTotal source = case parseFile source of
  Left _ →
    unsafeCrashWith "Invalid!"
  Right parsedFile → case parsedFile of
    ParsedTotal m →
      m
    ParsedPartial _ _ →
      unsafeCrashWith "Invalid!"
