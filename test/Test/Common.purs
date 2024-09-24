module Test.Common where

import Prelude

import Control.Monad.ST (ST)
import Data.Either (Either(..))
import Partial.Unsafe (unsafeCrashWith)
import PureScript.Driver.Files (ParsedFile(..), parseFile)
import PureScript.Surface.Lower as SurfaceLower

lowerTotal ∷ ∀ r. String → ST r SurfaceLower.Result
lowerTotal = parseFile >>> case _ of
  Left _ →
    unsafeCrashWith "Oops! Fixture is invalid!"
  Right parsedFile →
    case parsedFile of
      ParsedTotal m →
        SurfaceLower.lowerModule m
      ParsedPartial m _ →
        SurfaceLower.lowerModule m
