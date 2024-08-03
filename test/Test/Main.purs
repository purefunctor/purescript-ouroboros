module Test.Main where

import Prelude

import ArgParse.Basic
  ( ArgParser
  , boolean
  , default
  , flag
  , flagHelp
  , fromRecord
  , parseArgs
  , printArgError
  )
import Data.Array as Array
import Data.Either (Either(..))
import Effect (Effect)
import Effect.Aff (launchAff_)
import Effect.Class (liftEffect)
import Effect.Class.Console (error)
import Node.Process as Process
import Test.PureScript.Graph as TestGraph
import Test.PureScript.Query as TestQuery
import Test.PureScript.Scope as TestScope
import Test.PureScript.Surface as TestSurface
import Test.PureScript.Utils as TestUtils
import Test.Snapshot (Options(..), runSnapshotSpec)

optionsParser ∷ ArgParser Options
optionsParser = Options
  <$> fromRecord
    { overwrite: flag [ "--overwrite" ] "Overwrite existing snapshots." # boolean # default false
    }
  <* flagHelp

name ∷ String
name = "purescript-ouroboros-tests"

doc ∷ String
doc = "Test suite for purescript-ouroboros"

main ∷ Effect Unit
main = launchAff_ do
  argv ← liftEffect $ Array.drop 2 <$> Process.argv
  case parseArgs name doc optionsParser argv of
    Left e → do
      error $ printArgError e
      liftEffect $ Process.exit' 1
    Right o →
      runSnapshotSpec o do
        TestQuery.spec
        TestGraph.spec
        TestScope.spec
        TestSurface.spec
        TestUtils.spec
