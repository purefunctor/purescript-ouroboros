module Test.Snapshot where

import Prelude

import Control.Monad.Reader (ReaderT, ask, runReaderT)
import Control.Monad.Trans.Class (lift)
import Data.Either as Either
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff, error, throwError)
import Effect.Aff as Aff
import Effect.Class (liftEffect)
import Node.Encoding (Encoding(..))
import Node.FS.Aff as FSA
import Node.Glob.Basic (expandGlobsCwd)
import Node.Path (FilePath)
import Node.Path as P
import Node.Process as Process
import Test.JsDiff (diffPatch)
import Test.Spec (SpecT, it)
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner (defaultConfig, runSpecT)

newtype Options = Options
  { overwrite ∷ Boolean
  }

defaultOptions ∷ Options
defaultOptions = Options { overwrite: false }

newtype TestName = TestName String

derive newtype instance Semigroup TestName
derive newtype instance Monoid TestName

expectSnapshot ∷ Options → Maybe TestName → FilePath → (String → Aff String) → Aff Unit
expectSnapshot (Options { overwrite }) mTestName inputPath action = do
  let
    basename ∷ FilePath
    basename = P.basenameWithoutExt inputPath ".input"

    outputBase ∷ FilePath
    outputBase = case mTestName of
      Just (TestName testName) →
        basename <> "." <> testName <> ".output"
      Nothing →
        basename <> ".output"

    outputPath ∷ FilePath
    outputPath = P.concat [ P.dirname inputPath, outputBase ]

  inputFile ← FSA.readTextFile UTF8 inputPath
  outputFile ← Either.hush <$> (Aff.attempt $ FSA.readTextFile UTF8 outputPath)
  testOutput ← action inputFile

  case outputFile of
    Just outputFile' → do
      if overwrite then
        FSA.writeTextFile UTF8 outputPath testOutput
      else
        unless (testOutput == outputFile') do
          patchText <- liftEffect $ diffPatch outputFile' testOutput
          throwError $ error $ "Outputs did not match: \n\n" <> patchText
    Nothing → do
      FSA.writeTextFile UTF8 outputPath testOutput

type SnapshotSpec = SpecT Aff Unit (ReaderT Options Aff)

findInputs ∷ FilePath → SnapshotSpec (Set FilePath)
findInputs basePath = lift $ lift $ expandGlobsCwd [ basePath ]

makeSnapshots ∷ Set FilePath → (String → Aff String) → SnapshotSpec Unit
makeSnapshots inputPaths action = do
  options ← ask
  workPath ← liftEffect $ Process.cwd
  for_ inputPaths \inputPath →
    it (P.relative workPath inputPath) do
      expectSnapshot options mempty inputPath action

makeSnapshotsNamed
  ∷ Set FilePath
  → Array (Tuple String (String → Aff String))
  → SnapshotSpec Unit
makeSnapshotsNamed inputPaths actions = do
  options ← ask
  workPath ← liftEffect $ Process.cwd
  for_ inputPaths \inputPath → do
    for_ actions \(Tuple name action) →
      it (name <> ": " <> P.relative workPath inputPath) do
        expectSnapshot options (Just (TestName name)) inputPath action

runSnapshotSpec ∷ Options → SnapshotSpec Unit → Aff Unit
runSnapshotSpec options snapshotSpec = do
  let
    readerLayer = runSpecT defaultConfig [ consoleReporter ] snapshotSpec
    affLayer = runReaderT readerLayer options
  void $ join $ affLayer
