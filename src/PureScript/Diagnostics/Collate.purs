-- @inline Heterogeneous.Folding.foldlRecordCons arity=4
-- @inline Heterogeneous.Folding.hfoldl arity=3
-- @inline export foldingCollateRecoveredErrors.folding arity=3
module PureScript.Diagnostics.Collate where

import Prelude

import Data.HashMap (HashMap)
import Data.HashMap as HashMap
import Data.Set (Set)
import Data.Set as Set
import Heterogeneous.Folding (class Folding, hfoldl)
import PureScript.CST.Errors (RecoveredError)
import PureScript.CST.Parser.Monad (PositionedError)
import PureScript.Diagnostics.Types (Diagnostic(..), DiagnosticKind(..))
import PureScript.Driver.Files (ParsedFile(..))
import PureScript.Id (Id)
import PureScript.Interface.Collect as InterfaceCollect
import PureScript.Interface.Error (InterfaceError)
import PureScript.Surface.Lower as SurfaceLower
import PureScript.Surface.Lower.Types (RecoveredErrors(..))

ofPositionedError ∷ PositionedError → Diagnostic
ofPositionedError { error } = Diagnostic { kind: DiagnosticParseError error }

ofRecoveredError ∷ RecoveredError → Diagnostic
ofRecoveredError error = Diagnostic { kind: DiagnosticRecoveredError error }

ofInterfaceError ∷ InterfaceError → Diagnostic
ofInterfaceError error = Diagnostic { kind: DiagnosticInterfaceError error }

data CollateRecoveredErrors = CollateRecoveredErrors

instance foldingCollateRecoveredErrors ∷
  Folding CollateRecoveredErrors (Set Diagnostic) (HashMap (Id t) RecoveredError) (Set Diagnostic) where
  folding _ diagnostics =
    HashMap.toArrayBy (const ofRecoveredError)
      >>> Set.fromFoldable
      >>> Set.union diagnostics

collateDiagnostics
  ∷ ParsedFile
  → SurfaceLower.Result
  → InterfaceCollect.Result
  → Set Diagnostic
collateDiagnostics parsedFile surfaceResult interfaceResult = do
  let
    parsedFileDiagnostics ∷ Set Diagnostic
    parsedFileDiagnostics = case parsedFile of
      ParsedTotal _ →
        Set.empty
      ParsedPartial _ errors →
        Set.fromFoldable $ map ofPositionedError errors

    surfaceDiagnostics ∷ Set Diagnostic
    surfaceDiagnostics = do
      case surfaceResult.recoveredErrors of
        RecoveredErrors recoveredErrors → do
          hfoldl CollateRecoveredErrors (Set.empty ∷ Set Diagnostic) recoveredErrors

    interfaceDiagnostics ∷ Set Diagnostic
    interfaceDiagnostics = Set.fromFoldable $ map ofInterfaceError interfaceResult.errors

  Set.unions [ parsedFileDiagnostics, surfaceDiagnostics, interfaceDiagnostics ]
