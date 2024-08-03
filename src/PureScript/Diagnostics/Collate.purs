module PureScript.Diagnostics.Collate where

import Prelude

import Data.Set (Set)
import Data.Set as Set
import PureScript.CST.Parser.Monad (PositionedError)
import PureScript.Diagnostics.Types (Diagnostic(..), DiagnosticKind(..))
import PureScript.Driver.Files (ParsedFile(..))
import PureScript.Interface.Collect as InterfaceCollect
import PureScript.Interface.Error (InterfaceError)
import PureScript.Surface.Lower as SurfaceLower

collateDiagnostics
  ∷ ParsedFile
  → SurfaceLower.Result
  → InterfaceCollect.Result
  → Set Diagnostic
collateDiagnostics parsedFile _ interfaceResult = do
  let
    ofPositionedError ∷ PositionedError → Diagnostic
    ofPositionedError { error } = Diagnostic { kind: DiagnosticParseError error }

    ofInterfaceError ∷ InterfaceError → Diagnostic
    ofInterfaceError error = Diagnostic { kind: DiagnosticInterfaceError error }

    parsedFileDiagnostics ∷ Set Diagnostic
    parsedFileDiagnostics = case parsedFile of
      ParsedTotal _ →
        Set.empty
      ParsedPartial _ errors →
        Set.fromFoldable $ map ofPositionedError errors

    interfaceDiagnostics ∷ Set Diagnostic
    interfaceDiagnostics = Set.fromFoldable $ map ofInterfaceError interfaceResult.errors

  Set.unions [ parsedFileDiagnostics, interfaceDiagnostics ]
