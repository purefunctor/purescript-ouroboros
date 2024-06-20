module Main where

import Prelude

import Effect (Effect)
import Effect.Console (log)
import PureScript.CST (RecoveredParserResult(..), parseModule)
import PureScript.CST.Traversal (defaultVisitorM, topDownTraversal, traverseModule)
import PureScript.CST.Types (Module)

moduleSource ∷ String
moduleSource =
  """
module Main where

x = f a
"""

onExpr ∷ Module Void → Effect (Module Void)
onExpr = traverseModule $ topDownTraversal $ defaultVisitorM
  { onExpr = \e → do
      log "Hey!"
      pure e
  }

main ∷ Effect Unit
main = case parseModule moduleSource of
  ParseSucceeded m → do
    _ ← onExpr m
    pure unit
  _ →
    log "Failed."
