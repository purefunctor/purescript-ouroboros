module Test.PureScript.Query where

import Prelude

import Control.Monad.ST (ST)
import Control.Monad.ST.Global (Global, toEffect)
import Control.Monad.ST.Ref as STRef
import Data.Either (Either(..))
import Effect.Class (class MonadEffect, liftEffect)
import Partial.Unsafe (unsafeCrashWith)
import PureScript.Driver.Files (ParsedFile, parseFile)
import PureScript.Driver.Interner (ModuleNameIndex(..))
import PureScript.Driver.Query
  ( HitMiss
  , QueryStats
  , Storage(..)
  , emptyStorage
  , getScopeGraph
  , getSurface
  , getSurfaceFull
  , setParsedFile
  )
import Safe.Coerce (coerce)
import Test.Snapshot (SnapshotSpec)
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldEqual)

parseTotal ∷ String → ParsedFile
parseTotal source = case parseFile source of
  Left _ →
    unsafeCrashWith "Oops!"
  Right parsedFile →
    parsedFile

a1 ∷ ParsedFile
a1 = parseTotal "module A where\na = 0"

a2 ∷ ParsedFile
a2 = parseTotal "module A where\na  =  0"

b1 ∷ ParsedFile
b1 = parseTotal "module B where\nb = 0"

i ∷ ModuleNameIndex
i = coerce 0

j ∷ ModuleNameIndex
j = coerce 1

runQuery ∷ ∀ m a. MonadEffect m ⇒ ST Global a → m a
runQuery = liftEffect <<< toEffect

getHitMiss
  ∷ Storage Global
  → (QueryStats Global → HitMiss Global)
  → ST Global { hit ∷ Int, miss ∷ Int }
getHitMiss (Storage storage) innerStats = do
  case innerStats storage.queryStats of
    { hit, miss } → do
      { hit: _, miss: _ } <$> STRef.read hit <*> STRef.read miss

spec ∷ SnapshotSpec Unit
spec = do
  describe "PureScript.Driver.Query" do
    -- Tests on edits that don't change semantics.
    describe "Non-Semantic Edits" do
      -- Will always miss because of modified SourceRanges
      it "misses on full lowering" do
        hitMiss ← runQuery do
          storage ← emptyStorage
          setParsedFile storage i a1
          void $ getSurfaceFull storage i
          setParsedFile storage i a2
          void $ getSurfaceFull storage i
          getHitMiss storage _.surfaceFull
        hitMiss `shouldEqual` { hit: 0, miss: 2 }
      -- Will always miss because of modified SourceRanges
      it "misses on partial lowering" do
        hitMiss ← runQuery do
          storage ← emptyStorage
          setParsedFile storage i a1
          void $ getSurface storage i
          setParsedFile storage i a2
          void $ getSurface storage i
          getHitMiss storage _.surface
        hitMiss `shouldEqual` { hit: 0, miss: 2 }
      -- Since getSurface hides SourceRanges, we get a
      -- cache hit on getScopeGraph despite the former
      -- having misses.
      it "caches on scope graphs v1" do
        hitMiss ← runQuery do
          storage ← emptyStorage
          setParsedFile storage i a1
          void $ getScopeGraph storage i
          setParsedFile storage i a2
          void $ getScopeGraph storage i
          getHitMiss storage _.scopeGraph
        hitMiss `shouldEqual` { hit: 1, miss: 1 }
      -- Editing a different input should not miss.
      it "caches on scope graphs v2" do
        hitMiss ← runQuery do
          storage ← emptyStorage
          setParsedFile storage i a1
          void $ getScopeGraph storage i
          setParsedFile storage j b1
          void $ getScopeGraph storage i
          getHitMiss storage _.scopeGraph
        hitMiss `shouldEqual` { hit: 1, miss: 1 }
    -- Tests on edits that do change semantics.
    describe "Semantic Edits" do
      -- different module = different scope graph
      it "misses on scope graphs" do
        hitMiss ← runQuery do
          storage ← emptyStorage
          setParsedFile storage i a1
          void $ getScopeGraph storage i
          setParsedFile storage i b1
          void $ getScopeGraph storage i
          getHitMiss storage _.scopeGraph
        hitMiss `shouldEqual` { hit: 0, miss: 2 }
