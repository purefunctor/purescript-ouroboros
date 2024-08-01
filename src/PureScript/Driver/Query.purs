-- | Implements the incremental computation core for the compiler.
-- |
-- | Based on Niko Matsakis' notes on Salsa:
-- |
-- | https://gist.github.com/nikomatsakis/5b119a71465549b61743e8739a369b5e
-- |
-- | # Architecture
-- |
-- | At a high level, the query engine:
-- | * consumes inputs from an external provider
-- | * orchestrates computations operating on said inputs
-- | * keeps track of when things should be recomputed
-- |
-- | More concretely, the query engine:
-- | * consumes parsed files as inputs from the driver
-- | * orchestrates compiler procedures such as lowering
-- | * keeps track of which procedures need to be redone
-- |
-- | The query engine uses revisions as the primary mechanism for tracking
-- | when to recompute compiler operations. It keeps track of the current
-- | revision using an integer, which is incremented when inputs are changed
-- | or when new values are produced from operations. This revision is then
-- | attached to cache entries, providing a marker for "when" an input was
-- | changed or "when" an operation was last recomputed.
-- |
-- | The query engine also automatically keeps track of dependencies between
-- | computations, the idea being that if a computation's dependencies remain
-- | unchanged, then there's no need to run the dependent computation. To
-- | accommodate for this functionality, the engine also keeps track of when
-- | computations were last "verified".
-- |
-- | The dependency checking algorithm goes as follows: for each dependency:
-- | * if the dependency is an input: if it were changed more recently than
-- |   the dependent was verified, then recomputation is required.
-- | * if the dependency is a query: if its computation returns a value
-- |   not equal to the cached value, then recomputation is required.
module PureScript.Driver.Query where

import Prelude

import Control.Monad.ST (ST)
import Control.Monad.ST.Ref (STRef)
import Control.Monad.ST.Ref as STRef
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Traversable (traverse_)
import Partial.Unsafe (unsafeCrashWith)
import PureScript.CST.Types (ModuleName)
import PureScript.Driver.Files (ParsedFile(..))
import PureScript.Driver.Interner (ModuleNameIndex, ModuleNameInterner)
import PureScript.Driver.Interner as ModuleNameInterner
import PureScript.Scope.Collect (ScopeNodes)
import PureScript.Scope.Collect as ScopeCollect
import PureScript.Surface.Interface (InterfaceWithErrors)
import PureScript.Surface.Interface as SurfaceInterface
import PureScript.Surface.Lower (ModuleWithSourceRanges)
import PureScript.Surface.Lower as SurfaceLower
import PureScript.Surface.Types (Module)
import PureScript.Utils.Mutable.Array (MutableArray)
import PureScript.Utils.Mutable.Array as MutableArray

data Query
  = OnParsedFile ModuleNameIndex
  | OnSurfaceFull ModuleNameIndex
  | OnSurface ModuleNameIndex
  | OnInterface ModuleNameIndex
  | OnScopeGraph ModuleNameIndex

derive instance Eq Query
derive instance Ord Query

type InputStorage r k v =
  STRef r
    ( Map k
        { changedRef ∷ STRef r Int
        , value ∷ v
        }
    )

type QueryStorage r k v =
  STRef r
    ( Map k
        { changedRef ∷ STRef r Int
        , verifiedRef ∷ STRef r Int
        , dependencies ∷ Set Query
        , value ∷ v
        }
    )

type HitMiss r = { hit ∷ STRef r Int, miss ∷ STRef r Int }

emptyHitMiss ∷ ∀ r. ST r (HitMiss r)
emptyHitMiss = { hit: _, miss: _ } <$> STRef.new 0 <*> STRef.new 0

type QueryStats r =
  { surfaceFull ∷ HitMiss r
  , surface ∷ HitMiss r
  , interface ∷ HitMiss r
  , scopeGraph ∷ HitMiss r
  }

emptyQueryStats ∷ ∀ r. ST r (QueryStats r)
emptyQueryStats = { surfaceFull: _, surface: _, interface: _, scopeGraph: _ }
  <$> emptyHitMiss
  <*> emptyHitMiss
  <*> emptyHitMiss
  <*> emptyHitMiss

newtype QueryEngine r = QueryEngine
  { revisionRef ∷ STRef r Int
  , moduleNameInterner ∷ ModuleNameInterner r
  , parsedFileStorage ∷ InputStorage r ModuleNameIndex ParsedFile
  , surfaceFullStorage ∷ QueryStorage r ModuleNameIndex ModuleWithSourceRanges
  , surfaceStorage ∷ QueryStorage r ModuleNameIndex Module
  , interfaceStorage ∷ QueryStorage r ModuleNameIndex InterfaceWithErrors
  , scopeGraphStorage ∷ QueryStorage r ModuleNameIndex ScopeNodes
  , activeQuery ∷ MutableArray r { query ∷ Query, dependencies ∷ MutableArray r Query }
  , queryStats ∷ QueryStats r
  }

emptyQueryEngine ∷ ∀ r. ST r (QueryEngine r)
emptyQueryEngine = do
  revisionRef ← STRef.new 0
  moduleNameInterner ← ModuleNameInterner.emptyInterner
  parsedFileStorage ← STRef.new Map.empty
  surfaceFullStorage ← STRef.new Map.empty
  surfaceStorage ← STRef.new Map.empty
  interfaceStorage ← STRef.new Map.empty
  scopeGraphStorage ← STRef.new Map.empty
  activeQuery ← MutableArray.empty
  queryStats ← emptyQueryStats
  pure $ QueryEngine
    { revisionRef
    , moduleNameInterner
    , parsedFileStorage
    , surfaceFullStorage
    , interfaceStorage
    , surfaceStorage
    , scopeGraphStorage
    , activeQuery
    , queryStats
    }

pushActive ∷ ∀ r. QueryEngine r → Query → ST r Unit
pushActive (QueryEngine { activeQuery }) query = do
  dependencies ← MutableArray.empty
  void $ MutableArray.push { query, dependencies } activeQuery

popActive ∷ ∀ r. QueryEngine r → ST r (Array Query)
popActive (QueryEngine { activeQuery }) = do
  MutableArray.pop activeQuery >>= case _ of
    Just { dependencies } →
      MutableArray.unsafeFreeze dependencies
    Nothing →
      pure []

pushDependency ∷ ∀ r. QueryEngine r → Query → ST r Unit
pushDependency (QueryEngine { activeQuery }) dependency =
  MutableArray.last activeQuery >>= traverse_ \{ dependencies } →
    void $ MutableArray.push dependency dependencies

inputGet
  ∷ ∀ r k v
  . Ord k
  ⇒ (k → Query)
  → (QueryEngine r → InputStorage r k v)
  → QueryEngine r
  → k
  → ST r v
inputGet getQuery getStorage storage key = do
  pushDependency storage $ getQuery key
  map ← STRef.read $ getStorage storage
  case Map.lookup key map of
    Just { value } →
      pure value
    Nothing →
      unsafeCrashWith "invariant violated: value is not in storage"

inputSet
  ∷ ∀ r k v
  . Ord k
  ⇒ (QueryEngine r → InputStorage r k v)
  → QueryEngine r
  → k
  → v
  → ST r Unit
inputSet getStorage engine@(QueryEngine { revisionRef }) key value = do
  let
    mapRef ∷ InputStorage r k v
    mapRef = getStorage engine
  changedRef ← STRef.read revisionRef >>= STRef.new
  void $ STRef.modify (_ + 1) revisionRef
  void $ STRef.modify (Map.insert key { changedRef, value }) mapRef

queryGet
  ∷ ∀ r k v
  . Ord k
  ⇒ (k → Query)
  → (QueryEngine r → QueryStorage r k v)
  → (QueryEngine r → k → ST r v)
  → QueryEngine r
  → k
  → ST r v
queryGet
  getQuery
  getStorage
  getValue
  engine@
    ( QueryEngine
        { revisionRef
        , parsedFileStorage
        , surfaceFullStorage
        , surfaceStorage
        , interfaceStorage
        , scopeGraphStorage
        , queryStats
        }
    )
  key = do
  let
    query ∷ Query
    query = getQuery key

    addHitOrMiss ∷ Boolean → ST r Unit
    addHitOrMiss isHit = do
      let
        hitMiss ∷ Maybe (HitMiss r)
        hitMiss = case query of
          OnParsedFile _ →
            Nothing
          OnSurfaceFull _ →
            Just queryStats.surfaceFull
          OnSurface _ →
            Just queryStats.surface
          OnInterface _ →
            Just queryStats.interface
          OnScopeGraph _ →
            Just queryStats.scopeGraph
      case hitMiss of
        Just { hit, miss } →
          void $
            if isHit then
              STRef.modify (_ + 1) hit
            else
              STRef.modify (_ + 1) miss
        _ →
          pure unit

    mapRef ∷ QueryStorage r k v
    mapRef = getStorage engine

    freshValue ∷ ST r v
    freshValue = do
      pushActive engine query
      value ← getValue engine key
      void $ STRef.modify (_ + 1) revisionRef
      changedRef ← STRef.read revisionRef >>= STRef.new
      verifiedRef ← STRef.read revisionRef >>= STRef.new
      dependencies ← Set.fromFoldable <$> popActive engine
      void $ STRef.modify (Map.insert key { changedRef, verifiedRef, dependencies, value }) mapRef
      pure value

    checkDependencies ∷ Set Query → Int → ST r Boolean
    checkDependencies dependencies verified = do
      isClean ← STRef.new true
      let
        checkInput
          ∷ ∀ ik iv
          . Ord ik
          ⇒ ik
          → InputStorage r ik iv
          → ST r Unit
        checkInput k inputStorage = do
          m ← STRef.read inputStorage
          case Map.lookup k m of
            Just { changedRef } → do
              changed ← STRef.read changedRef
              void $ STRef.modify (_ && (changed < verified)) isClean
            Nothing →
              pure unit

        checkDependency
          ∷ ∀ ik iv
          . Ord ik
          ⇒ Eq iv
          ⇒ ik
          → (QueryEngine r → ik → ST r iv)
          → QueryStorage r ik iv
          → ST r Unit
        checkDependency k getV innerStorage = do
          m ← STRef.read innerStorage
          case Map.lookup k m of
            Just { value: cacheV } → do
              freshV ← getV engine k
              unless (freshV == cacheV) do
                void $ STRef.write false isClean
            Nothing →
              unsafeCrashWith "impossible."

        onQuery ∷ Query → ST r Unit
        onQuery = case _ of
          OnParsedFile k →
            checkInput k parsedFileStorage
          OnSurfaceFull k →
            checkDependency k getSurfaceFull surfaceFullStorage
          OnSurface k →
            checkDependency k getSurface surfaceStorage
          OnInterface k →
            checkDependency k getInterface interfaceStorage
          OnScopeGraph k →
            checkDependency k getScopeGraph scopeGraphStorage

      traverse_ onQuery dependencies
      STRef.read isClean

  pushDependency engine query
  map ← STRef.read mapRef
  value ← case Map.lookup key map of
    Just { verifiedRef, dependencies, value } → do
      revision ← STRef.read revisionRef
      verified ← STRef.read verifiedRef
      if verified == revision then do
        addHitOrMiss true
        pure value
      else do
        isClean ← checkDependencies dependencies verified
        if isClean then do
          void $ STRef.write revision verifiedRef
          addHitOrMiss true
          pure value
        else do
          addHitOrMiss false
          freshValue
    Nothing → do
      addHitOrMiss false
      freshValue

  pure value

-- The presence of a module name in the interner does not necessarily imply
-- the presence of a parsed source file. This utility is useful for queries
-- that need to obtain information from source files that may not exist yet.
--
-- Rather than designing queries to return `Maybe` if the source file does
-- not exist, we simply do not call them at all if they're not available.
lookupModuleIndex ∷ ∀ r. QueryEngine r → ModuleName → ST r (Maybe ModuleNameIndex)
lookupModuleIndex (QueryEngine { moduleNameInterner, parsedFileStorage }) name = do
  index ← ModuleNameInterner.internModuleName moduleNameInterner name
  STRef.read parsedFileStorage <#> Map.member index >>> if _ then Just index else Nothing

getParsedFile ∷ ∀ r. QueryEngine r → ModuleNameIndex → ST r ParsedFile
getParsedFile = inputGet OnParsedFile \(QueryEngine { parsedFileStorage }) → parsedFileStorage

setParsedFile ∷ ∀ r. QueryEngine r → ModuleNameIndex → ParsedFile → ST r Unit
setParsedFile = inputSet \(QueryEngine { parsedFileStorage }) → parsedFileStorage

computeSurfaceFull ∷ ∀ r. QueryEngine r → ModuleNameIndex → ST r ModuleWithSourceRanges
computeSurfaceFull storage moduleNameIndex = do
  parsedFile ← getParsedFile storage moduleNameIndex
  case parsedFile of
    ParsedTotal m → do
      SurfaceLower.lowerModule m
    ParsedPartial _ _ →
      unsafeCrashWith "todo: support partial lowering"

getSurfaceFull ∷ ∀ r. QueryEngine r → ModuleNameIndex → ST r ModuleWithSourceRanges
getSurfaceFull = do
  let
    getStorage ∷ QueryEngine r → QueryStorage r ModuleNameIndex ModuleWithSourceRanges
    getStorage (QueryEngine { surfaceFullStorage }) = surfaceFullStorage
  queryGet OnSurfaceFull getStorage computeSurfaceFull

getSurface ∷ ∀ r. QueryEngine r → ModuleNameIndex → ST r Module
getSurface = do
  let
    getStorage ∷ QueryEngine r → QueryStorage r ModuleNameIndex Module
    getStorage (QueryEngine { surfaceStorage }) = surfaceStorage
  queryGet OnSurface getStorage \storage moduleNameIndex → do
    getSurfaceFull storage moduleNameIndex <#> _.surface

computeInterface ∷ ∀ r. QueryEngine r → ModuleNameIndex → ST r InterfaceWithErrors
computeInterface storage moduleNameIndex = do
  m ← getSurface storage moduleNameIndex
  SurfaceInterface.collectInterface m

getInterface ∷ ∀ r. QueryEngine r → ModuleNameIndex → ST r InterfaceWithErrors
getInterface = do
  let
    getStorage ∷ QueryEngine r → QueryStorage r ModuleNameIndex InterfaceWithErrors
    getStorage (QueryEngine { interfaceStorage }) = interfaceStorage
  queryGet OnInterface getStorage computeInterface

computeScopeGraph ∷ ∀ r. QueryEngine r → ModuleNameIndex → ST r ScopeNodes
computeScopeGraph storage moduleNameIndex = do
  surface ← getSurface storage moduleNameIndex
  { interface } ← getInterface storage moduleNameIndex
  ScopeCollect.collectModule surface interface

getScopeGraph ∷ ∀ r. QueryEngine r → ModuleNameIndex → ST r ScopeNodes
getScopeGraph = do
  let
    getStorage ∷ QueryEngine r → QueryStorage r ModuleNameIndex ScopeNodes
    getStorage (QueryEngine { scopeGraphStorage }) = scopeGraphStorage
  queryGet OnScopeGraph getStorage computeScopeGraph
