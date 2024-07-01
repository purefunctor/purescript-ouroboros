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
import PureScript.Driver.Files (ParsedFile(..))
import PureScript.Driver.Interner (ModuleNameIndex)
import PureScript.Scope.Collect (ScopeNodes)
import PureScript.Scope.Collect as ScopeCollect
import PureScript.Surface.Lower (ModuleWithSourceRanges)
import PureScript.Surface.Lower as SurfaceLower
import PureScript.Surface.Types (Module)
import PureScript.Utils.Mutable.Array (MutableArray)
import PureScript.Utils.Mutable.Array as MutableArray

data Query
  = OnParsedFile ModuleNameIndex
  | OnSurfaceFull ModuleNameIndex
  | OnSurface ModuleNameIndex
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

newtype Storage r = Storage
  { revisionRef ∷ STRef r Int
  , parsedFileStorage ∷ InputStorage r ModuleNameIndex ParsedFile
  , surfaceLowerFullStorage ∷ QueryStorage r ModuleNameIndex ModuleWithSourceRanges
  , surfaceLowerStorage ∷ QueryStorage r ModuleNameIndex Module
  , scopeGraphStorage ∷ QueryStorage r ModuleNameIndex ScopeNodes
  , activeQuery ∷ MutableArray r { query ∷ Query, dependencies ∷ MutableArray r Query }
  }

emptyStorage ∷ ∀ r. ST r (Storage r)
emptyStorage = do
  revisionRef ← STRef.new 0
  parsedFileStorage ← STRef.new Map.empty
  surfaceLowerFullStorage ← STRef.new Map.empty
  surfaceLowerStorage ← STRef.new Map.empty
  scopeGraphStorage ← STRef.new Map.empty
  activeQuery ← MutableArray.empty
  pure $ Storage
    { revisionRef
    , parsedFileStorage
    , surfaceLowerFullStorage
    , surfaceLowerStorage
    , scopeGraphStorage
    , activeQuery
    }

pushActive ∷ ∀ r. Storage r → Query → ST r Unit
pushActive (Storage { activeQuery }) query = do
  dependencies ← MutableArray.empty
  void $ MutableArray.push { query, dependencies } activeQuery

popActive ∷ ∀ r. Storage r → ST r (Array Query)
popActive (Storage { activeQuery }) = do
  MutableArray.pop activeQuery >>= case _ of
    Just { dependencies } →
      MutableArray.unsafeFreeze dependencies
    Nothing →
      pure []

pushDependency ∷ ∀ r. Storage r → Query → ST r Unit
pushDependency (Storage { activeQuery }) dependency =
  MutableArray.last activeQuery >>= traverse_ \{ dependencies } →
    void $ MutableArray.push dependency dependencies

inputGet
  ∷ ∀ r k v
  . Ord k
  ⇒ (k → Query)
  → (Storage r → InputStorage r k v)
  → Storage r
  → k
  → ST r v
inputGet getQuery getStorage storage key = do
  pushDependency storage $ getQuery key
  map ← STRef.read $ getStorage storage
  case Map.lookup key map of
    Just { value } →
      pure value
    Nothing →
      unsafeCrashWith "impossible."

inputSet
  ∷ ∀ r k v
  . Ord k
  ⇒ (Storage r → InputStorage r k v)
  → Storage r
  → k
  → v
  → ST r Unit
inputSet getStorage storage@(Storage { revisionRef }) key value = do
  let
    mapRef ∷ InputStorage r k v
    mapRef = getStorage storage
  changedRef ← STRef.read revisionRef >>= STRef.new
  void $ STRef.modify (_ + 1) revisionRef
  void $ STRef.modify (Map.insert key { changedRef, value }) mapRef

queryGet
  ∷ ∀ r k v
  . Ord k
  ⇒ (k → Query)
  → (Storage r → QueryStorage r k v)
  → (Storage r → k → ST r v)
  → Storage r
  → k
  → ST r v
queryGet
  getQuery
  getStorage
  getValue
  storage@
    ( Storage
        { revisionRef
        , parsedFileStorage
        , surfaceLowerFullStorage
        , surfaceLowerStorage
        , scopeGraphStorage
        }
    )
  key = do
  let
    query ∷ Query
    query = getQuery key

    mapRef ∷ QueryStorage r k v
    mapRef = getStorage storage

    freshValue ∷ ST r v
    freshValue = do
      pushActive storage query
      value ← getValue storage key
      changedRef ← STRef.read revisionRef >>= STRef.new
      void $ STRef.modify (_ + 1) revisionRef
      verifiedRef ← STRef.read revisionRef >>= STRef.new
      dependencies ← Set.fromFoldable <$> popActive storage
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
          → (Storage r → ik → ST r iv)
          → QueryStorage r ik iv
          → ST r Unit
        checkDependency k getV innerStorage = do
          m ← STRef.read innerStorage
          case Map.lookup k m of
            Just { value: cacheV } → do
              freshV ← getV storage k
              unless (freshV == cacheV) do
                void $ STRef.write false isClean
            Nothing →
              unsafeCrashWith "impossible."

        onQuery ∷ Query → ST r Unit
        onQuery = case _ of
          OnParsedFile k →
            checkInput k parsedFileStorage
          OnSurfaceFull k →
            checkDependency k getSurfaceFull surfaceLowerFullStorage
          OnSurface k →
            checkDependency k getSurface surfaceLowerStorage
          OnScopeGraph k →
            checkDependency k getScopeGraph scopeGraphStorage

      traverse_ onQuery dependencies
      STRef.read isClean

  pushDependency storage query
  map ← STRef.read mapRef
  value ← case Map.lookup key map of
    Just { verifiedRef, dependencies, value } → do
      revision ← STRef.read revisionRef
      verified ← STRef.read verifiedRef
      if verified == revision then do
        pure value
      else do
        isClean ← checkDependencies dependencies verified
        if isClean then do
          void $ STRef.write revision verifiedRef
          pure value
        else do
          freshValue
    Nothing → do
      freshValue

  pure value

getParsedFile ∷ ∀ r. Storage r → ModuleNameIndex → ST r ParsedFile
getParsedFile = inputGet OnParsedFile \(Storage { parsedFileStorage }) → parsedFileStorage

setParsedFile ∷ ∀ r. Storage r → ModuleNameIndex → ParsedFile → ST r Unit
setParsedFile = inputSet \(Storage { parsedFileStorage }) → parsedFileStorage

computeSurfaceFull ∷ ∀ r. Storage r → ModuleNameIndex → ST r ModuleWithSourceRanges
computeSurfaceFull storage moduleNameIndex = do
  parsedFile ← getParsedFile storage moduleNameIndex
  case parsedFile of
    ParsedTotal m → do
      SurfaceLower.lowerModule m
    ParsedPartial _ _ →
      unsafeCrashWith "todo: support partial lowering"

getSurfaceFull ∷ ∀ r. Storage r → ModuleNameIndex → ST r ModuleWithSourceRanges
getSurfaceFull = do
  let
    getStorage ∷ Storage r → QueryStorage r ModuleNameIndex ModuleWithSourceRanges
    getStorage (Storage { surfaceLowerFullStorage }) = surfaceLowerFullStorage
  queryGet OnSurfaceFull getStorage computeSurfaceFull

getSurface ∷ ∀ r. Storage r → ModuleNameIndex → ST r Module
getSurface = do
  let
    getStorage ∷ Storage r → QueryStorage r ModuleNameIndex Module
    getStorage (Storage { surfaceLowerStorage }) = surfaceLowerStorage
  queryGet OnSurface getStorage \storage moduleNameIndex → do
    getSurfaceFull storage moduleNameIndex <#> _.surface

computeScopeGraph ∷ ∀ r. Storage r → ModuleNameIndex → ST r ScopeNodes
computeScopeGraph storage moduleNameIndex = do
  m ← getSurface storage moduleNameIndex
  ScopeCollect.collectModule m

getScopeGraph ∷ ∀ r. Storage r → ModuleNameIndex → ST r ScopeNodes
getScopeGraph = do
  let
    getStorage ∷ Storage r → QueryStorage r ModuleNameIndex ScopeNodes
    getStorage (Storage { scopeGraphStorage }) = scopeGraphStorage
  queryGet OnScopeGraph getStorage computeScopeGraph
