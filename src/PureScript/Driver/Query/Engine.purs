module PureScript.Driver.Query.Engine where

import Prelude

import Control.Monad.ST (Region, ST)
import Control.Monad.ST.Ref (STRef)
import Control.Monad.ST.Ref as STRef
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Newtype (un)
import Data.Set (Set)
import Data.Set as Set
import Data.Traversable (for_)
import Data.Variant (match)
import Partial.Unsafe (unsafeCrashWith)
import Prim.Row as Row
import PureScript.Driver.Files (ParsedFile(..))
import PureScript.Driver.Query.Stable (ModuleNameId, Stable)
import PureScript.Driver.Query.Stable as Stable
import PureScript.Driver.Query.Stats (class HasStats, Stats, addHit, addMiss)
import PureScript.Driver.Query.Stats as Stats
import PureScript.Driver.Query.Storage (InputStorage, QueryStorage, QueryStorages, Storage(..))
import PureScript.Driver.Query.Storage as Storage
import PureScript.Driver.Query.Types (class GetQueryTag, Queries, QueryTag(..), queryTag)
import PureScript.Scope.Collect (ScopeNodes, collectModule)
import PureScript.Surface.Interface (InterfaceWithErrors, collectInterface)
import PureScript.Surface.Lower (ModuleWithSourceRanges)
import PureScript.Surface.Lower as SurfaceLower
import PureScript.Surface.Types (Module)
import PureScript.Utils.Mutable.Array (MutableArray)
import PureScript.Utils.Mutable.Array as MutableArray
import Record as Record
import Type.Prelude (class IsSymbol, Proxy(..))

newtype Engine r = Engine
  { revisionRef ∷ STRef r Int
  , stable ∷ Stable r
  , storage ∷ Storage r
  , stats ∷ Stats r
  , active ∷
      MutableArray r
        { query ∷ QueryTag
        , dependencies ∷ MutableArray r QueryTag
        }
  }

empty ∷ ∀ r. ST r (Engine r)
empty = do
  revisionRef ← STRef.new 0
  stable ← Stable.empty
  storage ← Storage.empty
  stats ← Stats.empty
  active ← MutableArray.empty
  pure $ Engine { revisionRef, stable, storage, stats, active }

pushActive ∷ ∀ r. Engine r → QueryTag → ST r Unit
pushActive (Engine { active }) query = do
  dependencies ← MutableArray.empty
  void $ MutableArray.push { query, dependencies } active

popActive ∷ ∀ r. Engine r → ST r (Array QueryTag)
popActive (Engine { active }) = do
  MutableArray.pop active >>= case _ of
    Just { dependencies } →
      MutableArray.unsafeFreeze dependencies
    Nothing →
      pure []

pushDependency ∷ ∀ r. Engine r → QueryTag → ST r Unit
pushDependency (Engine { active }) dependency = do
  MutableArray.last active >>= case _ of
    Just { dependencies } →
      void $ MutableArray.push dependency dependencies
    Nothing →
      pure unit

class GetInputStorage ∷ Symbol → Type → Type → Region → Constraint
class GetInputStorage name key value region | name → key value where
  inputStorage ∷ Storage region → InputStorage region key value

instance getInputStorageInstance ∷
  ( IsSymbol name
  , Row.Cons name (InputStorage region key value) _tail (QueryStorages region)
  ) ⇒
  GetInputStorage name key value region where
  inputStorage (Storage storage) = Record.get (Proxy ∷ _ name) storage

class GetQueryStorage ∷ Symbol → Type → Type → Region → Constraint
class GetQueryStorage name key value region | name → key value where
  queryStorage ∷ Storage region → QueryStorage region key value

instance getQueryStorageInstance ∷
  ( IsSymbol name
  , Row.Cons name (QueryStorage region key value) _tail (QueryStorages region)
  ) ⇒
  GetQueryStorage name key value region where
  queryStorage (Storage storage) = Record.get (Proxy ∷ _ name) storage

class EngineInputCore ∷ Symbol → Type → Type → Region → Constraint
class EngineInputCore name key value region | name → key value where
  inputGet ∷ Engine region → key → ST region value
  inputSet ∷ Engine region → key → value → ST region Unit

instance engineInputCoreInstance ∷
  ( GetQueryTag name key
  , GetInputStorage name key value region
  , Ord key
  ) ⇒
  EngineInputCore name key value region where

  inputGet engine@(Engine { storage }) key = do
    pushDependency engine $ queryTag @name key
    map ← STRef.read $ inputStorage @name storage
    case Map.lookup key map of
      Just { value } →
        pure value
      Nothing →
        unsafeCrashWith "invariant violated: inputSet not called."

  inputSet (Engine { revisionRef, storage }) key value = do
    let
      mapRef ∷ InputStorage region key value
      mapRef = inputStorage @name storage
    changedRef ← STRef.read revisionRef >>= STRef.new
    void $ STRef.modify (_ + 1) revisionRef
    void $ STRef.modify (Map.insert key { changedRef, value }) mapRef

class EngineQueryCore ∷ Symbol → Type → Type → Region → Constraint
class EngineQueryCore name key value region | name → key value where
  queryGet ∷ Engine region → key → ST region value

instance engineQueryCoreInstance ∷
  ( IsSymbol name
  , GetQueryTag name key
  , GetQueryStorage name key value region
  , GetQueryFn name key value region
  , HasStats name region
  , Ord key
  ) ⇒
  EngineQueryCore name key value region where

  queryGet engine@(Engine { revisionRef, storage, stats }) key = do
    let
      tag ∷ QueryTag
      tag = queryTag @name key

      mapRef ∷ QueryStorage region key value
      mapRef = queryStorage @name storage

      freshValue ∷ ST region value
      freshValue = do
        pushActive engine tag
        value ← queryFn @name engine key
        void $ STRef.modify (_ + 1) revisionRef
        changedRef ← STRef.read revisionRef >>= STRef.new
        verifiedRef ← STRef.read revisionRef >>= STRef.new
        dependencies ← Set.fromFoldable <$> popActive engine
        void $ STRef.modify (Map.insert key { changedRef, verifiedRef, dependencies, value }) mapRef
        pure value

      checkDependencies ∷ Set QueryTag → Int → ST region Boolean
      checkDependencies dependencies verified = do
        isClean ← STRef.new true

        let
          checkInput
            ∷ ∀ @iN iK iV
            . GetInputStorage iN iK iV region
            ⇒ Ord iK
            ⇒ iK
            → ST region Unit
          checkInput k = do
            m ← STRef.read $ inputStorage @iN storage
            case Map.lookup k m of
              Just { changedRef } → do
                changed ← STRef.read changedRef
                void $ STRef.modify (_ && (changed < verified)) isClean
              Nothing →
                pure unit

          checkDependency
            ∷ ∀ @iN iK iV
            . GetQueryStorage iN iK iV region
            ⇒ GetQueryFn iN iK iV region
            ⇒ Ord iK
            ⇒ Eq iV
            ⇒ iK
            → ST region Unit
          checkDependency k = do
            m ← STRef.read $ queryStorage @iN storage
            case Map.lookup k m of
              Just { value: cacheV } → do
                freshV ← queryFn @iN engine k
                unless (freshV == cacheV) do
                  void $ STRef.write false isClean
              Nothing →
                unsafeCrashWith "invariant violated: dependency being checked should have a cache."

        for_ dependencies $ un QueryTag >>> match
          { parsedFile: checkInput @"parsedFile"
          , surfaceFull: checkDependency @"surfaceFull"
          , surface: checkDependency @"surface"
          , interface: checkDependency @"interface"
          , scopeGraph: checkDependency @"scopeGraph"
          }
        STRef.read isClean

    pushDependency engine tag
    map ← STRef.read mapRef
    case Map.lookup key map of
      Just { verifiedRef, dependencies, value } → do
        revision ← STRef.read revisionRef
        verified ← STRef.read verifiedRef
        if verified == revision then do
          addHit @name stats
          pure value
        else do
          isClean ← checkDependencies dependencies verified
          if isClean then do
            void $ STRef.write revision verifiedRef
            addHit @name stats
            pure value
          else do
            addMiss @name stats
            freshValue
      Nothing → do
        addMiss @name stats
        freshValue

type NotQueryFn ∷ Region → Type → Type → Type
type NotQueryFn r a b = Void → b

type QueryFn ∷ Region → Type → Type → Type
type QueryFn r a b = Engine r → a → ST r b

type QueryFns r = Queries (NotQueryFn r) (QueryFn r)

class GetQueryFn ∷ Symbol → Type → Type → Region → Constraint
class GetQueryFn name key value region | name → key value where
  queryFn ∷ QueryFn region key value

instance getQueryFnInstance ∷
  ( IsSymbol name
  , Row.Cons name (QueryFn region key value) _tail (QueryFns region)
  ) ⇒
  GetQueryFn name key value region where
  queryFn = Record.get (Proxy ∷ _ name) (queryFns ∷ { | QueryFns region })

queryFns ∷ ∀ r. { | QueryFns r }
queryFns =
  { parsedFile: absurd
  , surfaceFull: surfaceFullImpl
  , surface: surfaceImpl
  , interface: interfaceImpl
  , scopeGraph: scopeGraphImpl
  }

surfaceFullImpl ∷ ∀ r. QueryFn r ModuleNameId ModuleWithSourceRanges
surfaceFullImpl engine id = do
  parsedFile ← inputGet @"parsedFile" engine id
  case parsedFile of
    ParsedTotal m →
      SurfaceLower.lowerModule m
    ParsedPartial _ _ →
      unsafeCrashWith "TODO: ParsedPartial"

surfaceImpl ∷ ∀ r. QueryFn r ModuleNameId Module
surfaceImpl engine id =
  queryGet @"surfaceFull" engine id <#> _.surface

interfaceImpl ∷ ∀ r. QueryFn r ModuleNameId InterfaceWithErrors
interfaceImpl engine id = do
  surface ← queryGet @"surface" engine id
  collectInterface surface

scopeGraphImpl ∷ ∀ r. QueryFn r ModuleNameId ScopeNodes
scopeGraphImpl engine id = do
  surface ← queryGet @"surface" engine id
  { interface } ← queryGet @"interface" engine id
  collectModule surface interface

-- example ∷ ∀ r. Engine r → ST r Unit
-- example engine = do
--   inputSet @"parsedFile" engine (Id 0) (unsafeCoerce unit)
--   void $ inputGet @"parsedFile" engine (Id 0)
--   queryGet @"interface" engine (Id 0) >>= traceM
--   queryGet @"scopeGraph" engine (Id 0) >>= traceM

--   inputSet @"parsedFile" engine (Id 1) (unsafeCoerce unit)
--   void $ inputGet @"parsedFile" engine (Id 1)
--   queryGet @"interface" engine (Id 1) >>= traceM
--   queryGet @"scopeGraph" engine (Id 1) >>= traceM

--   inputSet @"parsedFile" engine (Id 2) (unsafeCoerce unit)
--   void $ inputGet @"parsedFile" engine (Id 2)
--   queryGet @"interface" engine (Id 2) >>= traceM
--   queryGet @"scopeGraph" engine (Id 2) >>= traceM
