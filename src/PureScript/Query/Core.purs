module PureScript.Query.Core where

import Prelude

import Control.Monad.ST (ST)
import Control.Monad.ST.Global (toEffect)
import Control.Monad.ST.Ref (STRef)
import Control.Monad.ST.Ref as STRef
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.String as String
import Data.Traversable (traverse_)
import Effect (Effect)
import Partial.Unsafe (unsafeCrashWith)
import PureScript.Debug (traceM)
import PureScript.Utils.Mutable.Array (MutableArray)
import PureScript.Utils.Mutable.Array as MutableArray

newtype RootKey = RootKey { name ∷ String }

derive newtype instance Eq RootKey
derive newtype instance Ord RootKey

newtype OneKey = OneKey { name ∷ String }

derive newtype instance Eq OneKey
derive newtype instance Ord OneKey

newtype ManyKey = ManyKey {}

derive newtype instance Eq ManyKey
derive newtype instance Ord ManyKey

data Query
  = OnRoot RootKey
  | OnOne OneKey
  | OnMany ManyKey

derive instance Eq Query
derive instance Ord Query

type InputValue r v =
  { changedRef ∷ STRef r Int
  , value ∷ v
  }

type QueryValue r v =
  { changedRef ∷ STRef r Int
  , verifiedRef ∷ STRef r Int
  , dependencies ∷ Set Query
  , value ∷ v
  }

newtype Storage r = Storage
  { revisionRef ∷ STRef r Int
  , rootStorage ∷ STRef r (Map RootKey (InputValue r String))
  , oneStorage ∷ STRef r (Map OneKey (QueryValue r String))
  , manyStorage ∷ STRef r (Map ManyKey (QueryValue r String))
  , activeQuery ∷ MutableArray r { query ∷ Query, dependencies ∷ MutableArray r Query }
  }

emptyStorage ∷ ∀ r. ST r (Storage r)
emptyStorage = do
  revisionRef ← STRef.new 0
  rootStorage ← STRef.new Map.empty
  oneStorage ← STRef.new Map.empty
  manyStorage ← STRef.new Map.empty
  activeQuery ← MutableArray.empty
  pure $ Storage
    { revisionRef
    , rootStorage
    , oneStorage
    , manyStorage
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
  → (Storage r → STRef r (Map k (InputValue r v)))
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
  ⇒ (Storage r → STRef r (Map k (InputValue r v)))
  → Storage r
  → k
  → v
  → ST r Unit
inputSet getStorage storage@(Storage { revisionRef }) key value = do
  let
    mapRef ∷ STRef r (Map k (InputValue r v))
    mapRef = getStorage storage
  changedRef ← STRef.read revisionRef >>= STRef.new
  void $ STRef.modify (_ + 1) revisionRef
  void $ STRef.modify (Map.insert key { changedRef, value }) mapRef

queryGet
  ∷ ∀ r k v
  . Ord k
  ⇒ (k → Query)
  → (Storage r → STRef r (Map k (QueryValue r v)))
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
        , rootStorage
        , oneStorage
        , manyStorage
        }
    )
  key = do
  let
    query ∷ Query
    query = getQuery key

    mapRef ∷ STRef r (Map k (QueryValue r v))
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
          → STRef r (Map ik (InputValue r iv))
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
          → STRef r (Map ik (QueryValue r iv))
          → ST r Unit
        checkDependency k getV innerStorage = do
          m ← STRef.read innerStorage
          case Map.lookup k m of
            Just { dependencies: innerDependencies, changedRef, value: cacheV } → do
              freshV ← getV storage k
              unless (freshV == cacheV) do
                changed ← STRef.read changedRef
                void $ STRef.modify (_ && (changed < verified)) isClean
                traverse_ onQuery innerDependencies
            Nothing →
              unsafeCrashWith "impossible."

        onQuery ∷ Query → ST r Unit
        onQuery = case _ of
          OnRoot k →
            checkInput k rootStorage
          OnOne k → do
            checkDependency k getOne oneStorage
          OnMany k → do
            checkDependency k getMany manyStorage

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
    Nothing →
      freshValue

  pure value

getRoot ∷ ∀ r. Storage r → RootKey → ST r String
getRoot = inputGet OnRoot \(Storage storage) → storage.rootStorage

setRoot ∷ ∀ r. Storage r → RootKey → String → ST r Unit
setRoot = inputSet \(Storage storage) → storage.rootStorage

computeOne ∷ ∀ r. Storage r → OneKey → ST r String
computeOne storage (OneKey { name }) = do
  traceM { fn: "computeOne" }
  String.toUpper <$> getRoot storage (RootKey { name })

getOne ∷ ∀ r. Storage r → OneKey → ST r String
getOne = do
  let
    getStorage ∷ Storage r → _
    getStorage (Storage { oneStorage }) = oneStorage
  queryGet OnOne getStorage computeOne

computeMany ∷ ∀ r. Storage r → ManyKey → ST r String
computeMany storage (ManyKey {}) = do
  traceM { fn: "computeMany" }
  a ← getOne storage (OneKey { name: "A.purs" })
  b ← getOne storage (OneKey { name: "B.purs" })
  pure $ a <> " " <> b

getMany ∷ ∀ r. Storage r → ManyKey → ST r String
getMany = do
  let
    getStorage ∷ Storage r → _
    getStorage (Storage { manyStorage }) = manyStorage
  queryGet OnMany getStorage computeMany

example ∷ Effect Unit
example = toEffect do
  storage ← emptyStorage

  setRoot storage (RootKey { name: "A.purs" }) "Hello"
  setRoot storage (RootKey { name: "B.purs" }) "World"
  getMany storage (ManyKey {}) >>= traceM

  setRoot storage (RootKey { name: "A.purs" }) "hello"
  setRoot storage (RootKey { name: "B.purs" }) "world"
  getMany storage (ManyKey {}) >>= traceM

  pure unit
