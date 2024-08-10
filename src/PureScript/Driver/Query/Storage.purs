module PureScript.Driver.Query.Storage where

import Prelude

import Control.Monad.ST (ST)
import Control.Monad.ST.Ref (STRef)
import Control.Monad.ST.Ref as STRef
import Data.Map (Map)
import Data.Map as Map
import Data.Set (Set)
import PureScript.Driver.Query.Types (Queries, QueryTag)

type MakeStorage r k f = STRef r (Map k { | f })

type InputStorage r k v = MakeStorage r k
  ( changedRef ∷ STRef r Int
  , value ∷ v
  )

type QueryStorage r k v = MakeStorage r k
  ( changedRef ∷ STRef r Int
  , verifiedRef ∷ STRef r Int
  , dependencies ∷ Set QueryTag
  , value ∷ v
  )

type QueryStorages r = Queries (InputStorage r) (QueryStorage r)

newtype Storage r = Storage { | QueryStorages r }

empty ∷ ∀ r. ST r (Storage r)
empty = do
  parsedFile ← STRef.new Map.empty
  surfaceFull ← STRef.new Map.empty
  surface ← STRef.new Map.empty
  interface ← STRef.new Map.empty
  scopeGraph ← STRef.new Map.empty
  resolution ← STRef.new Map.empty
  diagnostics ← STRef.new Map.empty
  pure $ Storage
    { parsedFile, surfaceFull, surface, interface, scopeGraph, resolution, diagnostics }
