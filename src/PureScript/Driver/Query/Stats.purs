module PureScript.Driver.Query.Stats where

import Prelude

import Control.Monad.ST (Region, ST)
import Control.Monad.ST.Ref (STRef)
import Control.Monad.ST.Ref as STRef
import Data.Symbol (class IsSymbol)
import Prim.Row as Row
import PureScript.Driver.Query.Types (Queries)
import Record as Record
import Type.Proxy (Proxy(..))

type Stat ∷ Region → Type
type Stat r = { hit ∷ STRef r Int, miss ∷ STRef r Int }

emptyStat ∷ ∀ r. ST r (Stat r)
emptyStat = { hit: _, miss: _ } <$> STRef.new 0 <*> STRef.new 0

type NoMakeStat ∷ Region → Type → Type → Type
type NoMakeStat r a b = Unit

type MakeStat ∷ Region → Type → Type → Type
type MakeStat r a b = Stat r

type QueryStats r = Queries (NoMakeStat r) (MakeStat r)

newtype Stats r = Stats { | QueryStats r }

empty ∷ ∀ r. ST r (Stats r)
empty = do
  parsedFile ← pure unit
  surfaceFull ← emptyStat
  surface ← emptyStat
  interface ← emptyStat
  scopeGraph ← emptyStat
  resolution ← emptyStat
  diagnostics ← emptyStat
  pure $ Stats { parsedFile, surfaceFull, surface, interface, scopeGraph, resolution, diagnostics }

class HasStats ∷ Symbol → Region → Constraint
class HasStats name region where
  addHit ∷ Stats region → ST region Unit
  addMiss ∷ Stats region → ST region Unit
  getStat ∷ Stats region → ST region { hit ∷ Int, miss ∷ Int }

instance hasStatsInstance ∷
  ( IsSymbol name
  , Row.Cons name (Stat region) t (QueryStats region)
  ) ⇒
  HasStats name region where

  addHit (Stats queryStats) =
    void $ STRef.modify (_ + 1) (Record.get (Proxy ∷ _ name) queryStats).hit

  addMiss (Stats queryStats) =
    void $ STRef.modify (_ + 1) (Record.get (Proxy ∷ _ name) queryStats).miss

  getStat (Stats queryStats) = do
    let
      stat ∷ Stat region
      stat = Record.get (Proxy ∷ _ name) queryStats
    { hit: _, miss: _ } <$> STRef.read stat.hit <*> STRef.read stat.miss
