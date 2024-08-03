module PureScript.Driver.Query.Types where

import Prelude

import Data.Newtype (class Newtype)
import Data.Set (Set)
import Data.Symbol (class IsSymbol)
import Data.Variant (Variant, inj)
import Prim.Row as Row
import PureScript.Diagnostic.Types (Diagnostic)
import PureScript.Driver.Files (ParsedFile)
import PureScript.Driver.Query.Stable (FileId)
import PureScript.Interface.Collect as InterfaceCollect
import PureScript.Scope.Collect as ScopeCollect
import PureScript.Surface.Lower as SurfaceLower
import PureScript.Surface.Types (Module)
import Type.Proxy (Proxy(..))

type Queries ∷ ∀ k. (Type → Type → k) → (Type → Type → k) → Row k
type Queries onInput onQuery =
  ( parsedFile ∷ onInput FileId ParsedFile
  , surfaceFull ∷ onQuery FileId SurfaceLower.Result
  , surface ∷ onQuery FileId Module
  , interface ∷ onQuery FileId InterfaceCollect.Result
  , scopeGraph ∷ onQuery FileId ScopeCollect.Result
  , diagnostics ∷ onQuery FileId (Set Diagnostic)
  )

type Key ∷ Type → Type → Type
type Key a b = a

type QueryKeys = Queries Key Key

newtype QueryTag = QueryTag (Variant QueryKeys)

derive instance Newtype QueryTag _
derive newtype instance Eq QueryTag
derive newtype instance Ord QueryTag

class GetQueryTag ∷ Symbol → Type → Constraint
class GetQueryTag name key | name → key where
  queryTag ∷ key → QueryTag

instance getQueryTagInstance ∷
  ( IsSymbol name
  , Row.Cons name key _tail QueryKeys
  ) ⇒
  GetQueryTag name key where
  queryTag = QueryTag <<< inj (Proxy ∷ _ name)
