module PureScript.Driver.Query.Types where

import Prelude

import Data.Newtype (class Newtype)
import Data.Symbol (class IsSymbol)
import Data.Variant (Variant, inj)
import Prim.Row as Row
import PureScript.Driver.Files (ParsedFile)
import PureScript.Driver.Query.Stable (FileId)
import PureScript.Scope.Collect (ScopeNodes)
import PureScript.Surface.Interface (InterfaceWithErrors)
import PureScript.Surface.Lower (ModuleWithSourceRanges)
import PureScript.Surface.Types (Module)
import Type.Proxy (Proxy(..))

type Queries ∷ ∀ k. (Type → Type → k) → (Type → Type → k) → Row k
type Queries onInput onQuery =
  ( parsedFile ∷ onInput FileId ParsedFile
  , surfaceFull ∷ onQuery FileId ModuleWithSourceRanges
  , surface ∷ onQuery FileId Module
  , interface ∷ onQuery FileId InterfaceWithErrors
  , scopeGraph ∷ onQuery FileId ScopeNodes
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
