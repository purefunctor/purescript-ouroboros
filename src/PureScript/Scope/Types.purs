module PureScript.Scope.Types where

import Prelude

import Control.Alt ((<|>))
import Data.Maybe (Maybe(..))
import Foreign.Object (Object)
import Foreign.Object as Object
import PureScript.CST.Types (Ident(..))
import PureScript.Interface.Types (Interface)
import PureScript.Interface.Types as Interface
import PureScript.Surface.Syntax.Tree as SST

data ScopeNode
  = RootScope
  | TopLevel ScopeNode Interface
  | Binders ScopeNode (Object SST.BinderId)
  | LetBound ScopeNode (Object SST.LetBindingId)
  | TypeVar ScopeNode String SST.TypeVarBindingId
  | JoinScope ScopeNode ScopeNode

derive instance Eq ScopeNode

data ExprIdentResolution
  = ExprIdentBinder SST.BinderId
  | ExprIdentLetBound SST.LetBindingId
  | ExprIdentDeclaration SST.DeclarationId
  | ExprIdentClassMethod SST.ClassMethodId

type OnScopeNode r =
  { onTopLevel ∷ Interface → Maybe r
  , onBinders ∷ Object SST.BinderId → Maybe r
  , onLetBound ∷ Object SST.LetBindingId → Maybe r
  , onTypeVar ∷ String → SST.TypeVarBindingId → Maybe r
  }

defaultOnScopeNode ∷ ∀ r. OnScopeNode r
defaultOnScopeNode =
  { onTopLevel: \_ → Nothing
  , onBinders: \_ → Nothing
  , onLetBound: \_ → Nothing
  , onTypeVar: \_ _ → Nothing
  }

resolveCore ∷ ∀ r. OnScopeNode r → ScopeNode → Maybe r
resolveCore k n = go n
  where
  orGo ∷ ScopeNode → Maybe r → Maybe r
  orGo parent = case _ of
    v@(Just _) → v
    Nothing → go parent

  go ∷ ScopeNode → Maybe r
  go = case _ of
    RootScope →
      Nothing
    TopLevel parent interface →
      k.onTopLevel interface # orGo parent
    Binders parent binders →
      k.onBinders binders # orGo parent
    LetBound parent letBound →
      k.onLetBound letBound # orGo parent
    TypeVar parent varName varId →
      k.onTypeVar varName varId # orGo parent
    JoinScope leftParent rightParent →
      Nothing # orGo leftParent # orGo rightParent

resolveExprIdent ∷ Ident → ScopeNode → Maybe ExprIdentResolution
resolveExprIdent (Ident i) = do
  let
    -- TODO: GENERATE AN ERROR HERE!!!
    -- Q: but wouldn't it make sense to generate these
    -- during interface collection? Then we could just
    -- guarantee that everything under interface must
    -- be unique.
    -- A: True, and it also currently doesn't! So that's
    -- definitely the better idea here--add more errors
    -- during interface collection, and then we can just
    -- trust that everything is unique here.
    onTopLevel ∷ Interface → Maybe ExprIdentResolution
    onTopLevel interface =
      (Interface.lookupValue i interface <#> ExprIdentDeclaration)
        <|> (Interface.lookupClassMethod i interface <#> ExprIdentClassMethod)

  resolveCore $ defaultOnScopeNode
    { onTopLevel = onTopLevel
    , onBinders = Object.lookup i >=> ExprIdentBinder >>> Just
    , onLetBound = Object.lookup i >=> ExprIdentLetBound >>> Just
    }
