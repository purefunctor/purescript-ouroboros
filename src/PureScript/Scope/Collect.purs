module PureScript.Scope.Collect where

import Prelude

import Control.Monad.ST (ST)
import Control.Monad.ST as ST
import Control.Monad.ST.Ref (STRef)
import Control.Monad.ST.Ref as STRef
import Control.Monad.ST.Uncurried (STFn1, mkSTFn1, runSTFn1)
import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Array.ST (STArray)
import Data.Array.ST as STA
import Data.Array.ST.Partial as STAP
import Data.Traversable (for_, traverse_)
import Data.Tuple (Tuple(..))
import Foreign.Object as O
import Foreign.Object.ST (STObject)
import Foreign.Object.ST as STO
import Foreign.Object.ST.Unsafe as STOU
import Partial.Unsafe (unsafeCrashWith, unsafePartial)
import PureScript.CST.Types as CST
import PureScript.Scope.Types (ScopeNode(..), TopLevelRefs)
import PureScript.Surface.Types as SST
import Safe.Coerce (coerce)

type State r =
  { scope ∷ STRef r ScopeNode
  , exprScopeNode ∷ STArray r ScopeNode
  }

defaultState ∷ ∀ r. ST r (State r)
defaultState = do
  scope ← STRef.new RootScope
  exprScopeNode ← STA.new
  pure { scope, exprScopeNode }

currentScope ∷ ∀ r. State r → ST r ScopeNode
currentScope state = STRef.read state.scope

pushScope ∷ ∀ r. State r → ScopeNode → ST r Unit
pushScope state scope = void $ STRef.write scope state.scope

pushExprScopeNode ∷ ∀ r. State r → SST.ExprIndex → ST r Unit
pushExprScopeNode state (SST.Index index) = do
  scope ← currentScope state
  unsafePartial $ STAP.poke index scope state.exprScopeNode

withRevertingScope ∷ ∀ r a. State r → ST r a → ST r a
withRevertingScope state action = do
  previousScope ← currentScope state
  result ← action
  pushScope state previousScope
  pure result

collectDeclaration ∷ ∀ r. State r → SST.Declaration → ST r Unit
collectDeclaration state = case _ of
  SST.DeclarationValue _ _ t e → do
    traverse_ (collectType state) t
    traverse_ (collectValueEquation state) e
  SST.DeclarationNotImplemented _ →
    pure unit

collectValueEquation ∷ ∀ r. State r → SST.ValueEquation → ST r Unit
collectValueEquation state (SST.ValueEquation { binders, guarded }) = do
  withRevertingScope state do
    collectPushBinders state binders
    collectGuarded state guarded

collectGuarded ∷ ∀ r. State r → SST.Guarded → ST r Unit
collectGuarded state = case _ of
  SST.Unconditional w → collectWhere state w
  SST.Guarded g → traverse_ (collectGuardedExpr state) g

collectWhere ∷ ∀ r. State r → SST.Where → ST r Unit
collectWhere state (SST.Where expr bindings) = do
  withRevertingScope state do
    collectPushLetBindings state bindings
    collectExpr state expr

collectGuardedExpr ∷ ∀ r. State r → SST.GuardedExpr → ST r Unit
collectGuardedExpr state (SST.GuardedExpr guards (SST.Where expr bindings)) = do
  patternGuardScope ← withRevertingScope state do
    traverse_ (collectPushPatternGuard state) guards
    currentScope state
  letBindingScope ← withRevertingScope state do
    collectPushLetBindings state bindings
    currentScope state
  withRevertingScope state do
    pushScope state (JoinScope patternGuardScope letBindingScope)
    collectExpr state expr

collectPushPatternGuard ∷ ∀ r. State r → SST.PatternGuard → ST r Unit
collectPushPatternGuard state (SST.PatternGuard binder expr) = do
  collectPushBinders state $ Array.fromFoldable binder
  collectExpr state expr

collectExpr ∷ ∀ r. State r → SST.Expr → ST r Unit
collectExpr state = runSTFn1 go
  where
  goRecordUpdate ∷ STFn1 SST.RecordUpdate r Unit
  goRecordUpdate = mkSTFn1 case _ of
    SST.RecordUpdateLeaf _ i →
      runSTFn1 go i
    SST.RecordUpdateBranch _ r →
      traverse_ (runSTFn1 goRecordUpdate) r

  goAppSpine ∷ STFn1 SST.AppSpine r Unit
  goAppSpine = mkSTFn1 case _ of
    SST.AppTerm e → runSTFn1 go e
    SST.AppType t → collectType state t

  goPushDoStatement ∷ STFn1 SST.DoStatement r Unit
  goPushDoStatement = mkSTFn1 case _ of
    SST.DoLet bindings →
      collectPushLetBindings state $ NEA.toArray bindings
    SST.DoDiscard term →
      runSTFn1 go term
    SST.DoBind binder term → do
      runSTFn1 go term
      collectPushBinders state [ binder ]
    SST.DoNotImplemented →
      pure unit

  go ∷ STFn1 SST.Expr r Unit
  go = mkSTFn1 \e →
    case e of
      SST.ExprHole (SST.Annotation { index }) _ →
        pushExprScopeNode state index
      SST.ExprSection (SST.Annotation { index }) →
        pushExprScopeNode state index
      SST.ExprIdent (SST.Annotation { index }) _ →
        pushExprScopeNode state index
      SST.ExprConstructor (SST.Annotation { index }) _ →
        pushExprScopeNode state index
      SST.ExprBoolean (SST.Annotation { index }) _ →
        pushExprScopeNode state index
      SST.ExprChar (SST.Annotation { index }) _ →
        pushExprScopeNode state index
      SST.ExprString (SST.Annotation { index }) _ →
        pushExprScopeNode state index
      SST.ExprInt (SST.Annotation { index }) _ →
        pushExprScopeNode state index
      SST.ExprNumber (SST.Annotation { index }) _ →
        pushExprScopeNode state index
      SST.ExprArray (SST.Annotation { index }) items → do
        pushExprScopeNode state index
        traverse_ (runSTFn1 go) items
      SST.ExprRecord (SST.Annotation { index }) items → do
        pushExprScopeNode state index
        for_ items case _ of
          SST.RecordPun _ → pure unit
          SST.RecordField _ item → runSTFn1 go item
      SST.ExprParens (SST.Annotation { index }) i → do
        pushExprScopeNode state index
        runSTFn1 go i
      SST.ExprTyped (SST.Annotation { index }) i t → do
        pushExprScopeNode state index
        runSTFn1 go i
        collectType state t
      SST.ExprInfix (SST.Annotation { index }) head chain → do
        pushExprScopeNode state index
        runSTFn1 go head
        for_ chain \(Tuple operator operand) → do
          runSTFn1 go operator
          runSTFn1 go operand
      SST.ExprOp (SST.Annotation { index }) head chain → do
        pushExprScopeNode state index
        runSTFn1 go head
        for_ chain \(Tuple _ operand) → do
          runSTFn1 go operand
      SST.ExprOpName (SST.Annotation { index }) _ →
        pushExprScopeNode state index
      SST.ExprNegate (SST.Annotation { index }) i → do
        pushExprScopeNode state index
        runSTFn1 go i
      SST.ExprRecordAccessor (SST.Annotation { index }) i _ → do
        pushExprScopeNode state index
        runSTFn1 go i
      SST.ExprRecordUpdate (SST.Annotation { index }) i r → do
        pushExprScopeNode state index
        runSTFn1 go i
        traverse_ (runSTFn1 goRecordUpdate) r
      SST.ExprApplication (SST.Annotation { index }) f s → do
        pushExprScopeNode state index
        runSTFn1 go f
        traverse_ (runSTFn1 goAppSpine) s
      SST.ExprLambda (SST.Annotation { index }) b i → do
        pushExprScopeNode state index
        withRevertingScope state do
          collectPushBinders state $ NEA.toArray b
          runSTFn1 go i
      SST.ExprIfThenElse (SST.Annotation { index }) c t f → do
        pushExprScopeNode state index
        runSTFn1 go c
        runSTFn1 go t
        runSTFn1 go f
      SST.ExprCase (SST.Annotation { index }) head branches → do
        pushExprScopeNode state index
        traverse_ (runSTFn1 go) head
        for_ branches \(Tuple binders guarded) → do
          withRevertingScope state do
            collectPushBinders state $ NEA.toArray binders
            collectGuarded state guarded
      SST.ExprLet (SST.Annotation { index }) bindings body → do
        pushExprScopeNode state index
        withRevertingScope state do
          collectPushLetBindings state $ NEA.toArray bindings
          runSTFn1 go body
      SST.ExprDo (SST.Annotation { index }) statements → do
        pushExprScopeNode state index
        withRevertingScope state do
          traverse_ (runSTFn1 goPushDoStatement) statements
      SST.ExprAdo (SST.Annotation { index }) statements body → do
        pushExprScopeNode state index
        withRevertingScope state do
          traverse_ (runSTFn1 goPushDoStatement) statements
          runSTFn1 go body
      SST.ExprNotImplemented (SST.Annotation { index }) →
        pushExprScopeNode state index

collectBinder ∷ ∀ r. State r → STObject r SST.BinderIndex → SST.Binder → ST r Unit
collectBinder _ perName = runSTFn1 go
  where
  insert ∷ String → SST.BinderIndex → ST r Unit
  insert k v = void $ STO.poke k v perName

  go ∷ STFn1 SST.Binder r Unit
  go = mkSTFn1 \b →
    case b of
      SST.BinderWildcard _ →
        pure unit
      SST.BinderVar (SST.Annotation { index }) name →
        insert (coerce name) index
      SST.BinderNamed (SST.Annotation { index }) name _ →
        insert (coerce name) index
      SST.BinderConstructor _ _ arguments →
        traverse_ (runSTFn1 go) arguments
      SST.BinderBoolean _ _ →
        pure unit
      SST.BinderChar _ _ →
        pure unit
      SST.BinderString _ _ →
        pure unit
      SST.BinderInt _ _ _ →
        pure unit
      SST.BinderNumber _ _ _ →
        pure unit
      SST.BinderArray _ items →
        traverse_ (runSTFn1 go) items
      SST.BinderRecord (SST.Annotation { index }) items →
        for_ items case _ of
          SST.RecordPun name →
            insert (coerce name) index
          SST.RecordField _ i →
            runSTFn1 go i
      SST.BinderParens _ i →
        runSTFn1 go i
      SST.BinderTyped _ i _ →
        runSTFn1 go i
      SST.BinderOp _ head chain → do
        runSTFn1 go head
        for_ chain \(Tuple _ operand) →
          runSTFn1 go operand
      SST.BinderNotImplemented _ →
        pure unit

collectType ∷ ∀ r. State r → SST.Type → ST r Unit
collectType _ _ = pure unit

collectPushBinders ∷ ∀ r. State r → Array SST.Binder → ST r Unit
collectPushBinders state binders = do
  inScopeRaw ← STO.new
  for_ binders (collectBinder state inScopeRaw)
  inScope ← O.freezeST inScopeRaw
  parentScope ← currentScope state
  pushScope state (Binders parentScope inScope)

groupByKind ∷ SST.LetBinding → SST.LetBinding → Boolean
groupByKind = case _, _ of
  SST.LetBindingValue _ _ _ _, SST.LetBindingValue _ _ _ _ →
    true
  SST.LetBindingPattern _ _ _, SST.LetBindingPattern _ _ _ →
    true
  _, _ →
    false

extractNameIndex ∷ ∀ r. STObject r SST.LetBindingIndex → SST.LetBinding → ST r Unit
extractNameIndex letBoundRaw = case _ of
  SST.LetBindingValue (SST.Annotation { index }) name _ _ →
    void $ STO.poke (coerce name) index letBoundRaw
  _ →
    unsafeCrashWith "invariant violated: expected LetBindingValue"

collectPushLetBindings ∷ ∀ r. State r → Array SST.LetBinding → ST r Unit
collectPushLetBindings state letBindings = do
  let
    kindGroups = Array.groupBy groupByKind letBindings

    collectValue ∷ SST.LetBinding → ST r Unit
    collectValue = case _ of
      SST.LetBindingValue _ _ t e → do
        traverse_ (collectType state) t
        traverse_ (collectValueEquation state) e
      _ →
        unsafeCrashWith "invariant violated: expected LetBindingValue"

    collectPattern ∷ SST.LetBinding → ST r Unit
    collectPattern = case _ of
      SST.LetBindingPattern _ b w → do
        collectWhere state w
        collectPushBinders state [ b ]
      _ →
        unsafeCrashWith "invariant violated: expected LetBindingPattern"

  for_ kindGroups \kindGroup →
    case NEA.uncons kindGroup of
      { head: SST.LetBindingValue _ _ _ _ } → do
        letBoundRaw ← STO.new
        traverse_ (extractNameIndex letBoundRaw) kindGroup
        letBound ← O.freezeST letBoundRaw
        parentScope ← currentScope state
        pushScope state (LetBound parentScope letBound)
        traverse_ collectValue kindGroup
      { head: SST.LetBindingPattern _ _ _ } →
        traverse_ collectPattern kindGroup
      _ →
        pure unit

  pure unit

collectTopLevel ∷ Array SST.Declaration → TopLevelRefs
collectTopLevel declarations = ST.run do
  valuesRaw ← STO.new

  for_ declarations case _ of
    SST.DeclarationValue (SST.Annotation { index }) name _ _ →
      void $ STO.poke (coerce name) index valuesRaw
    SST.DeclarationNotImplemented _ →
      pure unit

  values ← STOU.unsafeFreeze valuesRaw
  pure $ { values }

collectModule ∷ ∀ r. SST.Module → ST r Unit
collectModule (SST.Module { declarations }) = do
  state ← defaultState

  let
    topLevel ∷ TopLevelRefs
    topLevel = collectTopLevel declarations

  parentScope ← currentScope state
  pushScope state (TopLevel parentScope topLevel)

  traverse_ (collectDeclaration state) declarations
