module PureScript.Scope.Collect where

import Prelude

import Control.Monad.ST.Global (Global)
import Control.Monad.ST.Global as STG
import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Array.ST (STArray)
import Data.Array.ST as STA
import Data.Array.ST.Partial as STAP
import Data.Traversable (for_, traverse_)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Effect.Uncurried (EffectFn1, mkEffectFn1, runEffectFn1)
import Foreign.Object as O
import Foreign.Object.ST (STObject)
import Foreign.Object.ST as STO
import Partial.Unsafe (unsafeCrashWith, unsafePartial)
import PureScript.CST.Types as CST
import PureScript.Scope.Types (ScopeNode(..))
import PureScript.Surface.Types as SST
import Safe.Coerce (coerce)

type State =
  { scope ∷ Ref ScopeNode
  , exprScopeNode ∷ STArray Global ScopeNode
  }

defaultState ∷ Effect State
defaultState = do
  scope ← Ref.new RootScope
  exprScopeNode ← STG.toEffect STA.new
  pure { scope, exprScopeNode }

currentScope ∷ State → Effect ScopeNode
currentScope state = Ref.read state.scope

pushScope ∷ State → ScopeNode → Effect Unit
pushScope state scope = Ref.write scope state.scope

pushExprScopeNode ∷ State → SST.ExprIndex → Effect Unit
pushExprScopeNode state (SST.Index index) = do
  scope ← currentScope state
  unsafePartial $ STG.toEffect $ STAP.poke index scope state.exprScopeNode

withRevertingScope ∷ ∀ a. State → Effect a → Effect a
withRevertingScope state action = do
  previousScope ← currentScope state
  result ← action
  pushScope state previousScope
  pure result

collectDeclaration ∷ State → SST.Declaration → Effect Unit
collectDeclaration state = case _ of
  SST.DeclarationValue _ _ t e → do
    traverse_ (collectType state) t
    traverse_ (collectValueEquation state) e
  SST.DeclarationNotImplemented _ →
    pure unit

collectValueEquation ∷ State → SST.ValueEquation → Effect Unit
collectValueEquation state (SST.ValueEquation { binders, guarded }) = do
  withRevertingScope state do
    collectPushBinders state binders
    collectGuarded state guarded

collectGuarded ∷ State → SST.Guarded → Effect Unit
collectGuarded state = case _ of
  SST.Unconditional w → collectWhere state w
  SST.Guarded g → traverse_ (collectGuardedExpr state) g

collectWhere ∷ State → SST.Where → Effect Unit
collectWhere state (SST.Where expr bindings) = do
  withRevertingScope state do
    collectPushLetBindings state bindings
    collectExpr state expr

collectGuardedExpr ∷ State → SST.GuardedExpr → Effect Unit
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

collectPushPatternGuard ∷ State → SST.PatternGuard → Effect Unit
collectPushPatternGuard state (SST.PatternGuard binder expr) = do
  collectPushBinders state $ Array.fromFoldable binder
  collectExpr state expr

collectExpr ∷ State → SST.Expr → Effect Unit
collectExpr state = runEffectFn1 go
  where
  goRecordUpdate ∷ EffectFn1 SST.RecordUpdate Unit
  goRecordUpdate = mkEffectFn1 case _ of
    SST.RecordUpdateLeaf _ i →
      runEffectFn1 go i
    SST.RecordUpdateBranch _ r →
      traverse_ (runEffectFn1 goRecordUpdate) r

  goAppSpine ∷ EffectFn1 SST.AppSpine Unit
  goAppSpine = mkEffectFn1 case _ of
    SST.AppTerm e → runEffectFn1 go e
    SST.AppType t → collectType state t

  goPushDoStatement ∷ EffectFn1 SST.DoStatement Unit
  goPushDoStatement = mkEffectFn1 case _ of
    SST.DoLet bindings →
      collectPushLetBindings state $ NEA.toArray bindings
    SST.DoDiscard term →
      runEffectFn1 go term
    SST.DoBind binder term → do
      runEffectFn1 go term
      collectPushBinders state [ binder ]
    SST.DoNotImplemented →
      pure unit

  go ∷ EffectFn1 SST.Expr Unit
  go = mkEffectFn1 \e →
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
        traverse_ (runEffectFn1 go) items
      SST.ExprRecord (SST.Annotation { index }) items → do
        pushExprScopeNode state index
        for_ items case _ of
          SST.RecordPun _ → pure unit
          SST.RecordField _ item → runEffectFn1 go item
      SST.ExprParens (SST.Annotation { index }) i → do
        pushExprScopeNode state index
        runEffectFn1 go i
      SST.ExprTyped (SST.Annotation { index }) i t → do
        pushExprScopeNode state index
        runEffectFn1 go i
        collectType state t
      SST.ExprInfix (SST.Annotation { index }) head chain → do
        pushExprScopeNode state index
        runEffectFn1 go head
        for_ chain \(Tuple operator operand) → do
          runEffectFn1 go operator
          runEffectFn1 go operand
      SST.ExprOp (SST.Annotation { index }) head chain → do
        pushExprScopeNode state index
        runEffectFn1 go head
        for_ chain \(Tuple _ operand) → do
          runEffectFn1 go operand
      SST.ExprOpName (SST.Annotation { index }) _ →
        pushExprScopeNode state index
      SST.ExprNegate (SST.Annotation { index }) i → do
        pushExprScopeNode state index
        runEffectFn1 go i
      SST.ExprRecordAccessor (SST.Annotation { index }) i _ → do
        pushExprScopeNode state index
        runEffectFn1 go i
      SST.ExprRecordUpdate (SST.Annotation { index }) i r → do
        pushExprScopeNode state index
        runEffectFn1 go i
        traverse_ (runEffectFn1 goRecordUpdate) r
      SST.ExprApplication (SST.Annotation { index }) f s → do
        pushExprScopeNode state index
        runEffectFn1 go f
        traverse_ (runEffectFn1 goAppSpine) s
      SST.ExprLambda (SST.Annotation { index }) b i → do
        pushExprScopeNode state index
        withRevertingScope state do
          collectPushBinders state $ NEA.toArray b
          runEffectFn1 go i
      SST.ExprIfThenElse (SST.Annotation { index }) c t f → do
        pushExprScopeNode state index
        runEffectFn1 go c
        runEffectFn1 go t
        runEffectFn1 go f
      SST.ExprCase (SST.Annotation { index }) head branches → do
        pushExprScopeNode state index
        traverse_ (runEffectFn1 go) head
        for_ branches \(Tuple binders guarded) → do
          withRevertingScope state do
            collectPushBinders state $ NEA.toArray binders
            collectGuarded state guarded
      SST.ExprLet (SST.Annotation { index }) bindings body → do
        pushExprScopeNode state index
        withRevertingScope state do
          collectPushLetBindings state $ NEA.toArray bindings
          runEffectFn1 go body
      SST.ExprDo (SST.Annotation { index }) statements → do
        pushExprScopeNode state index
        withRevertingScope state do
          traverse_ (runEffectFn1 goPushDoStatement) statements
      SST.ExprAdo (SST.Annotation { index }) statements body → do
        pushExprScopeNode state index
        withRevertingScope state do
          traverse_ (runEffectFn1 goPushDoStatement) statements
          runEffectFn1 go body
      SST.ExprNotImplemented (SST.Annotation { index }) →
        pushExprScopeNode state index

collectBinder ∷ State → STObject Global SST.BinderIndex → SST.Binder → Effect Unit
collectBinder _ perName = runEffectFn1 go
  where
  insert ∷ String → SST.BinderIndex → Effect Unit
  insert k v = void $ STG.toEffect $ STO.poke k v perName

  go ∷ EffectFn1 SST.Binder Unit
  go = mkEffectFn1 \b →
    case b of
      SST.BinderWildcard _ →
        pure unit
      SST.BinderVar (SST.Annotation { index }) (CST.Name { name }) →
        insert (coerce name) index
      SST.BinderNamed (SST.Annotation { index }) (CST.Name { name }) _ →
        insert (coerce name) index
      SST.BinderConstructor _ _ arguments →
        traverse_ (runEffectFn1 go) arguments
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
        traverse_ (runEffectFn1 go) items
      SST.BinderRecord (SST.Annotation { index }) items →
        for_ items case _ of
          SST.RecordPun (CST.Name { name }) →
            insert (coerce name) index
          SST.RecordField _ i →
            runEffectFn1 go i
      SST.BinderParens _ i →
        runEffectFn1 go i
      SST.BinderTyped _ i _ →
        runEffectFn1 go i
      SST.BinderOp _ head chain → do
        runEffectFn1 go head
        for_ chain \(Tuple _ operand) →
          runEffectFn1 go operand
      SST.BinderNotImplemented _ →
        pure unit

collectType ∷ State → SST.Type → Effect Unit
collectType _ _ = pure unit

collectPushBinders ∷ State → Array SST.Binder → Effect Unit
collectPushBinders state binders = do
  inScopeRaw ← STG.toEffect $ STO.new
  for_ binders (collectBinder state inScopeRaw)
  inScope ← STG.toEffect $ O.freezeST inScopeRaw
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

extractNameIndex ∷ STObject Global SST.LetBindingIndex → SST.LetBinding → Effect Unit
extractNameIndex letBoundRaw = case _ of
  SST.LetBindingValue (SST.Annotation { index }) name _ _ →
    void $ STG.toEffect $ STO.poke (coerce name) index letBoundRaw
  _ →
    unsafeCrashWith "invariant violated: expected LetBindingValue"

collectPushLetBindings ∷ State → Array SST.LetBinding → Effect Unit
collectPushLetBindings state letBindings = do
  let
    kindGroups = Array.groupBy groupByKind letBindings

    collectValue :: SST.LetBinding -> Effect Unit
    collectValue = case _ of
      SST.LetBindingValue _ _ t e -> do
        traverse_ (collectType state) t
        traverse_ (collectValueEquation state) e
      _ ->
        unsafeCrashWith "invariant violated: expected LetBindingValue"

    collectPattern :: SST.LetBinding -> Effect Unit
    collectPattern = case _ of
      SST.LetBindingPattern _ b w -> do
        collectWhere state w
        collectPushBinders state [b]
      _ ->
        unsafeCrashWith "invariant violated: expected LetBindingPattern"

  for_ kindGroups \kindGroup →
    case NEA.uncons kindGroup of
      { head: SST.LetBindingValue _ _ _ _ } → do
        letBoundRaw ← STG.toEffect STO.new
        traverse_ (extractNameIndex letBoundRaw) kindGroup
        letBound ← STG.toEffect $ O.freezeST letBoundRaw
        parentScope ← currentScope state
        pushScope state (LetBound parentScope letBound)
        traverse_ collectValue kindGroup
      { head: SST.LetBindingPattern _ _ _ } →
        traverse_ collectPattern kindGroup
      _ →
        pure unit

  pure unit

collectModule ∷ SST.Module → Effect Unit
collectModule (SST.Module { declarations }) = do
  state ← defaultState
  traverse_ (collectDeclaration state) declarations
