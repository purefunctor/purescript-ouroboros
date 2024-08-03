module PureScript.Scope.Collect where

import Prelude

import Control.Monad.ST (ST)
import Control.Monad.ST.Ref (STRef)
import Control.Monad.ST.Ref as STRef
import Control.Monad.ST.Uncurried (STFn1, mkSTFn1, runSTFn1)
import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Traversable (class Traversable, for_, traverse_)
import Data.Tuple (Tuple(..))
import Data.Tuple as Tuple
import Foreign.Object as O
import Foreign.Object.ST (STObject)
import Foreign.Object.ST as STO
import Partial.Unsafe (unsafeCrashWith)
import PureScript.CST.Types as CST
import PureScript.Id (Id(..), IdMap(..))
import PureScript.Interface.Types as IFT
import PureScript.Scope.Types (ScopeNode(..))
import PureScript.Surface.Syntax.Tree as SST
import PureScript.Utils.Mutable.STIntMap (STIntMap)
import PureScript.Utils.Mutable.STIntMap as STIntMap
import Safe.Coerce (coerce)

type State r =
  { scope ∷ STRef r ScopeNode
  , exprScopeNode ∷ STIntMap r ScopeNode
  , binderScopeNode ∷ STIntMap r ScopeNode
  , typeScopeNode ∷ STIntMap r ScopeNode
  }

type Result =
  { exprScopeNode ∷ IdMap SST.Expr ScopeNode
  , binderScopeNode ∷ IdMap SST.Binder ScopeNode
  , typeScopeNode ∷ IdMap SST.Type ScopeNode
  }

defaultState ∷ ∀ r. ST r (State r)
defaultState = do
  scope ← STRef.new RootScope
  exprScopeNode ← STIntMap.empty
  binderScopeNode ← STIntMap.empty
  typeScopeNode ← STIntMap.empty
  pure { scope, exprScopeNode, binderScopeNode, typeScopeNode }

freezeState ∷ ∀ r. State r → ST r Result
freezeState state = do
  exprScopeNode ← STIntMap.freeze state.exprScopeNode
  binderScopeNode ← STIntMap.freeze state.binderScopeNode
  typeScopeNode ← STIntMap.freeze state.typeScopeNode
  pure $ coerce { exprScopeNode, binderScopeNode, typeScopeNode }

currentScope ∷ ∀ r. State r → ST r ScopeNode
currentScope state = STRef.read state.scope

pushScope ∷ ∀ r. State r → ScopeNode → ST r Unit
pushScope state scope = void $ STRef.write scope state.scope

assignExprScopeNode ∷ ∀ r. State r → SST.ExprId → ST r Unit
assignExprScopeNode state@{ exprScopeNode } index = do
  scope ← currentScope state
  STIntMap.set (coerce index) scope exprScopeNode

assignBinderScopeNode ∷ ∀ r. State r → SST.BinderId → ST r Unit
assignBinderScopeNode state@{ binderScopeNode } index = do
  scope ← currentScope state
  STIntMap.set (coerce index) scope binderScopeNode

assignTypeScopeNode ∷ ∀ r. State r → SST.TypeId → ST r Unit
assignTypeScopeNode state@{ typeScopeNode } index = do
  scope ← currentScope state
  STIntMap.set (coerce index) scope typeScopeNode

withRevertingScope ∷ ∀ r a. State r → ST r a → ST r a
withRevertingScope state action = do
  previousScope ← currentScope state
  result ← action
  pushScope state previousScope
  pure result

collectDeclaration ∷ ∀ r. State r → SST.Declaration → ST r Unit
collectDeclaration state = case _ of
  SST.DeclarationData _ _ t e →
    withRevertingScope state do
      traverse_ (collectPushType state) t
      collectDataEquation state e
  SST.DeclarationType _ _ t e →
    withRevertingScope state do
      traverse_ (collectPushType state) t
      collectTypeEquation state e
  SST.DeclarationNewtype _ _ t e →
    withRevertingScope state do
      traverse_ (collectPushType state) t
      collectNewtypeEquation state e
  SST.DeclarationClass _ _ t e → do
    withRevertingScope state do
      traverse_ (collectPushType state) t
      collectClassEquation state e
  SST.DeclarationValue _ _ t e →
    withRevertingScope state do
      traverse_ (collectPushType state) t
      traverse_ (collectValueEquation state) e
  SST.DeclarationNotImplemented _ →
    pure unit

collectDataEquation ∷ ∀ r. State r → SST.DataEquation → ST r Unit
collectDataEquation state (SST.DataEquation { variables, constructors }) = do
  withRevertingScope state do
    collectPushTypeVars state variables
    traverse_ (traverse_ $ collectDataConstructor state) constructors

collectDataConstructor ∷ ∀ r. State r → SST.DataConstructor → ST r Unit
collectDataConstructor state (SST.DataConstructor { fields }) = traverse_ (collectType state) fields

collectTypeEquation ∷ ∀ r. State r → SST.TypeEquation → ST r Unit
collectTypeEquation state (SST.TypeEquation { variables, synonymTo }) = do
  withRevertingScope state do
    collectPushTypeVars state variables
    collectType state synonymTo

collectNewtypeEquation ∷ ∀ r. State r → SST.NewtypeEquation → ST r Unit
collectNewtypeEquation state (SST.NewtypeEquation { variables, constructor }) = do
  withRevertingScope state do
    collectPushTypeVars state variables
    case constructor of
      SST.NewtypeConstructor { field } →
        collectType state field

collectClassEquation ∷ ∀ r. State r → SST.ClassEquation → ST r Unit
collectClassEquation state (SST.ClassEquation { variables, methods }) = do
  withRevertingScope state do
    collectPushTypeVars state variables
    traverse_ (traverse_ $ collectClassMethod state) methods

collectClassMethod ∷ ∀ r. State r → SST.ClassMethod → ST r Unit
collectClassMethod state (SST.ClassMethod { signature }) = collectType state signature

collectValueEquation ∷ ∀ r. State r → SST.ValueEquation → ST r Unit
collectValueEquation state (SST.ValueEquation { binders, guarded }) = do
  withRevertingScope state do
    collectPushBinders state binders
    collectGuarded state guarded

collectPushTypeVars ∷ ∀ r t. Traversable t ⇒ State r → t SST.TypeVarBinding → ST r Unit
collectPushTypeVars state typeVars = do
  for_ typeVars case _ of
    SST.TypeVarKinded (SST.Annotation { id }) _ name kind → do
      collectType state kind
      parentScope ← currentScope state
      pushScope state (TypeVar parentScope (coerce name) id)
    SST.TypeVarName (SST.Annotation { id }) _ name → do
      parentScope ← currentScope state
      pushScope state (TypeVar parentScope (coerce name) id)

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
    SST.DoLet _ bindings →
      collectPushLetBindings state $ NEA.toArray bindings
    SST.DoDiscard _ term →
      runSTFn1 go term
    SST.DoBind _ binder term → do
      runSTFn1 go term
      collectPushBinders state [ binder ]
    SST.DoError _ →
      pure unit
    SST.DoNotImplemented _ →
      pure unit

  go ∷ STFn1 SST.Expr r Unit
  go = mkSTFn1 \e →
    case e of
      SST.ExprHole (SST.Annotation { id }) _ →
        assignExprScopeNode state id
      SST.ExprSection (SST.Annotation { id }) →
        assignExprScopeNode state id
      SST.ExprIdent (SST.Annotation { id }) _ →
        assignExprScopeNode state id
      SST.ExprConstructor (SST.Annotation { id }) _ →
        assignExprScopeNode state id
      SST.ExprBoolean (SST.Annotation { id }) _ →
        assignExprScopeNode state id
      SST.ExprChar (SST.Annotation { id }) _ →
        assignExprScopeNode state id
      SST.ExprString (SST.Annotation { id }) _ →
        assignExprScopeNode state id
      SST.ExprInt (SST.Annotation { id }) _ →
        assignExprScopeNode state id
      SST.ExprNumber (SST.Annotation { id }) _ →
        assignExprScopeNode state id
      SST.ExprArray (SST.Annotation { id }) items → do
        assignExprScopeNode state id
        traverse_ (runSTFn1 go) items
      SST.ExprRecord (SST.Annotation { id }) items → do
        assignExprScopeNode state id
        for_ items case _ of
          SST.RecordPun _ → pure unit
          SST.RecordField _ item → runSTFn1 go item
      SST.ExprParens (SST.Annotation { id }) i → do
        assignExprScopeNode state id
        runSTFn1 go i
      SST.ExprTyped (SST.Annotation { id }) i t → do
        assignExprScopeNode state id
        runSTFn1 go i
        collectType state t
      SST.ExprInfix (SST.Annotation { id }) head chain → do
        assignExprScopeNode state id
        runSTFn1 go head
        for_ chain \(Tuple operator operand) → do
          runSTFn1 go operator
          runSTFn1 go operand
      SST.ExprOp (SST.Annotation { id }) head chain → do
        assignExprScopeNode state id
        runSTFn1 go head
        traverse_ (Tuple.snd >>> runSTFn1 go) chain
      SST.ExprOpName (SST.Annotation { id }) _ →
        assignExprScopeNode state id
      SST.ExprNegate (SST.Annotation { id }) i → do
        assignExprScopeNode state id
        runSTFn1 go i
      SST.ExprRecordAccessor (SST.Annotation { id }) i _ → do
        assignExprScopeNode state id
        runSTFn1 go i
      SST.ExprRecordUpdate (SST.Annotation { id }) i r → do
        assignExprScopeNode state id
        runSTFn1 go i
        traverse_ (runSTFn1 goRecordUpdate) r
      SST.ExprApplication (SST.Annotation { id }) f s → do
        assignExprScopeNode state id
        runSTFn1 go f
        traverse_ (runSTFn1 goAppSpine) s
      SST.ExprLambda (SST.Annotation { id }) b i → do
        assignExprScopeNode state id
        withRevertingScope state do
          collectPushBinders state $ NEA.toArray b
          runSTFn1 go i
      SST.ExprIfThenElse (SST.Annotation { id }) c t f → do
        assignExprScopeNode state id
        runSTFn1 go c
        runSTFn1 go t
        runSTFn1 go f
      SST.ExprCase (SST.Annotation { id }) head branches → do
        assignExprScopeNode state id
        traverse_ (runSTFn1 go) head
        for_ branches \(Tuple binders guarded) → do
          withRevertingScope state do
            collectPushBinders state $ NEA.toArray binders
            collectGuarded state guarded
      SST.ExprLet (SST.Annotation { id }) bindings body → do
        assignExprScopeNode state id
        withRevertingScope state do
          collectPushLetBindings state $ NEA.toArray bindings
          runSTFn1 go body
      SST.ExprDo (SST.Annotation { id }) statements → do
        assignExprScopeNode state id
        withRevertingScope state do
          traverse_ (runSTFn1 goPushDoStatement) statements
      SST.ExprAdo (SST.Annotation { id }) statements body → do
        assignExprScopeNode state id
        withRevertingScope state do
          traverse_ (runSTFn1 goPushDoStatement) statements
          runSTFn1 go body
      SST.ExprError (SST.Annotation { id }) →
        assignExprScopeNode state id
      SST.ExprNotImplemented (SST.Annotation { id }) →
        assignExprScopeNode state id

collectBinder ∷ ∀ r. State r → STObject r SST.BinderId → SST.Binder → ST r Unit
collectBinder state perName = runSTFn1 go
  where
  insert ∷ String → SST.BinderId → ST r Unit
  insert k v = void $ STO.poke k v perName

  go ∷ STFn1 SST.Binder r Unit
  go = mkSTFn1 \b → do
    case b of
      SST.BinderWildcard (SST.Annotation { id }) →
        assignBinderScopeNode state id
      SST.BinderVar (SST.Annotation { id }) name → do
        assignBinderScopeNode state id
        insert (coerce name) id
      SST.BinderNamed (SST.Annotation { id }) name _ → do
        assignBinderScopeNode state id
        insert (coerce name) id
      SST.BinderConstructor (SST.Annotation { id }) _ arguments → do
        assignBinderScopeNode state id
        traverse_ (runSTFn1 go) arguments
      SST.BinderBoolean (SST.Annotation { id }) _ →
        assignBinderScopeNode state id
      SST.BinderChar (SST.Annotation { id }) _ →
        assignBinderScopeNode state id
      SST.BinderString (SST.Annotation { id }) _ →
        assignBinderScopeNode state id
      SST.BinderInt (SST.Annotation { id }) _ _ →
        assignBinderScopeNode state id
      SST.BinderNumber (SST.Annotation { id }) _ _ →
        assignBinderScopeNode state id
      SST.BinderArray (SST.Annotation { id }) items → do
        assignBinderScopeNode state id
        traverse_ (runSTFn1 go) items
      SST.BinderRecord (SST.Annotation { id }) items → do
        assignBinderScopeNode state id
        for_ items case _ of
          SST.RecordPun name →
            insert (coerce name) id
          SST.RecordField _ i →
            runSTFn1 go i
      SST.BinderParens (SST.Annotation { id }) i → do
        assignBinderScopeNode state id
        runSTFn1 go i
      SST.BinderTyped (SST.Annotation { id }) i _ → do
        assignBinderScopeNode state id
        runSTFn1 go i
      SST.BinderOp (SST.Annotation { id }) head chain → do
        assignBinderScopeNode state id
        runSTFn1 go head
        traverse_ (Tuple.snd >>> runSTFn1 go) chain
      SST.BinderError (SST.Annotation { id }) →
        assignBinderScopeNode state id
      SST.BinderNotImplemented (SST.Annotation { id }) →
        assignBinderScopeNode state id

collectType ∷ ∀ r. State r → SST.Type → ST r Unit
collectType state t = withRevertingScope state $ collectPushType state t

collectPushType ∷ ∀ r. State r → SST.Type → ST r Unit
collectPushType state = runSTFn1 go
  where
  goRow ∷ STFn1 SST.Row r Unit
  goRow = mkSTFn1 case _ of
    SST.Row { labels, tail } → do
      traverse_ (Tuple.snd >>> runSTFn1 go) labels
      traverse_ (runSTFn1 go) tail

  go ∷ STFn1 SST.Type r Unit
  go = mkSTFn1 \t → do
    case t of
      SST.TypeVar (SST.Annotation { id }) _ →
        assignTypeScopeNode state id
      SST.TypeConstructor (SST.Annotation { id }) _ →
        assignTypeScopeNode state id
      SST.TypeWildcard (SST.Annotation { id }) →
        assignTypeScopeNode state id
      SST.TypeHole (SST.Annotation { id }) _ →
        assignTypeScopeNode state id
      SST.TypeString (SST.Annotation { id }) _ →
        assignTypeScopeNode state id
      SST.TypeInt (SST.Annotation { id }) _ _ →
        assignTypeScopeNode state id
      SST.TypeRow (SST.Annotation { id }) r → do
        assignTypeScopeNode state id
        runSTFn1 goRow r
      SST.TypeRecord (SST.Annotation { id }) r → do
        assignTypeScopeNode state id
        runSTFn1 goRow r
      SST.TypeForall (SST.Annotation { id }) v i → do
        assignTypeScopeNode state id
        collectPushTypeVars state v
        runSTFn1 go i
      SST.TypeKinded (SST.Annotation { id }) i k → do
        assignTypeScopeNode state id
        runSTFn1 go i
        runSTFn1 go k
      SST.TypeApp (SST.Annotation { id }) f a → do
        assignTypeScopeNode state id
        runSTFn1 go f
        traverse_ (runSTFn1 go) a
      SST.TypeOp (SST.Annotation { id }) head chain → do
        assignTypeScopeNode state id
        runSTFn1 go head
        traverse_ (Tuple.snd >>> runSTFn1 go) chain
      SST.TypeOpName (SST.Annotation { id }) _ → do
        assignTypeScopeNode state id
      SST.TypeArrow (SST.Annotation { id }) a r → do
        assignTypeScopeNode state id
        runSTFn1 go a
        runSTFn1 go r
      SST.TypeArrowName (SST.Annotation { id }) →
        assignTypeScopeNode state id
      SST.TypeConstrained (SST.Annotation { id }) c i → do
        assignTypeScopeNode state id
        runSTFn1 go c
        runSTFn1 go i
      SST.TypeParens (SST.Annotation { id }) i → do
        assignTypeScopeNode state id
        runSTFn1 go i
      SST.TypeError (SST.Annotation { id }) →
        assignTypeScopeNode state id
      SST.TypeNotImplemented (SST.Annotation { id }) →
        assignTypeScopeNode state id

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

extractNameId ∷ ∀ r. STObject r SST.LetBindingId → SST.LetBinding → ST r Unit
extractNameId letBoundRaw = case _ of
  SST.LetBindingValue (SST.Annotation { id }) name _ _ →
    void $ STO.poke (coerce name) id letBoundRaw
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
        traverse_ (extractNameId letBoundRaw) kindGroup
        letBound ← O.freezeST letBoundRaw
        parentScope ← currentScope state
        pushScope state (LetBound parentScope letBound)
        traverse_ collectValue kindGroup
      { head: SST.LetBindingPattern _ _ _ } →
        traverse_ collectPattern kindGroup
      _ →
        pure unit

  pure unit

collectModule ∷ ∀ r. SST.Module → IFT.Interface → ST r Result
collectModule (SST.Module { declarations }) interface = do
  state ← defaultState

  parentScope ← currentScope state
  pushScope state (TopLevel parentScope interface)
  traverse_ (collectDeclaration state) declarations

  freezeState state
