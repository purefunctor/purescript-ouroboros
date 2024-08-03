module PureScript.Surface.Lower where

import Prelude

import Control.Monad.ST (Region, ST)
import Control.Monad.ST.Internal (STRef)
import Control.Monad.ST.Ref as STRef
import Control.Monad.ST.Uncurried (STFn1, STFn2, mkSTFn1, mkSTFn2, runSTFn1, runSTFn2)
import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Array.NonEmpty.Internal (NonEmptyArray(..))
import Data.Array.ST (STArray)
import Data.Array.ST as STA
import Data.Maybe (Maybe(..), isJust)
import Data.Symbol (class IsSymbol)
import Data.Traversable (class Traversable, for, for_, traverse)
import Data.Tuple (Tuple(..))
import Data.Tuple as Tuple
import Partial.Unsafe (unsafeCrashWith)
import Prim.Row as Row
import PureScript.CST.Errors (RecoveredError)
import PureScript.CST.Print (printToken)
import PureScript.CST.Range (class RangeOf, rangeOf)
import PureScript.CST.Types as CST
import PureScript.Surface.Error (class IntoRecoveredError, intoRecoveredError)
import PureScript.Surface.SourceRange (DeclarationSourceRange(..), LetBindingSourceRange(..))
import PureScript.Surface.Types as SST
import PureScript.Utils.Immutable.IntMap (IntMap)
import PureScript.Utils.Mutable.STIntMap (STIntMap)
import PureScript.Utils.Mutable.STIntMap as STIntMap
import Record as Record
import Safe.Coerce (coerce)
import Type.Proxy (Proxy(..))

type FieldGroup ∷ (Type → Type → Type) → Row Type
type FieldGroup f =
  ( expr ∷ f SST.Expr CST.SourceRange
  , binder ∷ f SST.Binder CST.SourceRange
  , type ∷ f SST.Type CST.SourceRange
  , doStatement ∷ f SST.DoStatement CST.SourceRange
  , letBinding ∷ f SST.LetBinding LetBindingSourceRange
  , declaration ∷ f SST.Declaration DeclarationSourceRange
  , constructor ∷ f SST.DataConstructor CST.SourceRange
  , newtype ∷ f SST.NewtypeConstructor CST.SourceRange
  , classMethod ∷ f SST.ClassMethod CST.SourceRange
  , typeVarBinding ∷ f SST.TypeVarBinding CST.SourceRange
  )

type ErrorFieldGroup ∷ (Type → Type) → Row Type
type ErrorFieldGroup f =
  ( expr ∷ f SST.Expr
  , binder ∷ f SST.Binder
  , type ∷ f SST.Type
  , doStatement ∷ f SST.DoStatement
  , letBinding ∷ f SST.LetBinding
  , declaration ∷ f SST.Declaration
  )

type MakeIndexState ∷ Region → Type → Type → Type
type MakeIndexState r t s = STRef r Int

type MakeSourceRangeState ∷ Region → Type → Type → Type
type MakeSourceRangeState r t s = STIntMap r s

type MakeSourceRangeFrozen ∷ Type → Type → Type
type MakeSourceRangeFrozen t s = IntMap s

type MakeRecoveredErrorState ∷ Region → Type → Type
type MakeRecoveredErrorState r t = STIntMap r RecoveredError

type MakeRecoveredErrorFrozen ∷ Type → Type
type MakeRecoveredErrorFrozen t = IntMap RecoveredError

type IndexStateFields r = FieldGroup (MakeIndexState r)

type SourceRangeStateFields r = FieldGroup (MakeSourceRangeState r)

type RecoveredErrorStateFields r = ErrorFieldGroup (MakeRecoveredErrorState r)

type StateFields r =
  ( indices ∷ { | IndexStateFields r }
  , sourceRanges ∷ { | SourceRangeStateFields r }
  , errors ∷ { | RecoveredErrorStateFields r }
  )

newtype State r = State { | StateFields r }

newtype SourceRanges = SourceRanges { | FieldGroup MakeSourceRangeFrozen }

derive newtype instance Eq SourceRanges

newtype RecoveredErrors = RecoveredErrors { | ErrorFieldGroup MakeRecoveredErrorFrozen }

derive newtype instance Eq RecoveredErrors

defaultState ∷ ∀ r. ST r (State r)
defaultState = do
  indices ← do
    expr ← STRef.new 0
    binder ← STRef.new 0
    type_ ← STRef.new 0
    doStatement ← STRef.new 0
    letBinding ← STRef.new 0
    declaration ← STRef.new 0
    constructor ← STRef.new 0
    newtype_ ← STRef.new 0
    classMethod ← STRef.new 0
    typeVarBinding ← STRef.new 0
    pure
      { expr
      , binder
      , type: type_
      , doStatement
      , letBinding
      , declaration
      , constructor
      , newtype: newtype_
      , classMethod
      , typeVarBinding
      }
  sourceRanges ← do
    expr ← STIntMap.empty
    binder ← STIntMap.empty
    type_ ← STIntMap.empty
    doStatement ← STIntMap.empty
    letBinding ← STIntMap.empty
    declaration ← STIntMap.empty
    constructor ← STIntMap.empty
    newtype_ ← STIntMap.empty
    classMethod ← STIntMap.empty
    typeVarBinding ← STIntMap.empty
    pure
      { expr
      , binder
      , type: type_
      , doStatement
      , letBinding
      , declaration
      , constructor
      , newtype: newtype_
      , classMethod
      , typeVarBinding
      }
  errors ← do
    expr ← STIntMap.empty
    binder ← STIntMap.empty
    type_ ← STIntMap.empty
    doStatement ← STIntMap.empty
    letBinding ← STIntMap.empty
    declaration ← STIntMap.empty
    pure
      { expr
      , binder
      , type: type_
      , doStatement
      , letBinding
      , declaration
      }
  pure $ State { indices, sourceRanges, errors }

freezeState ∷ ∀ r. State r → ST r { sourceRanges ∷ SourceRanges, errors ∷ RecoveredErrors }
freezeState (State { sourceRanges, errors }) = do
  sourceRanges' ← do
    expr ← STIntMap.freeze sourceRanges.expr
    binder ← STIntMap.freeze sourceRanges.binder
    type_ ← STIntMap.freeze sourceRanges."type"
    doStatement ← STIntMap.freeze sourceRanges.doStatement
    letBinding ← STIntMap.freeze sourceRanges.letBinding
    declaration ← STIntMap.freeze sourceRanges.declaration
    constructor ← STIntMap.freeze sourceRanges.constructor
    newtype_ ← STIntMap.freeze sourceRanges."newtype"
    classMethod ← STIntMap.freeze sourceRanges.classMethod
    typeVarBinding ← STIntMap.freeze sourceRanges.typeVarBinding
    pure $ SourceRanges
      { expr
      , binder
      , type: type_
      , doStatement
      , letBinding
      , declaration
      , constructor
      , newtype: newtype_
      , classMethod
      , typeVarBinding
      }
  errors' ← do
    expr ← STIntMap.freeze errors.expr
    binder ← STIntMap.freeze errors.binder
    type_ ← STIntMap.freeze errors."type"
    doStatement ← STIntMap.freeze errors.doStatement
    letBinding ← STIntMap.freeze errors.letBinding
    declaration ← STIntMap.freeze errors.declaration
    pure $ RecoveredErrors
      { expr
      , binder
      , type: type_
      , doStatement
      , letBinding
      , declaration
      }
  pure $ { sourceRanges: sourceRanges', errors: errors' }

nextIndex
  ∷ ∀ @n r t _t
  . IsSymbol n
  ⇒ Row.Cons n (STRef r Int) _t (IndexStateFields r)
  ⇒ State r
  → ST r (SST.Index t)
nextIndex (State { indices }) = do
  let
    ref ∷ STRef r Int
    ref = Record.get (Proxy ∷ _ n) indices
  index ← STRef.read ref
  void $ STRef.modify (_ + 1) ref
  pure $ SST.Index index

insertSourceRange
  ∷ ∀ @n r s t _t
  . IsSymbol n
  ⇒ Row.Cons n (STIntMap r s) _t (SourceRangeStateFields r)
  ⇒ State r
  → SST.Index t
  → s
  → ST r Unit
insertSourceRange (State { sourceRanges }) index sourceRange = do
  let
    ref ∷ STIntMap r s
    ref = Record.get (Proxy ∷ _ n) sourceRanges
  STIntMap.set (coerce index) sourceRange ref

insertError
  ∷ ∀ @n r e t _t
  . IsSymbol n
  ⇒ Row.Cons n (STIntMap r RecoveredError) _t (RecoveredErrorStateFields r)
  ⇒ IntoRecoveredError e
  ⇒ State r
  → SST.Index t
  → e
  → ST r Unit
insertError (State { errors }) index error = do
  let
    ref ∷ STIntMap r RecoveredError
    ref = Record.get (Proxy ∷ _ n) errors
  STIntMap.set (coerce index) (intoRecoveredError error) ref

unName ∷ ∀ a. CST.Name a → a
unName (CST.Name { name }) = name

lowerQualifiedName ∷ ∀ a. CST.QualifiedName a → SST.QualifiedName a
lowerQualifiedName (CST.QualifiedName { module: moduleName, name }) =
  SST.QualifiedName { moduleName, name }

lowerGuarded ∷ ∀ r e. RangeOf e ⇒ IntoRecoveredError e ⇒ State r → CST.Guarded e → ST r SST.Guarded
lowerGuarded state = case _ of
  CST.Unconditional _ w → SST.Unconditional <$> lowerWhere state w
  CST.Guarded g → SST.Guarded <$> traverse (lowerGuardedExpr state) g

lowerGuardedExpr
  ∷ ∀ r e. RangeOf e ⇒ IntoRecoveredError e ⇒ State r → CST.GuardedExpr e → ST r SST.GuardedExpr
lowerGuardedExpr
  state
  ( CST.GuardedExpr
      { patterns: CST.Separated
          { head: cstPatternsHead
          , tail: cstPatternsTail
          }
      , where: cstWhere
      }
  ) = do
  patternsHead ← lowerPatternGuard state cstPatternsHead
  patternsTail ← traverse (Tuple.snd >>> lowerPatternGuard state) cstPatternsTail
  let patterns = NEA.cons' patternsHead patternsTail
  sstWhere ← lowerWhere state cstWhere
  pure $ SST.GuardedExpr patterns sstWhere

lowerPatternGuard
  ∷ ∀ r e. RangeOf e ⇒ IntoRecoveredError e ⇒ State r → CST.PatternGuard e → ST r SST.PatternGuard
lowerPatternGuard state (CST.PatternGuard { binder: cstBinder, expr: cstExpr }) = do
  binder ← cstBinder # traverse case _ of
    Tuple cstBinder' _ → lowerBinder state cstBinder'
  expr ← lowerExpr state cstExpr
  pure $ SST.PatternGuard binder expr

lowerWhere ∷ ∀ r e. RangeOf e ⇒ IntoRecoveredError e ⇒ State r → CST.Where e → ST r SST.Where
lowerWhere state (CST.Where { expr: cstExpr, bindings: cstBindings }) = do
  expr ← lowerExpr state cstExpr
  bindings ← case cstBindings of
    Just (Tuple _ cstBindings') →
      NEA.toArray <$> lowerLetBindings state cstBindings'
    Nothing →
      pure []
  pure $ SST.Where expr bindings

lowerExpr ∷ ∀ r e. RangeOf e ⇒ IntoRecoveredError e ⇒ State r → CST.Expr e → ST r SST.Expr
lowerExpr state = runSTFn1 go
  where
  goAppSpine ∷ STFn1 (CST.AppSpine CST.Expr e) r SST.AppSpine
  goAppSpine = mkSTFn1 case _ of
    CST.AppTerm e → SST.AppTerm <$> runSTFn1 go e
    CST.AppType _ t → SST.AppType <$> lowerType state t

  goRecordLabeled ∷ STFn1 (CST.RecordLabeled (CST.Expr e)) r (SST.RecordLabeled SST.Expr)
  goRecordLabeled = mkSTFn1 case _ of
    CST.RecordPun (CST.Name { name }) → pure $ SST.RecordPun name
    CST.RecordField (CST.Name { name }) _ e → SST.RecordField name <$> runSTFn1 go e

  goChain ∷ ∀ a b. STFn2 (STFn1 a r b) (Tuple a (CST.Expr e)) r (Tuple b SST.Expr)
  goChain = mkSTFn2 \onOperator (Tuple operator operand) →
    Tuple <$> runSTFn1 onOperator operator <*> runSTFn1 go operand

  goInfixOperator ∷ STFn1 (CST.Wrapped (CST.Expr e)) r SST.Expr
  goInfixOperator = mkSTFn1 case _ of
    CST.Wrapped { value } → runSTFn1 go value

  goOperator ∷ STFn1 (CST.QualifiedName CST.Operator) r (SST.QualifiedName CST.Operator)
  goOperator = mkSTFn1 $ lowerQualifiedName >>> pure

  goRecordUpdate ∷ STFn1 (CST.RecordUpdate e) r SST.RecordUpdate
  goRecordUpdate = mkSTFn1 case _ of
    CST.RecordUpdateLeaf (CST.Name { name }) _ e →
      SST.RecordUpdateLeaf name <$> runSTFn1 go e
    CST.RecordUpdateBranch (CST.Name { name })
      (CST.Wrapped { value: (CST.Separated { head: cstHead, tail: cstTail }) }) → do
      head ← runSTFn1 goRecordUpdate cstHead
      tail ← traverse (Tuple.snd >>> runSTFn1 goRecordUpdate) cstTail
      pure $ SST.RecordUpdateBranch name $ NEA.cons' head tail

  goCaseBranch
    ∷ STFn1
        (Tuple (CST.Separated (CST.Binder e)) (CST.Guarded e))
        r
        (Tuple (NonEmptyArray SST.Binder) SST.Guarded)
  goCaseBranch = mkSTFn1 case _ of
    Tuple (CST.Separated { head: cstHead, tail: cstTail }) cstGuarded → do
      bindersHead ← lowerBinder state cstHead
      bindersTail ← traverse (Tuple.snd >>> lowerBinder state) cstTail
      let binders = NEA.cons' bindersHead bindersTail
      guarded ← lowerGuarded state cstGuarded
      pure $ Tuple binders guarded

  go ∷ STFn1 (CST.Expr e) r SST.Expr
  go = mkSTFn1 \e → do
    let
      range ∷ CST.SourceRange
      range = rangeOf e
    index ← nextIndex @"expr" state
    let
      annotation ∷ SST.ExprAnnotation
      annotation = SST.Annotation { index }
    insertSourceRange @"expr" state index range
    case e of
      CST.ExprHole (CST.Name { name }) → do
        pure $ SST.ExprHole annotation name
      CST.ExprSection _ → do
        pure $ SST.ExprSection annotation
      CST.ExprIdent i → do
        pure $ SST.ExprIdent annotation $ lowerQualifiedName i
      CST.ExprConstructor c → do
        pure $ SST.ExprConstructor annotation $ lowerQualifiedName c
      CST.ExprBoolean _ b → do
        pure $ SST.ExprBoolean annotation b
      CST.ExprChar _ c → do
        pure $ SST.ExprChar annotation c
      CST.ExprString _ s → do
        pure $ SST.ExprString annotation s
      CST.ExprInt _ i → do
        pure $ SST.ExprInt annotation i
      CST.ExprNumber _ n → do
        pure $ SST.ExprNumber annotation n
      CST.ExprArray (CST.Wrapped { value }) → do
        values ← case value of
          Just (CST.Separated { head: cstHead, tail: cstTail }) → do
            head ← runSTFn1 go cstHead
            tail ← traverse (Tuple.snd >>> runSTFn1 go) cstTail
            pure $ Array.cons head tail
          Nothing →
            pure []
        pure $ SST.ExprArray annotation values
      CST.ExprRecord (CST.Wrapped { value }) → do
        values ← case value of
          Just (CST.Separated { head: cstHead, tail: cstTail }) → do
            head ← runSTFn1 goRecordLabeled cstHead
            tail ← traverse (Tuple.snd >>> runSTFn1 goRecordLabeled) cstTail
            pure $ Array.cons head tail
          Nothing → do
            pure []
        pure $ SST.ExprRecord annotation values
      CST.ExprParens (CST.Wrapped { value }) → do
        SST.ExprParens annotation <$> runSTFn1 go value
      CST.ExprTyped tm _ ty → do
        tm' ← runSTFn1 go tm
        ty' ← lowerType state ty
        pure $ SST.ExprTyped annotation tm' ty'
      CST.ExprInfix cstTerm cstChain → do
        term ← runSTFn1 go cstTerm
        chain ← traverse (runSTFn2 goChain goInfixOperator) cstChain
        pure $ SST.ExprInfix annotation term chain
      CST.ExprOp cstTerm cstChain → do
        term ← runSTFn1 go cstTerm
        chain ← traverse (runSTFn2 goChain goOperator) cstChain
        pure $ SST.ExprOp annotation term chain
      CST.ExprOpName n → do
        pure $ SST.ExprOpName annotation $ lowerQualifiedName n
      CST.ExprNegate _ n → do
        SST.ExprNegate annotation <$> runSTFn1 go n
      CST.ExprRecordAccessor { expr: cstExpr, path: CST.Separated { head: cstHead, tail: cstTail } } →
        do
          expr ← runSTFn1 go cstExpr
          let
            path ∷ NonEmptyArray CST.Label
            path = NEA.cons' (unName cstHead) (map (Tuple.snd >>> unName) cstTail)
          pure $ SST.ExprRecordAccessor annotation expr path
      CST.ExprRecordUpdate cstExpr
        (CST.Wrapped { value: (CST.Separated { head: cstHead, tail: cstTail }) }) → do
        expr ← runSTFn1 go cstExpr
        head ← runSTFn1 goRecordUpdate cstHead
        tail ← traverse (Tuple.snd >>> runSTFn1 goRecordUpdate) cstTail
        pure $ SST.ExprRecordUpdate annotation expr $ NEA.cons' head tail
      CST.ExprApp cstHead cstSpine → do
        head ← runSTFn1 go cstHead
        spine ← traverse (runSTFn1 goAppSpine) cstSpine
        pure $ SST.ExprApplication annotation head spine
      CST.ExprLambda { binders: cstBinders, body: cstBody } → do
        binders ← traverse (lowerBinder state) cstBinders
        body ← runSTFn1 go cstBody
        pure $ SST.ExprLambda annotation binders body
      CST.ExprIf { cond: cstCond, true: cstWhen, false: cstUnless } → do
        cond ← runSTFn1 go cstCond
        when ← runSTFn1 go cstWhen
        unless ← runSTFn1 go cstUnless
        pure $ SST.ExprIfThenElse annotation cond when unless
      CST.ExprCase { head: CST.Separated { head: cstHead, tail: cstTail }, branches: cstBranches } →
        do
          headHead ← runSTFn1 go cstHead
          headTail ← traverse (Tuple.snd >>> runSTFn1 go) cstTail
          let head = NEA.cons' headHead headTail
          branches ← traverse (runSTFn1 goCaseBranch) cstBranches
          pure $ SST.ExprCase annotation head branches
      CST.ExprLet { bindings: cstBindings, body: cstBody } → do
        bindings ← lowerLetBindings state cstBindings
        body ← runSTFn1 go cstBody
        pure $ SST.ExprLet annotation bindings body
      CST.ExprDo { statements: cstStatements } → do
        SST.ExprDo annotation <$> traverse (lowerDoStatement state) cstStatements
      CST.ExprAdo { statements: cstStatements, result: cstResult } → do
        SST.ExprAdo annotation <$> traverse (lowerDoStatement state) cstStatements <*> runSTFn1
          go
          cstResult
      CST.ExprError error → do
        insertError @"expr" state index error
        pure $ SST.ExprError annotation

lowerBinder ∷ ∀ r e. RangeOf e ⇒ IntoRecoveredError e ⇒ State r → CST.Binder e → ST r SST.Binder
lowerBinder state = runSTFn1 go
  where
  goRecordLabeled
    ∷ STFn1 (CST.RecordLabeled (CST.Binder e)) r (SST.RecordLabeled SST.Binder)
  goRecordLabeled = mkSTFn1 case _ of
    CST.RecordPun (CST.Name { name }) → pure $ SST.RecordPun name
    CST.RecordField (CST.Name { name }) _ e → SST.RecordField name <$> runSTFn1 go e

  goChain ∷ ∀ a b. STFn2 (STFn1 a r b) (Tuple a (CST.Binder e)) r (Tuple b SST.Binder)
  goChain = mkSTFn2 \onOperator (Tuple operator operand) →
    Tuple <$> runSTFn1 onOperator operator <*> runSTFn1 go operand

  goOperator ∷ STFn1 (CST.QualifiedName CST.Operator) r (SST.QualifiedName CST.Operator)
  goOperator = mkSTFn1 $ lowerQualifiedName >>> pure

  go ∷ STFn1 (CST.Binder e) r SST.Binder
  go = mkSTFn1 \b → do
    let
      range ∷ CST.SourceRange
      range = rangeOf b
    index ← nextIndex @"binder" state
    let
      annotation ∷ SST.BinderAnnotation
      annotation = SST.Annotation { index }
    insertSourceRange @"binder" state index range
    case b of
      CST.BinderWildcard _ →
        pure $ SST.BinderWildcard annotation
      CST.BinderVar (CST.Name { name }) →
        pure $ SST.BinderVar annotation name
      CST.BinderNamed (CST.Name { name }) _ i →
        SST.BinderNamed annotation name <$> runSTFn1 go i
      CST.BinderConstructor n a →
        SST.BinderConstructor annotation (lowerQualifiedName n) <$> traverse (runSTFn1 go) a
      CST.BinderBoolean _ v →
        pure $ SST.BinderBoolean annotation v
      CST.BinderChar _ c →
        pure $ SST.BinderChar annotation c
      CST.BinderString _ s →
        pure $ SST.BinderString annotation s
      CST.BinderInt n _ v →
        pure $ SST.BinderInt annotation (isJust n) v
      CST.BinderNumber n _ v →
        pure $ SST.BinderNumber annotation (isJust n) v
      CST.BinderArray (CST.Wrapped { value: cstValues }) → do
        values ← case cstValues of
          Just (CST.Separated { head: cstValueHead, tail: cstValueTail }) → do
            valueHead ← runSTFn1 go cstValueHead
            valueTail ← traverse (Tuple.snd >>> runSTFn1 go) cstValueTail
            pure $ Array.cons valueHead valueTail
          Nothing →
            pure []
        pure $ SST.BinderArray annotation values
      CST.BinderRecord (CST.Wrapped { value: cstValues }) → do
        values ← case cstValues of
          Just (CST.Separated { head: cstValueHead, tail: cstValueTail }) → do
            valueHead ← runSTFn1 goRecordLabeled cstValueHead
            valueTail ← traverse (Tuple.snd >>> runSTFn1 goRecordLabeled) cstValueTail
            pure $ Array.cons valueHead valueTail
          Nothing →
            pure []
        pure $ SST.BinderRecord annotation values
      CST.BinderParens (CST.Wrapped { value }) → do
        SST.BinderParens annotation <$> runSTFn1 go value
      CST.BinderTyped i _ t → do
        SST.BinderTyped annotation <$> runSTFn1 go i <*> lowerType state t
      CST.BinderOp cstHead cstChain →
        SST.BinderOp annotation
          <$> runSTFn1 go cstHead
          <*> traverse (runSTFn2 goChain goOperator) cstChain
      CST.BinderError error → do
        insertError @"binder" state index error
        pure $ SST.BinderError annotation

lowerType ∷ ∀ r e. RangeOf e ⇒ IntoRecoveredError e ⇒ State r → CST.Type e → ST r SST.Type
lowerType state = runSTFn1 go
  where
  goRowPair
    ∷ STFn1
        (CST.Labeled (CST.Name CST.Label) (CST.Type e))
        r
        (Tuple CST.Label SST.Type)
  goRowPair = mkSTFn1 case _ of
    CST.Labeled { label: (CST.Name { name: cstLabel }), value: cstValue } →
      Tuple cstLabel <$> runSTFn1 go cstValue

  goRow ∷ STFn1 (CST.Wrapped (CST.Row e)) r SST.Row
  goRow = mkSTFn1 case _ of
    CST.Wrapped { value: CST.Row { labels: cstLabels, tail: cstTail } } → do
      labels ← case cstLabels of
        Just (CST.Separated { head: cstLabelsHead, tail: cstLabelsTail }) → do
          labelsHead ← runSTFn1 goRowPair cstLabelsHead
          labelsTail ← traverse (Tuple.snd >>> runSTFn1 goRowPair) cstLabelsTail
          pure $ Array.cons labelsHead labelsTail
        Nothing →
          pure []
      tail ← traverse (Tuple.snd >>> lowerType state) cstTail
      pure $ SST.Row { labels, tail }

  goChain ∷ ∀ a b. STFn2 (STFn1 a r b) (Tuple a (CST.Type e)) r (Tuple b SST.Type)
  goChain = mkSTFn2 \onOperator (Tuple operator operand) →
    Tuple <$> runSTFn1 onOperator operator <*> runSTFn1 go operand

  goOperator ∷ STFn1 (CST.QualifiedName CST.Operator) r (SST.QualifiedName CST.Operator)
  goOperator = mkSTFn1 $ lowerQualifiedName >>> pure

  go ∷ STFn1 (CST.Type e) r SST.Type
  go = mkSTFn1 \t → do
    let
      range ∷ CST.SourceRange
      range = rangeOf t
    index ← nextIndex @"type" state
    let
      annotation ∷ SST.TypeAnnotation
      annotation = SST.Annotation { index }
    insertSourceRange @"type" state index range
    case t of
      CST.TypeVar (CST.Name { name }) →
        pure $ SST.TypeVar annotation name
      CST.TypeConstructor c →
        pure $ SST.TypeConstructor annotation $ lowerQualifiedName c
      CST.TypeWildcard _ →
        pure $ SST.TypeWildcard annotation
      CST.TypeHole (CST.Name { name }) →
        pure $ SST.TypeHole annotation name
      CST.TypeString _ s →
        pure $ SST.TypeString annotation s
      CST.TypeInt n _ i →
        pure $ SST.TypeInt annotation (isJust n) i
      CST.TypeRow r → do
        SST.TypeRow annotation <$> runSTFn1 goRow r
      CST.TypeRecord r → do
        SST.TypeRecord annotation <$> runSTFn1 goRow r
      CST.TypeForall _ cstBindings _ cstBody → do
        bindings ← lowerTypeVarBindingsPrefixed state cstBindings
        body ← runSTFn1 go cstBody
        pure $ SST.TypeForall annotation bindings body
      CST.TypeKinded cstType _ cstKind →
        SST.TypeKinded annotation
          <$> runSTFn1 go cstType
          <*> runSTFn1 go cstKind
      CST.TypeApp cstType cstArguments →
        SST.TypeApp annotation
          <$> runSTFn1 go cstType
          <*> traverse (runSTFn1 go) cstArguments
      CST.TypeOp cstHead cstChain →
        SST.TypeOp annotation
          <$> runSTFn1 go cstHead
          <*> traverse (runSTFn2 goChain goOperator) cstChain
      CST.TypeOpName n →
        pure $ SST.TypeOpName annotation $ lowerQualifiedName n
      CST.TypeArrow cstArgument _ cstReturn →
        SST.TypeArrow annotation
          <$> runSTFn1 go cstArgument
          <*> runSTFn1 go cstReturn
      CST.TypeArrowName _ →
        pure $ SST.TypeArrowName annotation
      CST.TypeConstrained cstConstraint _ cstConstrained →
        SST.TypeConstrained annotation
          <$> runSTFn1 go cstConstraint
          <*> runSTFn1 go cstConstrained
      CST.TypeParens (CST.Wrapped { value }) →
        SST.TypeParens annotation <$> runSTFn1 go value
      CST.TypeError error → do
        insertError @"type" state index error
        pure $ SST.TypeError annotation

data LetLoweringGroup r = LetLoweringGroup
  CST.Ident
  (STRef r (Maybe { sourceRange ∷ CST.SourceRange, t ∷ SST.Type }))
  (STArray r { sourceRange ∷ CST.SourceRange, v ∷ SST.ValueEquation })

lowerLetBindings
  ∷ ∀ r e
  . RangeOf e
  ⇒ IntoRecoveredError e
  ⇒ State r
  → NonEmptyArray (CST.LetBinding e)
  → ST r (NonEmptyArray SST.LetBinding)
lowerLetBindings state cstLetBindings = do
  currentGroupRef ← STRef.new Nothing
  letBindingsRaw ← STA.new

  let
    dischargeGroup ∷ ST r Unit
    dischargeGroup = do
      currentGroup ← STRef.read currentGroupRef
      case currentGroup of
        Just (LetLoweringGroup groupName signatureRef valuesRaw) → do
          signature ← STRef.read signatureRef
          values ← STA.unsafeFreeze valuesRaw
          let
            letBindingSourceRange ∷ LetBindingSourceRange
            letBindingSourceRange = LetBindingNameSourceRange
              { signature: signature <#> _.sourceRange
              , definitions: values <#> _.sourceRange
              }
          index ← nextIndex @"letBinding" state
          let
            annotation ∷ SST.LetBindingAnnotation
            annotation = SST.Annotation { index }
          insertSourceRange @"letBinding" state index letBindingSourceRange
          let
            letBinding ∷ SST.LetBinding
            letBinding =
              SST.LetBindingValue annotation groupName (signature <#> _.t) (values <#> _.v)
          void $ STA.push letBinding letBindingsRaw
        Nothing →
          pure unit
      void $ STRef.write Nothing currentGroupRef

    newNameGroup ∷ CST.Ident → _ → _ → ST r Unit
    newNameGroup groupName signature values = do
      signatureRef ← STRef.new signature
      valuesRaw ← STA.unsafeThaw values
      void $ STRef.write (Just $ LetLoweringGroup groupName signatureRef valuesRaw) currentGroupRef

    onLetSignature ∷ CST.SourceRange → CST.Ident → SST.Type → ST r Unit
    onLetSignature sourceRange signatureName t = do
      currentGroup ← STRef.read currentGroupRef
      case currentGroup of
        Just (LetLoweringGroup groupName signatureRef _) → do
          if signatureName == groupName then do
            void $ STRef.write (Just { sourceRange, t }) signatureRef
          else do
            dischargeGroup
            newNameGroup signatureName (Just { sourceRange, t }) []
        Nothing → do
          newNameGroup signatureName (Just { sourceRange, t }) []

    onLetName ∷ CST.SourceRange → CST.Ident → SST.ValueEquation → ST r Unit
    onLetName sourceRange valueName v = do
      currentGroup ← STRef.read currentGroupRef
      case currentGroup of
        Just (LetLoweringGroup groupName _ values) → do
          if valueName == groupName then
            void $ STA.push { sourceRange, v } values
          else do
            dischargeGroup
            newNameGroup valueName Nothing [ { sourceRange, v } ]
        Nothing → do
          newNameGroup valueName Nothing [ { sourceRange, v } ]

  for_ cstLetBindings \cstLetBinding → do
    let
      sourceRange ∷ CST.SourceRange
      sourceRange = rangeOf cstLetBinding
    case cstLetBinding of
      CST.LetBindingSignature (CST.Labeled { label: CST.Name { name }, value }) → do
        signature ← lowerType state value
        onLetSignature sourceRange name signature
      CST.LetBindingName { name: CST.Name { name }, binders: cstBinders, guarded: cstGuarded } → do
        binders ← traverse (lowerBinder state) cstBinders
        guarded ← lowerGuarded state cstGuarded
        onLetName sourceRange name (SST.ValueEquation { binders, guarded })
      CST.LetBindingPattern cstBinder _ cstWhere → do
        dischargeGroup
        let
          letBindingSourceRange ∷ LetBindingSourceRange
          letBindingSourceRange = LetBindingPatternSourceRange sourceRange
        index ← nextIndex @"letBinding" state
        let
          annotation ∷ SST.LetBindingAnnotation
          annotation = SST.Annotation { index }
        insertSourceRange @"letBinding" state index letBindingSourceRange
        sstBinder ← lowerBinder state cstBinder
        sstWhere ← lowerWhere state cstWhere
        let
          letBinding ∷ SST.LetBinding
          letBinding = SST.LetBindingPattern annotation sstBinder sstWhere
        void $ STA.push letBinding letBindingsRaw
      CST.LetBindingError error → do
        dischargeGroup
        let
          letBindingSourceRange ∷ LetBindingSourceRange
          letBindingSourceRange = LetBindingErrorSourceRange sourceRange
        index ← nextIndex @"letBinding" state
        let
          annotation ∷ SST.LetBindingAnnotation
          annotation = SST.Annotation { index }
        insertSourceRange @"letBinding" state index letBindingSourceRange
        insertError @"letBinding" state index error
        let
          letBinding ∷ SST.LetBinding
          letBinding = SST.LetBindingError annotation
        void $ STA.push letBinding letBindingsRaw

  dischargeGroup
  letBindings ← STA.unsafeFreeze letBindingsRaw
  pure $ NonEmptyArray letBindings

lowerDoStatement
  ∷ ∀ r e. RangeOf e ⇒ IntoRecoveredError e ⇒ State r → CST.DoStatement e → ST r SST.DoStatement
lowerDoStatement state = runSTFn1 go
  where
  go ∷ STFn1 (CST.DoStatement e) r SST.DoStatement
  go = mkSTFn1 \d → do
    let
      range ∷ CST.SourceRange
      range = rangeOf d
    index ← nextIndex @"doStatement" state
    let
      annotation ∷ SST.DoStatementAnnotation
      annotation = SST.Annotation { index }
    insertSourceRange @"doStatement" state index range
    case d of
      CST.DoLet _ cstLetBindings → do
        SST.DoLet annotation <$> lowerLetBindings state cstLetBindings
      CST.DoDiscard cstExpr → do
        SST.DoDiscard annotation <$> lowerExpr state cstExpr
      CST.DoBind cstBinder _ cstExpr → do
        SST.DoBind annotation <$> lowerBinder state cstBinder <*> lowerExpr state cstExpr
      CST.DoError error → do
        insertError @"doStatement" state index error
        pure $ SST.DoError annotation

lowerDataMembers ∷ Maybe CST.DataMembers → Maybe SST.DataMembers
lowerDataMembers cstDataMembers = cstDataMembers >>= case _ of
  CST.DataAll _ →
    pure SST.DataAll
  CST.DataEnumerated (CST.Wrapped { value }) →
    value <#> case _ of
      CST.Separated { head, tail } → do
        let
          head' ∷ CST.Proper
          head' = unName head

          tail' ∷ Array CST.Proper
          tail' = (Tuple.snd >>> unName) <$> tail
        SST.DataEnumerated $ Array.cons head' tail'

lowerExports
  ∷ ∀ r e
  . Maybe (CST.DelimitedNonEmpty (CST.Export e))
  → ST r (Maybe (NonEmptyArray SST.Export))
lowerExports cstExports = for cstExports case _ of
  CST.Wrapped { value: CST.Separated { head: headExport, tail } } → do
    let
      lowerExport ∷ CST.Export e → SST.Export
      lowerExport = case _ of
        CST.ExportValue v →
          SST.ExportValue (unName v)
        CST.ExportOp o →
          SST.ExportOp (unName o)
        CST.ExportType p m → do
          SST.ExportType (unName p) (lowerDataMembers m)
        CST.ExportTypeOp _ o →
          SST.ExportTypeOp (unName o)
        CST.ExportClass _ n →
          SST.ExportClass (unName n)
        CST.ExportModule _ m →
          SST.ExportModule (unName m)
        CST.ExportError _ →
          SST.ExportNotImplemented

    exportsRaw ← STA.new

    void $ STA.push (lowerExport headExport) exportsRaw
    for_ tail \(Tuple _ tailExport) → do
      void $ STA.push (lowerExport tailExport) exportsRaw

    exports ← STA.freeze exportsRaw
    pure $ NonEmptyArray exports

lowerImportDecls ∷ ∀ r e. Array (CST.ImportDecl e) → ST r (Array SST.Import)
lowerImportDecls cstImports = do
  importsRaw ← STA.new

  for_ cstImports \cstImport →
    case cstImport of
      CST.ImportDecl { module: CST.Name { name: importName } } → do
        let
          sstImport ∷ SST.Import
          sstImport = SST.Import { name: importName }
        void $ STA.push sstImport importsRaw

  STA.unsafeFreeze importsRaw

bySignatureName ∷ ∀ e. CST.Declaration e → CST.Declaration e → Boolean
bySignatureName = case _, _ of
  CST.DeclSignature (CST.Labeled { label: CST.Name { name: signatureName } }),
  CST.DeclValue ({ name: CST.Name { name: valueName } }) →
    signatureName == valueName
  CST.DeclValue ({ name: CST.Name { name: valueNameX } }),
  CST.DeclValue ({ name: CST.Name { name: valueNameY } }) →
    valueNameX == valueNameY
  CST.DeclKindSignature { value } (CST.Labeled { label: CST.Name { name: signatureName } }),
  CST.DeclData { name: CST.Name { name: dataName } } _ →
    printToken value == "data" && signatureName == dataName
  CST.DeclKindSignature { value } (CST.Labeled { label: CST.Name { name: signatureName } }),
  CST.DeclType { name: CST.Name { name: dataName } } _ _ →
    printToken value == "type" && signatureName == dataName
  CST.DeclKindSignature { value } (CST.Labeled { label: CST.Name { name: signatureName } }),
  CST.DeclNewtype { name: CST.Name { name: newtypeName } } _ _ _ →
    printToken value == "newtype" && signatureName == newtypeName
  CST.DeclKindSignature { value } (CST.Labeled { label: CST.Name { name: signatureName } }),
  CST.DeclClass { name: CST.Name { name: className } } _ →
    printToken value == "class" && signatureName == className
  _, _ →
    false

lowerDataCtor
  ∷ ∀ r e. RangeOf e ⇒ IntoRecoveredError e ⇒ State r → CST.DataCtor e → ST r SST.DataConstructor
lowerDataCtor state dataCtor = do
  index ← nextIndex @"constructor" state
  let
    sourceRange ∷ CST.SourceRange
    sourceRange = rangeOf dataCtor
  insertSourceRange @"constructor" state index sourceRange
  let
    annotation ∷ SST.ConstructorAnnotation
    annotation = SST.Annotation { index }
  case dataCtor of
    CST.DataCtor { name: CST.Name { name }, fields: cstFields } → do
      fields ← traverse (lowerType state) cstFields
      pure $ SST.DataConstructor { annotation, name, fields }

lowerTypeVarBindings_
  ∷ ∀ t i r e
  . Traversable t
  ⇒ RangeOf i
  ⇒ RangeOf e
  ⇒ IntoRecoveredError e
  ⇒ (i → { visible ∷ Boolean, name ∷ CST.Ident })
  → State r
  → t (CST.TypeVarBinding i e)
  → ST r (t SST.TypeVarBinding)
lowerTypeVarBindings_ un state = traverse \typeVarBinding → do
  index ← nextIndex @"typeVarBinding" state
  let
    sourceRange ∷ CST.SourceRange
    sourceRange = rangeOf typeVarBinding
  insertSourceRange @"typeVarBinding" state index sourceRange
  let
    annotation ∷ SST.TypeVarBindingAnnotation
    annotation = SST.Annotation { index }
  case typeVarBinding of
    CST.TypeVarKinded (CST.Wrapped { value: CST.Labeled { label, value } }) → do
      let { visible, name } = un label
      kind ← lowerType state value
      pure $ SST.TypeVarKinded annotation visible name kind
    CST.TypeVarName cstName → do
      let { visible, name } = un cstName
      pure $ SST.TypeVarName annotation visible name

lowerTypeVarBindings
  ∷ ∀ t r e
  . Traversable t
  ⇒ RangeOf e
  ⇒ IntoRecoveredError e
  ⇒ State r
  → t (CST.TypeVarBinding (CST.Name CST.Ident) e)
  → ST r (t SST.TypeVarBinding)
lowerTypeVarBindings = lowerTypeVarBindings_ case _ of
  CST.Name { name } → { visible: false, name }

lowerTypeVarBindingsPrefixed
  ∷ ∀ t r e
  . Traversable t
  ⇒ RangeOf e
  ⇒ IntoRecoveredError e
  ⇒ State r
  → t (CST.TypeVarBinding (CST.Prefixed (CST.Name CST.Ident)) e)
  → ST r (t SST.TypeVarBinding)
lowerTypeVarBindingsPrefixed = lowerTypeVarBindings_ case _ of
  CST.Prefixed { prefix, value: CST.Name { name } } → { visible: isJust prefix, name }

lowerDataEquation
  ∷ ∀ r e
  . RangeOf e
  ⇒ IntoRecoveredError e
  ⇒ State r
  → CST.DataHead e
  → Maybe (Tuple CST.SourceToken (CST.Separated (CST.DataCtor e)))
  → ST r SST.DataEquation
lowerDataEquation state { vars } cstConstructors = do
  variables ← lowerTypeVarBindings state vars
  constructors ← for cstConstructors case _ of
    Tuple _ (CST.Separated { head, tail }) → do
      sstHead ← lowerDataCtor state head
      sstTail ← traverse (Tuple.snd >>> lowerDataCtor state) tail
      pure $ NEA.cons' sstHead sstTail
  pure $ SST.DataEquation { variables, constructors }

lowerTypeEquation
  ∷ ∀ r e
  . RangeOf e
  ⇒ IntoRecoveredError e
  ⇒ State r
  → CST.DataHead e
  → CST.Type e
  → ST r SST.TypeEquation
lowerTypeEquation state { vars } cstType = do
  variables ← lowerTypeVarBindings state vars
  synonymTo ← lowerType state cstType
  pure $ SST.TypeEquation { variables, synonymTo }

lowerNewtypeEquation
  ∷ ∀ r e
  . RangeOf e
  ⇒ IntoRecoveredError e
  ⇒ State r
  → CST.DataHead e
  → CST.Name CST.Proper
  → CST.Type e
  → ST r SST.NewtypeEquation
lowerNewtypeEquation state { vars } cstName@(CST.Name { name }) cstField = do
  index ← nextIndex @"newtype" state
  let
    sourceRange ∷ CST.SourceRange
    sourceRange =
      { start: rangeOf cstName # _.start
      , end: rangeOf cstField # _.end
      }
  insertSourceRange @"newtype" state index sourceRange
  variables ← lowerTypeVarBindings state vars
  let
    annotation ∷ SST.NewtypeAnnotation
    annotation = SST.Annotation { index }
  field ← lowerType state cstField
  pure $ SST.NewtypeEquation
    { variables
    , constructor: SST.NewtypeConstructor
        { annotation
        , name
        , field
        }

    }

type CSTClassMethod e =
  CST.Labeled (CST.Name CST.Ident) (CST.Type e)

lowerClassMethod
  ∷ ∀ r e. RangeOf e ⇒ IntoRecoveredError e ⇒ State r → CSTClassMethod e → ST r SST.ClassMethod
lowerClassMethod state cstClassMethod = do
  index ← nextIndex @"classMethod" state
  let
    sourceRange ∷ CST.SourceRange
    sourceRange = rangeOf cstClassMethod
  insertSourceRange @"classMethod" state index sourceRange
  let
    annotation ∷ SST.ClassMethodAnnotation
    annotation = SST.Annotation { index }
  case cstClassMethod of
    CST.Labeled { label: CST.Name { name }, value } → do
      signature ← lowerType state value
      pure $ SST.ClassMethod { annotation, name, signature }

type CSTClassBody e =
  Tuple CST.SourceToken (NonEmptyArray (CSTClassMethod e))

lowerClassBody
  ∷ ∀ r e
  . RangeOf e
  ⇒ IntoRecoveredError e
  ⇒ State r
  → CST.ClassHead e
  → Maybe (CSTClassBody e)
  → ST r SST.ClassEquation
lowerClassBody state { vars } classBody = do
  variables ← lowerTypeVarBindings state vars
  methods ← for classBody case _ of
    Tuple _ classMethods →
      traverse (lowerClassMethod state) classMethods
  pure $ SST.ClassEquation { variables, methods }

lowerDeclarations
  ∷ ∀ r e
  . RangeOf e
  ⇒ IntoRecoveredError e
  ⇒ State r
  → Array (CST.Declaration e)
  → ST r (Array SST.Declaration)
lowerDeclarations state cstDeclarations = do
  declarationsRaw ← STA.new

  let
    signatureNameGroups ∷ Array (NonEmptyArray (CST.Declaration e))
    signatureNameGroups = Array.groupBy bySignatureName cstDeclarations

    onTypeGroup ∷ CST.Proper → _ → _ → ST r Unit
    onTypeGroup cstName cstSignature cstDeclaration = do
      index ← nextIndex @"declaration" state
      let
        declarationSourceRange ∷ DeclarationSourceRange
        declarationSourceRange = DeclarationValueSourceRange
          { signature: cstSignature <#> rangeOf
          , definitions: cstDeclaration <#> rangeOf
          }
      insertSourceRange @"declaration" state index declarationSourceRange

      signature ← for cstSignature case _ of
        CST.DeclKindSignature _ (CST.Labeled { value: cstType }) →
          lowerType state cstType
        _ →
          unsafeCrashWith "invariant violated: expecting DeclKindSignature"

      let
        annotation ∷ SST.DeclarationAnnotation
        annotation = SST.Annotation { index }

      declaration ← case cstDeclaration of
        [ CST.DeclData dataHead dataEquation ] → do
          equation ← lowerDataEquation state dataHead dataEquation
          pure $ SST.DeclarationData annotation cstName signature equation
        [ CST.DeclType dataHead _ ctorType ] → do
          equation ← lowerTypeEquation state dataHead ctorType
          pure $ SST.DeclarationType annotation cstName signature equation
        [ CST.DeclNewtype dataHead _ ctorName ctorField ] → do
          equation ← lowerNewtypeEquation state dataHead ctorName ctorField
          pure $ SST.DeclarationNewtype annotation cstName signature equation
        [ CST.DeclClass classHead classBody ] → do
          body ← lowerClassBody state classHead classBody
          pure $ SST.DeclarationClass annotation cstName signature body
        _ →
          unsafeCrashWith "invariant violated: expecting DeclData/DeclType/DeclNewtype"

      void $ STA.push declaration declarationsRaw

    onDeclValueGroup ∷ CST.Ident → _ → _ → ST r Unit
    onDeclValueGroup cstName cstSignature cstValues = do
      index ← nextIndex @"declaration" state
      let
        declarationSourceRange ∷ DeclarationSourceRange
        declarationSourceRange = DeclarationValueSourceRange
          { signature: cstSignature <#> rangeOf
          , definitions: cstValues <#> rangeOf
          }
      insertSourceRange @"declaration" state index declarationSourceRange

      signature ← for cstSignature case _ of
        CST.DeclSignature (CST.Labeled { value: cstType }) →
          lowerType state cstType
        _ →
          unsafeCrashWith "invariant violated: expecting DeclSignature"

      values ← for cstValues case _ of
        CST.DeclValue { binders: cstBinders, guarded: cstGuarded } → do
          binders ← traverse (lowerBinder state) cstBinders
          guarded ← lowerGuarded state cstGuarded
          pure $ SST.ValueEquation { binders, guarded }
        _ →
          unsafeCrashWith "invariant violated: expecting DeclValue"

      let
        annotation ∷ SST.DeclarationAnnotation
        annotation = SST.Annotation { index }

        declaration ∷ SST.Declaration
        declaration = SST.DeclarationValue annotation cstName signature values

      void $ STA.push declaration declarationsRaw

  for_ signatureNameGroups \signatureNameGroup →
    case NEA.uncons signatureNameGroup of
      { head, tail } → case head of
        CST.DeclData { name: CST.Name { name } } _ →
          onTypeGroup name Nothing (NEA.toArray signatureNameGroup)
        CST.DeclType { name: CST.Name { name } } _ _ →
          onTypeGroup name Nothing (NEA.toArray signatureNameGroup)
        CST.DeclNewtype { name: CST.Name { name } } _ _ _ →
          onTypeGroup name Nothing (NEA.toArray signatureNameGroup)
        CST.DeclClass { name: CST.Name { name } } _ →
          onTypeGroup name Nothing (NEA.toArray signatureNameGroup)
        CST.DeclKindSignature _ (CST.Labeled { label: CST.Name { name } }) →
          onTypeGroup name (Just head) tail
        CST.DeclSignature (CST.Labeled { label: CST.Name { name } }) →
          onDeclValueGroup name (Just head) tail
        CST.DeclValue { name: CST.Name { name } } →
          onDeclValueGroup name Nothing (NEA.toArray signatureNameGroup)
        CST.DeclError error → do
          index ← nextIndex @"declaration" state
          let
            declarationSourceRange ∷ DeclarationSourceRange
            declarationSourceRange = DeclarationErrorSourceRange $ rangeOf head
          insertSourceRange @"declaration" state index declarationSourceRange
          insertError @"declaration" state index error
        _ →
          pure unit

  STA.freeze declarationsRaw

type Result =
  { surface ∷ SST.Module
  , sourceRanges ∷ SourceRanges
  , errors ∷ RecoveredErrors
  }

lowerModule ∷ ∀ r e. RangeOf e ⇒ IntoRecoveredError e ⇒ CST.Module e → ST r Result
lowerModule
  ( CST.Module
      { header: CST.ModuleHeader
          { name: CST.Name { name }
          , exports: cstExports
          , imports: cstImports
          }
      , body: CST.ModuleBody { decls: cstDeclarations }
      }
  ) = do
  state ← defaultState
  surface ← do
    exports ← lowerExports cstExports
    imports ← lowerImportDecls cstImports
    declarations ← lowerDeclarations state cstDeclarations
    pure $ SST.Module { name, exports, imports, declarations }
  { sourceRanges, errors } ← freezeState state
  pure { surface, sourceRanges, errors }
