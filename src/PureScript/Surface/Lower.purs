module PureScript.Surface.Lower where

import Prelude

import Control.Monad.ST (ST)
import Control.Monad.ST.Internal (STRef)
import Control.Monad.ST.Ref as STRef
import Control.Monad.ST.Uncurried (STFn1, STFn2, mkSTFn1, mkSTFn2, runSTFn1, runSTFn2)
import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Array.NonEmpty.Internal (NonEmptyArray(..))
import Data.Array.ST (STArray)
import Data.Array.ST as STA
import Data.Maybe (Maybe(..), isJust)
import Data.Traversable (class Traversable, for, for_, traverse)
import Data.Tuple (Tuple(..))
import Data.Tuple as Tuple
import Partial.Unsafe (unsafeCrashWith)
import PureScript.CST.Print (printToken)
import PureScript.CST.Range (rangeOf)
import PureScript.CST.Types as CST
import PureScript.Surface.Types as SST
import PureScript.Utils.Mutable.Array (MutableArray)
import PureScript.Utils.Mutable.Array as MutableArray
import Safe.Coerce (class Coercible, coerce)

type SigDefSourceRange =
  { signature ∷ Maybe CST.SourceRange
  , definitions ∷ Array CST.SourceRange
  }

data LetBindingSourceRange
  = LetBindingNameSourceRange SigDefSourceRange
  | LetBindingPatternSourceRange CST.SourceRange

derive instance Eq LetBindingSourceRange

data DeclarationSourceRange
  = DeclarationDataSourceRange SigDefSourceRange
  | DeclarationValueSourceRange SigDefSourceRange

derive instance Eq DeclarationSourceRange

type StateIndex r = STRef r Int
type StateSourceRange r = MutableArray r CST.SourceRange
type StateLetBindingSourceRange r = MutableArray r LetBindingSourceRange
type StateDeclarationSourceRange r = MutableArray r DeclarationSourceRange

newtype State r = State
  { exprIndex ∷ StateIndex r
  , binderIndex ∷ StateIndex r
  , typeIndex ∷ StateIndex r
  , letBindingIndex ∷ StateIndex r
  , declarationIndex ∷ StateIndex r
  , constructorIndex ∷ StateIndex r
  , newtypeIndex ∷ StateIndex r
  , classMethodIndex ∷ StateIndex r
  , exprSourceRange ∷ StateSourceRange r
  , binderSourceRange ∷ StateSourceRange r
  , typeSourceRange ∷ StateSourceRange r
  , letBindingSourceRange ∷ StateLetBindingSourceRange r
  , declarationSourceRange ∷ StateDeclarationSourceRange r
  , constructorSourceRange ∷ StateSourceRange r
  , newtypeSourceRange ∷ StateSourceRange r
  , classMethodSourceRange ∷ StateSourceRange r
  }

type SourceRanges =
  { exprSourceRange ∷ SST.SparseMap SST.Expr CST.SourceRange
  , binderSourceRange ∷ SST.SparseMap SST.Binder CST.SourceRange
  , typeSourceRange ∷ SST.SparseMap SST.Type CST.SourceRange
  , letBindingSourceRange ∷ SST.SparseMap SST.LetBinding LetBindingSourceRange
  , declarationSourceRange ∷ SST.SparseMap SST.Declaration DeclarationSourceRange
  , constructorSourceRange ∷ SST.SparseMap SST.DataConstructor CST.SourceRange
  , newtypeSourceRange ∷ SST.SparseMap SST.NewtypeConstructor CST.SourceRange
  , classMethodSourceRange ∷ SST.SparseMap SST.ClassMethod CST.SourceRange
  }

defaultState ∷ ∀ r. ST r (State r)
defaultState = do
  exprIndex ← STRef.new 0
  binderIndex ← STRef.new 0
  typeIndex ← STRef.new 0
  letBindingIndex ← STRef.new 0
  declarationIndex ← STRef.new 0
  constructorIndex ← STRef.new 0
  newtypeIndex ← STRef.new 0
  classMethodIndex ← STRef.new 0
  exprSourceRange ← MutableArray.empty
  binderSourceRange ← MutableArray.empty
  typeSourceRange ← MutableArray.empty
  letBindingSourceRange ← MutableArray.empty
  declarationSourceRange ← MutableArray.empty
  constructorSourceRange ← MutableArray.empty
  newtypeSourceRange ← MutableArray.empty
  classMethodSourceRange ← MutableArray.empty
  pure $ State
    { exprIndex
    , binderIndex
    , typeIndex
    , letBindingIndex
    , declarationIndex
    , constructorIndex
    , newtypeIndex
    , classMethodIndex
    , exprSourceRange
    , binderSourceRange
    , typeSourceRange
    , letBindingSourceRange
    , declarationSourceRange
    , constructorSourceRange
    , newtypeSourceRange
    , classMethodSourceRange
    }

freezeState ∷ ∀ r. State r → ST r SourceRanges
freezeState (State state) = do
  exprSourceRange ← coerce $ MutableArray.unsafeFreeze state.exprSourceRange
  binderSourceRange ← coerce $ MutableArray.unsafeFreeze state.binderSourceRange
  typeSourceRange ← coerce $ MutableArray.unsafeFreeze state.typeSourceRange
  letBindingSourceRange ← coerce $ MutableArray.unsafeFreeze state.letBindingSourceRange
  declarationSourceRange ← coerce $ MutableArray.unsafeFreeze state.declarationSourceRange
  constructorSourceRange ← coerce $ MutableArray.unsafeFreeze state.constructorSourceRange
  newtypeSourceRange ← coerce $ MutableArray.unsafeFreeze state.constructorSourceRange
  classMethodSourceRange ← coerce $ MutableArray.unsafeFreeze state.classMethodSourceRange
  pure
    { exprSourceRange
    , binderSourceRange
    , typeSourceRange
    , letBindingSourceRange
    , declarationSourceRange
    , constructorSourceRange
    , newtypeSourceRange
    , classMethodSourceRange
    }

nextIndex ∷ ∀ r a. (State r → StateIndex r) → State r → ST r (SST.Index a)
nextIndex getRef state = do
  let ref = getRef state
  index ← STRef.read ref
  void $ STRef.modify (_ + 1) ref
  pure $ SST.Index index

nextExprIndex ∷ ∀ r. State r → ST r SST.ExprIndex
nextExprIndex = nextIndex \(State { exprIndex }) → exprIndex

nextBinderIndex ∷ ∀ r. State r → ST r SST.BinderIndex
nextBinderIndex = nextIndex \(State { binderIndex }) → binderIndex

nextTypeIndex ∷ ∀ r. State r → ST r SST.TypeIndex
nextTypeIndex = nextIndex \(State { typeIndex }) → typeIndex

nextLetBindingIndex ∷ ∀ r. State r → ST r SST.LetBindingIndex
nextLetBindingIndex = nextIndex \(State { letBindingIndex }) → letBindingIndex

nextDeclarationIndex ∷ ∀ r. State r → ST r SST.DeclarationIndex
nextDeclarationIndex = nextIndex \(State { declarationIndex }) → declarationIndex

nextConstructorIndex ∷ ∀ r. State r → ST r SST.ConstructorIndex
nextConstructorIndex = nextIndex \(State { constructorIndex }) → constructorIndex

nextNewtypeIndex ∷ ∀ r. State r → ST r SST.NewtypeIndex
nextNewtypeIndex = nextIndex \(State { newtypeIndex }) → newtypeIndex

nextClassMethodIndex ∷ ∀ r. State r → ST r SST.ClassMethodIndex
nextClassMethodIndex = nextIndex \(State { classMethodIndex }) → classMethodIndex

insertSourceRange
  ∷ ∀ r k v
  . Coercible k Int
  ⇒ (State r → MutableArray r v)
  → State r
  → k
  → v
  → ST r Unit
insertSourceRange getRaw state k v = MutableArray.poke k v (getRaw state)

insertExprSourceRange ∷ ∀ r. State r → SST.ExprIndex → CST.SourceRange → ST r Unit
insertExprSourceRange = insertSourceRange \(State { exprSourceRange }) → exprSourceRange

insertBinderSourceRange ∷ ∀ r. State r → SST.BinderIndex → CST.SourceRange → ST r Unit
insertBinderSourceRange = insertSourceRange \(State { binderSourceRange }) → binderSourceRange

insertTypeSourceRange ∷ ∀ r. State r → SST.TypeIndex → CST.SourceRange → ST r Unit
insertTypeSourceRange = insertSourceRange \(State { typeSourceRange }) → typeSourceRange

insertLetBindingSourceRange
  ∷ ∀ r. State r → SST.LetBindingIndex → LetBindingSourceRange → ST r Unit
insertLetBindingSourceRange =
  insertSourceRange \(State { letBindingSourceRange }) → letBindingSourceRange

insertConstructorSourceRange
  ∷ ∀ r. State r → SST.ConstructorIndex → CST.SourceRange → ST r Unit
insertConstructorSourceRange =
  insertSourceRange \(State { constructorSourceRange }) → constructorSourceRange

insertNewtypeSourceRange ∷ ∀ r. State r → SST.NewtypeIndex → CST.SourceRange → ST r Unit
insertNewtypeSourceRange = insertSourceRange \(State { newtypeSourceRange }) → newtypeSourceRange

insertClassMethodSourceRange
  ∷ ∀ r. State r → SST.ClassMethodIndex → CST.SourceRange → ST r Unit
insertClassMethodSourceRange =
  insertSourceRange \(State { classMethodSourceRange }) → classMethodSourceRange

insertDeclarationSourceRange
  ∷ ∀ r. State r → SST.DeclarationIndex → DeclarationSourceRange → ST r Unit
insertDeclarationSourceRange =
  insertSourceRange \(State { declarationSourceRange }) → declarationSourceRange

unName ∷ ∀ a. CST.Name a → a
unName (CST.Name { name }) = name

lowerQualifiedName ∷ ∀ a. CST.QualifiedName a → SST.QualifiedName a
lowerQualifiedName (CST.QualifiedName { module: moduleName, name }) =
  SST.QualifiedName { moduleName, name }

lowerGuarded ∷ ∀ r. State r → CST.Guarded Void → ST r SST.Guarded
lowerGuarded state = case _ of
  CST.Unconditional _ w → SST.Unconditional <$> lowerWhere state w
  CST.Guarded g → SST.Guarded <$> traverse (lowerGuardedExpr state) g

lowerGuardedExpr ∷ ∀ r. State r → CST.GuardedExpr Void → ST r SST.GuardedExpr
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

lowerPatternGuard ∷ ∀ r. State r → CST.PatternGuard Void → ST r SST.PatternGuard
lowerPatternGuard state (CST.PatternGuard { binder: cstBinder, expr: cstExpr }) = do
  binder ← cstBinder # traverse case _ of
    Tuple cstBinder' _ → lowerBinder state cstBinder'
  expr ← lowerExpr state cstExpr
  pure $ SST.PatternGuard binder expr

lowerWhere ∷ ∀ r. State r → CST.Where Void → ST r SST.Where
lowerWhere state (CST.Where { expr: cstExpr, bindings: cstBindings }) = do
  expr ← lowerExpr state cstExpr
  bindings ← case cstBindings of
    Just (Tuple _ cstBindings') →
      NEA.toArray <$> lowerLetBindings state cstBindings'
    Nothing →
      pure []
  pure $ SST.Where expr bindings

lowerExpr ∷ ∀ r. State r → CST.Expr Void → ST r SST.Expr
lowerExpr state = runSTFn1 go
  where
  nextIndexWith ∷ CST.SourceRange → ST r SST.ExprIndex
  nextIndexWith range = do
    index ← nextExprIndex state
    insertExprSourceRange state index range
    pure index

  goAppSpine ∷ STFn1 (CST.AppSpine CST.Expr Void) r SST.AppSpine
  goAppSpine = mkSTFn1 case _ of
    CST.AppTerm e → SST.AppTerm <$> runSTFn1 go e
    CST.AppType _ t → SST.AppType <$> lowerType state t

  goRecordLabeled ∷ STFn1 (CST.RecordLabeled (CST.Expr Void)) r (SST.RecordLabeled SST.Expr)
  goRecordLabeled = mkSTFn1 case _ of
    CST.RecordPun (CST.Name { name }) → pure $ SST.RecordPun name
    CST.RecordField (CST.Name { name }) _ e → SST.RecordField name <$> runSTFn1 go e

  goChain ∷ ∀ a b. STFn2 (STFn1 a r b) (Tuple a (CST.Expr Void)) r (Tuple b SST.Expr)
  goChain = mkSTFn2 \onOperator (Tuple operator operand) →
    Tuple <$> runSTFn1 onOperator operator <*> runSTFn1 go operand

  goInfixOperator ∷ STFn1 (CST.Wrapped (CST.Expr Void)) r SST.Expr
  goInfixOperator = mkSTFn1 case _ of
    CST.Wrapped { value } → runSTFn1 go value

  goOperator ∷ STFn1 (CST.QualifiedName CST.Operator) r (SST.QualifiedName CST.Operator)
  goOperator = mkSTFn1 $ lowerQualifiedName >>> pure

  goRecordUpdate ∷ STFn1 (CST.RecordUpdate Void) r SST.RecordUpdate
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
        (Tuple (CST.Separated (CST.Binder Void)) (CST.Guarded Void))
        r
        (Tuple (NonEmptyArray SST.Binder) SST.Guarded)
  goCaseBranch = mkSTFn1 case _ of
    Tuple (CST.Separated { head: cstHead, tail: cstTail }) cstGuarded → do
      bindersHead ← lowerBinder state cstHead
      bindersTail ← traverse (Tuple.snd >>> lowerBinder state) cstTail
      let binders = NEA.cons' bindersHead bindersTail
      guarded ← lowerGuarded state cstGuarded
      pure $ Tuple binders guarded

  go ∷ STFn1 (CST.Expr Void) r SST.Expr
  go = mkSTFn1 \e → do
    let
      range ∷ CST.SourceRange
      range = rangeOf e
    index ← nextIndexWith range
    let
      annotation ∷ SST.ExprAnnotation
      annotation = SST.Annotation { index }
    insertExprSourceRange state index range
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
      CST.ExprError v → do
        absurd v

lowerBinder ∷ ∀ r. State r → CST.Binder Void → ST r SST.Binder
lowerBinder state = runSTFn1 go
  where
  nextIndexWith ∷ CST.SourceRange → ST r SST.BinderIndex
  nextIndexWith range = do
    index ← nextBinderIndex state
    insertBinderSourceRange state index range
    pure index

  goRecordLabeled ∷ STFn1 (CST.RecordLabeled (CST.Binder Void)) r (SST.RecordLabeled SST.Binder)
  goRecordLabeled = mkSTFn1 case _ of
    CST.RecordPun (CST.Name { name }) → pure $ SST.RecordPun name
    CST.RecordField (CST.Name { name }) _ e → SST.RecordField name <$> runSTFn1 go e

  goChain ∷ ∀ a b. STFn2 (STFn1 a r b) (Tuple a (CST.Binder Void)) r (Tuple b SST.Binder)
  goChain = mkSTFn2 \onOperator (Tuple operator operand) →
    Tuple <$> runSTFn1 onOperator operator <*> runSTFn1 go operand

  goOperator ∷ STFn1 (CST.QualifiedName CST.Operator) r (SST.QualifiedName CST.Operator)
  goOperator = mkSTFn1 $ lowerQualifiedName >>> pure

  go ∷ STFn1 (CST.Binder Void) r SST.Binder
  go = mkSTFn1 \b → do
    let
      range ∷ CST.SourceRange
      range = rangeOf b
    index ← nextIndexWith range
    let
      annotation ∷ SST.BinderAnnotation
      annotation = SST.Annotation { index }
    insertBinderSourceRange state index range
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
      CST.BinderError v →
        absurd v

lowerType ∷ ∀ r. State r → CST.Type Void → ST r SST.Type
lowerType state = runSTFn1 go
  where
  nextIndexWith ∷ CST.SourceRange → ST r SST.TypeIndex
  nextIndexWith range = do
    index ← nextTypeIndex state
    insertTypeSourceRange state index range
    pure index

  goRowPair
    ∷ STFn1
        (CST.Labeled (CST.Name CST.Label) (CST.Type Void))
        r
        (Tuple CST.Label SST.Type)
  goRowPair = mkSTFn1 case _ of
    CST.Labeled { label: (CST.Name { name: cstLabel }), value: cstValue } →
      Tuple cstLabel <$> runSTFn1 go cstValue

  goRow ∷ STFn1 (CST.Wrapped (CST.Row Void)) r SST.Row
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
      pure $ SST.Row labels tail

  goChain ∷ ∀ a b. STFn2 (STFn1 a r b) (Tuple a (CST.Type Void)) r (Tuple b SST.Type)
  goChain = mkSTFn2 \onOperator (Tuple operator operand) →
    Tuple <$> runSTFn1 onOperator operator <*> runSTFn1 go operand

  goOperator ∷ STFn1 (CST.QualifiedName CST.Operator) r (SST.QualifiedName CST.Operator)
  goOperator = mkSTFn1 $ lowerQualifiedName >>> pure

  go ∷ STFn1 (CST.Type Void) r SST.Type
  go = mkSTFn1 \t → do
    let
      range ∷ CST.SourceRange
      range = rangeOf t
    index ← nextIndexWith range
    let
      annotation ∷ SST.TypeAnnotation
      annotation = SST.Annotation { index }
    insertTypeSourceRange state index range
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
      CST.TypeError v →
        absurd v

data LetLoweringGroup r = LetLoweringGroup
  CST.Ident
  (STRef r (Maybe { sourceRange ∷ CST.SourceRange, t ∷ SST.Type }))
  (STArray r { sourceRange ∷ CST.SourceRange, v ∷ SST.ValueEquation })

lowerLetBindings
  ∷ ∀ r. State r → NonEmptyArray (CST.LetBinding Void) → ST r (NonEmptyArray SST.LetBinding)
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
          index ← nextLetBindingIndex state
          let
            annotation ∷ SST.LetBindingAnnotation
            annotation = SST.Annotation { index }
          insertLetBindingSourceRange state index letBindingSourceRange
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
        index ← nextLetBindingIndex state
        let
          annotation ∷ SST.LetBindingAnnotation
          annotation = SST.Annotation { index }
        insertLetBindingSourceRange state index letBindingSourceRange
        sstBinder ← lowerBinder state cstBinder
        sstWhere ← lowerWhere state cstWhere
        let
          letBinding ∷ SST.LetBinding
          letBinding = SST.LetBindingPattern annotation sstBinder sstWhere
        void $ STA.push letBinding letBindingsRaw
      CST.LetBindingError v →
        absurd v

  dischargeGroup
  letBindings ← STA.unsafeFreeze letBindingsRaw
  pure $ NonEmptyArray letBindings

-- TODO: It might be useful to assign indices to do statements, like we do with let bindings,
-- so we keep the shape similar to other lowerX functions. For instance, indices could improve
-- error reporting for do blocks since we can recover the entire statement rather than just the
-- let binding.
lowerDoStatement ∷ ∀ r. State r → CST.DoStatement Void → ST r SST.DoStatement
lowerDoStatement state = runSTFn1 go
  where
  go ∷ STFn1 (CST.DoStatement Void) r SST.DoStatement
  go = mkSTFn1 \d → do
    case d of
      CST.DoLet _ cstLetBindings → do
        SST.DoLet <$> lowerLetBindings state cstLetBindings
      CST.DoDiscard cstExpr → do
        SST.DoDiscard <$> lowerExpr state cstExpr
      CST.DoBind cstBinder _ cstExpr → do
        SST.DoBind <$> lowerBinder state cstBinder <*> lowerExpr state cstExpr
      CST.DoError e →
        absurd e

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
  ∷ ∀ r. Maybe (CST.DelimitedNonEmpty (CST.Export Void)) → ST r (Maybe (NonEmptyArray SST.Export))
lowerExports cstExports = for cstExports case _ of
  CST.Wrapped { value: CST.Separated { head: headExport, tail } } → do
    let
      lowerExport ∷ CST.Export Void → SST.Export
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
        CST.ExportError v →
          absurd v

    exportsRaw ← STA.new

    void $ STA.push (lowerExport headExport) exportsRaw
    for_ tail \(Tuple _ tailExport) → do
      void $ STA.push (lowerExport tailExport) exportsRaw

    exports ← STA.freeze exportsRaw
    pure $ NonEmptyArray exports

lowerImportDecls ∷ ∀ r. Array (CST.ImportDecl Void) → ST r (Array SST.Import)
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

lowerDataCtor ∷ ∀ r. State r → CST.DataCtor Void → ST r SST.DataConstructor
lowerDataCtor state dataCtor = do
  index ← nextConstructorIndex state
  let
    sourceRange ∷ CST.SourceRange
    sourceRange = rangeOf dataCtor
  insertConstructorSourceRange state index sourceRange
  let
    annotation ∷ SST.ConstructorAnnotation
    annotation = SST.Annotation { index }
  case dataCtor of
    CST.DataCtor { name: CST.Name { name }, fields: cstFields } → do
      fields ← traverse (lowerType state) cstFields
      pure $ SST.DataConstructor { annotation, name, fields }

lowerTypeVarBindings_
  ∷ ∀ t i r
  . Traversable t
  ⇒ (i → { visible ∷ Boolean, name ∷ CST.Ident })
  → State r
  → t (CST.TypeVarBinding i Void)
  → ST r (t SST.TypeVarBinding)
lowerTypeVarBindings_ un state = traverse case _ of
  CST.TypeVarKinded (CST.Wrapped { value: CST.Labeled { label, value } }) → do
    let { visible, name } = un label
    SST.TypeVarKinded visible name <$> lowerType state value
  CST.TypeVarName cstName → do
    let { visible, name } = un cstName
    pure $ SST.TypeVarName visible name

lowerTypeVarBindings
  ∷ ∀ t r
  . Traversable t
  ⇒ State r
  → t (CST.TypeVarBinding (CST.Name CST.Ident) Void)
  → ST r (t SST.TypeVarBinding)
lowerTypeVarBindings = lowerTypeVarBindings_ case _ of
  CST.Name { name } → { visible: false, name }

lowerTypeVarBindingsPrefixed
  ∷ ∀ t r
  . Traversable t
  ⇒ State r
  → t (CST.TypeVarBinding (CST.Prefixed (CST.Name CST.Ident)) Void)
  → ST r (t SST.TypeVarBinding)
lowerTypeVarBindingsPrefixed = lowerTypeVarBindings_ case _ of
  CST.Prefixed { prefix, value: CST.Name { name } } → { visible: isJust prefix, name }

lowerDataEquation
  ∷ ∀ r
  . State r
  → CST.DataHead Void
  → Maybe (Tuple CST.SourceToken (CST.Separated (CST.DataCtor Void)))
  → ST r SST.DataEquation
lowerDataEquation state { vars } cstConstructors = do
  variables ← lowerTypeVarBindings state vars
  constructors ← for cstConstructors case _ of
    Tuple _ (CST.Separated { head, tail }) → do
      sstHead ← lowerDataCtor state head
      sstTail ← traverse (Tuple.snd >>> lowerDataCtor state) tail
      pure $ NEA.cons' sstHead sstTail
  pure $ SST.DataEquation { variables, constructors }

lowerTypeEquation ∷ ∀ r. State r → CST.DataHead Void → CST.Type Void → ST r SST.TypeEquation
lowerTypeEquation state { vars } cstType = do
  variables ← lowerTypeVarBindings state vars
  synonymTo ← lowerType state cstType
  pure $ SST.TypeEquation { variables, synonymTo }

lowerNewtypeEquation
  ∷ ∀ r
  . State r
  → CST.DataHead Void
  → CST.Name CST.Proper
  → CST.Type Void
  → ST r SST.NewtypeEquation
lowerNewtypeEquation state { vars } cstName@(CST.Name { name }) cstField = do
  index ← nextNewtypeIndex state
  let
    sourceRange ∷ CST.SourceRange
    sourceRange =
      { start: rangeOf cstName # _.start
      , end: rangeOf cstField # _.end
      }
  insertNewtypeSourceRange state index sourceRange
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

type CSTClassMethod =
  CST.Labeled (CST.Name CST.Ident) (CST.Type Void)

lowerClassMethod ∷ ∀ r. State r → CSTClassMethod → ST r SST.ClassMethod
lowerClassMethod state cstClassMethod = do
  index ← nextClassMethodIndex state
  let
    sourceRange ∷ CST.SourceRange
    sourceRange = rangeOf cstClassMethod
  insertClassMethodSourceRange state index sourceRange
  let
    annotation ∷ SST.ClassMethodAnnotation
    annotation = SST.Annotation { index }
  case cstClassMethod of
    CST.Labeled { label: CST.Name { name }, value } → do
      signature ← lowerType state value
      pure $ SST.ClassMethod { annotation, name, signature }

type CSTClassBody =
  Tuple CST.SourceToken (NonEmptyArray CSTClassMethod)

lowerClassBody ∷ ∀ r. State r → CST.ClassHead Void → Maybe CSTClassBody → ST r SST.ClassEquation
lowerClassBody state { vars } classBody = do
  variables ← lowerTypeVarBindings state vars
  methods ← for classBody case _ of
    Tuple _ classMethods →
      traverse (lowerClassMethod state) classMethods
  pure $ SST.ClassEquation { variables, methods }

lowerDeclarations ∷ ∀ r. State r → Array (CST.Declaration Void) → ST r (Array SST.Declaration)
lowerDeclarations state cstDeclarations = do
  declarationsRaw ← STA.new

  let
    signatureNameGroups ∷ Array (NonEmptyArray (CST.Declaration Void))
    signatureNameGroups = Array.groupBy bySignatureName cstDeclarations

    onTypeGroup ∷ CST.Proper → _ → _ → ST r Unit
    onTypeGroup cstName cstSignature cstDeclaration = do
      index ← nextDeclarationIndex state
      let
        declarationSourceRange ∷ DeclarationSourceRange
        declarationSourceRange = DeclarationValueSourceRange
          { signature: cstSignature <#> rangeOf
          , definitions: cstDeclaration <#> rangeOf
          }
      insertDeclarationSourceRange state index declarationSourceRange

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
      index ← nextDeclarationIndex state
      let
        declarationSourceRange ∷ DeclarationSourceRange
        declarationSourceRange = DeclarationValueSourceRange
          { signature: cstSignature <#> rangeOf
          , definitions: cstValues <#> rangeOf
          }
      insertDeclarationSourceRange state index declarationSourceRange

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
        _ →
          pure unit

  STA.freeze declarationsRaw

type ModuleWithSourceRanges =
  { surface ∷ SST.Module
  , sourceRanges ∷ SourceRanges
  }

lowerModule ∷ ∀ r. CST.Module Void → ST r ModuleWithSourceRanges
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
  sourceRanges ← freezeState state
  pure { surface, sourceRanges }
