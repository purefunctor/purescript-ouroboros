module PureScript.Surface.Lower where

import Prelude

import Control.Monad.ST.Global (Global)
import Control.Monad.ST.Global as STG
import Data.Array as Array
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NEA
import Data.Array.ST (STArray)
import Data.Array.ST as STA
import Data.Array.ST.Partial as STAP
import Data.Maybe (Maybe(..), isJust)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Data.Tuple as Tuple
import Effect (Effect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Effect.Uncurried (EffectFn1, EffectFn2, mkEffectFn1, mkEffectFn2, runEffectFn1, runEffectFn2)
import Partial.Unsafe (unsafePartial)
import PureScript.CST.Range (rangeOf)
import PureScript.CST.Types as CST
import PureScript.Surface.Types as SST

type StateIndex = Ref Int

type StateSourceRange = STArray Global CST.SourceRange

type State =
  { exprIndex ∷ StateIndex
  , binderIndex ∷ StateIndex
  , typeIndex ∷ StateIndex
  , letBindingIndex ∷ StateIndex
  , exprSourceRange ∷ StateSourceRange
  , binderSourceRange ∷ StateSourceRange
  , typeSourceRange ∷ StateSourceRange
  , letBindingSourceRange ∷ StateSourceRange
  }

defaultState ∷ Effect State
defaultState = do
  exprIndex ← Ref.new 0
  binderIndex ← Ref.new 0
  typeIndex ← Ref.new 0
  letBindingIndex ← Ref.new 0
  exprSourceRange ← STG.toEffect $ STA.new
  binderSourceRange ← STG.toEffect $ STA.new
  typeSourceRange ← STG.toEffect $ STA.new
  letBindingSourceRange ← STG.toEffect $ STA.new
  pure
    { exprIndex
    , binderIndex
    , typeIndex
    , letBindingIndex
    , exprSourceRange
    , binderSourceRange
    , typeSourceRange
    , letBindingSourceRange
    }

nextExprIndex ∷ State → Effect SST.ExprIndex
nextExprIndex { exprIndex } = do
  index ← Ref.read exprIndex
  Ref.modify_ (_ + 1) exprIndex
  pure $ SST.Index index

nextBinderIndex ∷ State → Effect SST.BinderIndex
nextBinderIndex { binderIndex } = do
  index ← Ref.read binderIndex
  Ref.modify_ (_ + 1) binderIndex
  pure $ SST.Index index

nextTypeIndex ∷ State → Effect SST.TypeIndex
nextTypeIndex { typeIndex } = do
  index ← Ref.read typeIndex
  Ref.modify_ (_ + 1) typeIndex
  pure $ SST.Index index

nextLetBindingIndex ∷ State → Effect SST.LetBindingIndex
nextLetBindingIndex { letBindingIndex } = do
  index ← Ref.read letBindingIndex
  Ref.modify_ (_ + 1) letBindingIndex
  pure $ SST.Index index

insertExprSourceRange ∷ State → SST.ExprIndex → CST.SourceRange → Effect Unit
insertExprSourceRange { exprSourceRange } (SST.Index exprIndex) exprRange = do
  unsafePartial $ STG.toEffect $ STAP.poke exprIndex exprRange exprSourceRange

insertBinderSourceRange ∷ State → SST.BinderIndex → CST.SourceRange → Effect Unit
insertBinderSourceRange { binderSourceRange } (SST.Index binderIndex) binderRange = do
  unsafePartial $ STG.toEffect $ STAP.poke binderIndex binderRange binderSourceRange

insertTypeSourceRange ∷ State → SST.TypeIndex → CST.SourceRange → Effect Unit
insertTypeSourceRange { typeSourceRange } (SST.Index typeIndex) typeRange = do
  unsafePartial $ STG.toEffect $ STAP.poke typeIndex typeRange typeSourceRange

insertLetBindingSourceRange ∷ State → SST.LetBindingIndex → CST.SourceRange → Effect Unit
insertLetBindingSourceRange { letBindingSourceRange } (SST.Index letBindingIndex) letBindingRange =
  unsafePartial $ STG.toEffect $ STAP.poke letBindingIndex letBindingRange letBindingSourceRange

lowerDeclaration ∷ State → CST.Declaration Void → Effect SST.Declaration
lowerDeclaration state = runEffectFn1 go
  where
  go ∷ EffectFn1 (CST.Declaration Void) SST.Declaration
  go = mkEffectFn1 \d → do
    case d of
      CST.DeclSignature (CST.Labeled { label: cstLabel, value: cstValue }) →
        SST.DeclarationSignature cstLabel <$> lowerType state cstValue
      CST.DeclValue { name: cstName, binders: cstBinders, guarded: cstGuarded } →
        SST.DeclarationValue cstName
          <$> traverse (lowerBinder state) cstBinders
          <*> lowerGuarded state cstGuarded
      CST.DeclError v →
        absurd v
      _ →
        pure $ SST.DeclarationNotImplemented

lowerGuarded ∷ State → CST.Guarded Void → Effect SST.Guarded
lowerGuarded state = case _ of
  CST.Unconditional _ w → SST.Unconditional <$> lowerWhere state w
  CST.Guarded g → SST.Guarded <$> traverse (lowerGuardedExpr state) g

lowerGuardedExpr ∷ State → CST.GuardedExpr Void → Effect SST.GuardedExpr
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

lowerPatternGuard ∷ State → CST.PatternGuard Void → Effect SST.PatternGuard
lowerPatternGuard state (CST.PatternGuard { binder: cstBinder, expr: cstExpr }) = do
  binder ← cstBinder # traverse case _ of
    Tuple cstBinder' _ → lowerBinder state cstBinder'
  expr ← lowerExpr state cstExpr
  pure $ SST.PatternGuard binder expr

lowerWhere ∷ State → CST.Where Void → Effect SST.Where
lowerWhere state (CST.Where { expr: cstExpr, bindings: cstBindings }) = do
  expr ← lowerExpr state cstExpr
  bindings ← case cstBindings of
    Just (Tuple _ cstBindings') →
      NEA.toArray <$> traverse (lowerLetBinding state) cstBindings'
    Nothing →
      pure []
  pure $ SST.Where expr bindings

lowerExpr ∷ State → CST.Expr Void → Effect SST.Expr
lowerExpr state = runEffectFn1 go
  where
  nextIndexWith ∷ CST.SourceRange → Effect SST.ExprIndex
  nextIndexWith range = do
    index ← nextExprIndex state
    insertExprSourceRange state index range
    pure index

  goAppSpine ∷ EffectFn1 (CST.AppSpine CST.Expr Void) SST.AppSpine
  goAppSpine = mkEffectFn1 case _ of
    CST.AppTerm e → SST.AppSpineTerm <$> runEffectFn1 go e
    CST.AppType _ _ → pure SST.AppSpineNotImplemented

  goRecordLabeled ∷ EffectFn1 (CST.RecordLabeled (CST.Expr Void)) (SST.RecordLabeled SST.Expr)
  goRecordLabeled = mkEffectFn1 case _ of
    CST.RecordPun n → pure $ SST.RecordPun n
    CST.RecordField l _ e → SST.RecordField l <$> runEffectFn1 go e

  goChain ∷ ∀ a b. EffectFn2 (EffectFn1 a b) (Tuple a (CST.Expr Void)) (Tuple b SST.Expr)
  goChain = mkEffectFn2 \onOperator (Tuple operator operand) →
    Tuple <$> runEffectFn1 onOperator operator <*> runEffectFn1 go operand

  goInfixOperator ∷ EffectFn1 (CST.Wrapped (CST.Expr Void)) SST.Expr
  goInfixOperator = mkEffectFn1 case _ of
    CST.Wrapped { value } → runEffectFn1 go value

  goOperator ∷ EffectFn1 (CST.QualifiedName CST.Operator) (CST.QualifiedName CST.Operator)
  goOperator = mkEffectFn1 pure

  goRecordUpdate ∷ EffectFn1 (CST.RecordUpdate Void) SST.RecordUpdate
  goRecordUpdate = mkEffectFn1 case _ of
    CST.RecordUpdateLeaf n _ e →
      SST.RecordUpdateLeaf n <$> runEffectFn1 go e
    CST.RecordUpdateBranch n
      (CST.Wrapped { value: (CST.Separated { head: cstHead, tail: cstTail }) }) → do
      head ← runEffectFn1 goRecordUpdate cstHead
      tail ← traverse (Tuple.snd >>> runEffectFn1 goRecordUpdate) cstTail
      pure $ SST.RecordUpdateBranch n $ NEA.cons' head tail

  goCaseBranch
    ∷ EffectFn1
        (Tuple (CST.Separated (CST.Binder Void)) (CST.Guarded Void))
        (Tuple (NonEmptyArray SST.Binder) SST.Guarded)
  goCaseBranch = mkEffectFn1 case _ of
    Tuple (CST.Separated { head: cstHead, tail: cstTail }) cstGuarded → do
      bindersHead ← lowerBinder state cstHead
      bindersTail ← traverse (Tuple.snd >>> lowerBinder state) cstTail
      let binders = NEA.cons' bindersHead bindersTail
      guarded ← lowerGuarded state cstGuarded
      pure $ Tuple binders guarded

  go ∷ EffectFn1 (CST.Expr Void) SST.Expr
  go = mkEffectFn1 \e → do
    let
      range ∷ CST.SourceRange
      range = rangeOf e
    index ← nextIndexWith range
    let
      annotation ∷ SST.ExprAnnotation
      annotation = SST.Annotation { index }
    insertExprSourceRange state index range
    case e of
      CST.ExprHole h → do
        pure $ SST.ExprHole annotation h
      CST.ExprSection _ → do
        pure $ SST.ExprSection annotation
      CST.ExprIdent i → do
        pure $ SST.ExprIdent annotation i
      CST.ExprConstructor c → do
        pure $ SST.ExprConstructor annotation c
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
            head ← runEffectFn1 go cstHead
            tail ← traverse (Tuple.snd >>> runEffectFn1 go) cstTail
            pure $ Array.cons head tail
          Nothing →
            pure []
        pure $ SST.ExprArray annotation values
      CST.ExprRecord (CST.Wrapped { value }) → do
        values ← case value of
          Just (CST.Separated { head: cstHead, tail: cstTail }) → do
            head ← runEffectFn1 goRecordLabeled cstHead
            tail ← traverse (Tuple.snd >>> runEffectFn1 goRecordLabeled) cstTail
            pure $ Array.cons head tail
          Nothing → do
            pure []
        pure $ SST.ExprRecord annotation values
      CST.ExprParens (CST.Wrapped { value }) → do
        SST.ExprParens annotation <$> runEffectFn1 go value
      CST.ExprTyped tm _ ty → do
        tm' ← runEffectFn1 go tm
        ty' ← lowerType state ty
        pure $ SST.ExprTyped annotation tm' ty'
      CST.ExprInfix cstTerm cstChain → do
        term ← runEffectFn1 go cstTerm
        chain ← traverse (runEffectFn2 goChain goInfixOperator) cstChain
        pure $ SST.ExprInfix annotation term chain
      CST.ExprOp cstTerm cstChain → do
        term ← runEffectFn1 go cstTerm
        chain ← traverse (runEffectFn2 goChain goOperator) cstChain
        pure $ SST.ExprOp annotation term chain
      CST.ExprOpName n → do
        pure $ SST.ExprOpName annotation n
      CST.ExprNegate _ n → do
        SST.ExprNegate annotation <$> runEffectFn1 go n
      CST.ExprRecordAccessor { expr: cstExpr, path: CST.Separated { head: cstHead, tail: cstTail } } →
        do
          expr ← runEffectFn1 go cstExpr
          let path = NEA.cons' cstHead (map Tuple.snd cstTail)
          pure $ SST.ExprRecordAccessor annotation expr path
      CST.ExprRecordUpdate cstExpr
        (CST.Wrapped { value: (CST.Separated { head: cstHead, tail: cstTail }) }) → do
        expr ← runEffectFn1 go cstExpr
        head ← runEffectFn1 goRecordUpdate cstHead
        tail ← traverse (Tuple.snd >>> runEffectFn1 goRecordUpdate) cstTail
        pure $ SST.ExprRecordUpdate annotation expr $ NEA.cons' head tail
      CST.ExprApp cstHead cstSpine → do
        head ← runEffectFn1 go cstHead
        spine ← traverse (runEffectFn1 goAppSpine) cstSpine
        pure $ SST.ExprApplication annotation head spine
      CST.ExprLambda { binders: cstBinders, body: cstBody } → do
        binders ← traverse (lowerBinder state) cstBinders
        body ← runEffectFn1 go cstBody
        pure $ SST.ExprLambda annotation binders body
      CST.ExprIf { cond: cstCond, true: cstWhen, false: cstUnless } → do
        cond ← runEffectFn1 go cstCond
        when ← runEffectFn1 go cstWhen
        unless ← runEffectFn1 go cstUnless
        pure $ SST.ExprIfThenElse annotation cond when unless
      CST.ExprCase { head: CST.Separated { head: cstHead, tail: cstTail }, branches: cstBranches } →
        do
          headHead ← runEffectFn1 go cstHead
          headTail ← traverse (Tuple.snd >>> runEffectFn1 go) cstTail
          let head = NEA.cons' headHead headTail
          branches ← traverse (runEffectFn1 goCaseBranch) cstBranches
          pure $ SST.ExprCase annotation head branches
      CST.ExprLet { bindings: cstBindings, body: cstBody } → do
        bindings ← traverse (lowerLetBinding state) cstBindings
        body ← runEffectFn1 go cstBody
        pure $ SST.ExprLet annotation bindings body
      CST.ExprDo { statements: cstStatements } → do
        SST.ExprDo annotation <$> traverse (lowerDoStatement state) cstStatements
      CST.ExprAdo { statements: cstStatements, result: cstResult } → do
        SST.ExprAdo annotation <$> traverse (lowerDoStatement state) cstStatements <*> runEffectFn1
          go
          cstResult
      CST.ExprError v → do
        absurd v

lowerBinder ∷ State → CST.Binder Void → Effect SST.Binder
lowerBinder state = runEffectFn1 go
  where
  nextIndexWith ∷ CST.SourceRange → Effect SST.BinderIndex
  nextIndexWith range = do
    index ← nextBinderIndex state
    insertBinderSourceRange state index range
    pure index

  goRecordLabeled ∷ EffectFn1 (CST.RecordLabeled (CST.Binder Void)) (SST.RecordLabeled SST.Binder)
  goRecordLabeled = mkEffectFn1 case _ of
    CST.RecordPun n → pure $ SST.RecordPun n
    CST.RecordField l _ e → SST.RecordField l <$> runEffectFn1 go e

  goChain ∷ ∀ a b. EffectFn2 (EffectFn1 a b) (Tuple a (CST.Binder Void)) (Tuple b SST.Binder)
  goChain = mkEffectFn2 \onOperator (Tuple operator operand) →
    Tuple <$> runEffectFn1 onOperator operator <*> runEffectFn1 go operand

  goOperator ∷ EffectFn1 (CST.QualifiedName CST.Operator) (CST.QualifiedName CST.Operator)
  goOperator = mkEffectFn1 pure

  go ∷ EffectFn1 (CST.Binder Void) SST.Binder
  go = mkEffectFn1 \b → do
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
      CST.BinderVar n →
        pure $ SST.BinderVar annotation n
      CST.BinderNamed n _ i →
        SST.BinderNamed annotation n <$> runEffectFn1 go i
      CST.BinderConstructor n a →
        SST.BinderConstructor annotation n <$> traverse (runEffectFn1 go) a
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
            valueHead ← runEffectFn1 go cstValueHead
            valueTail ← traverse (Tuple.snd >>> runEffectFn1 go) cstValueTail
            pure $ Array.cons valueHead valueTail
          Nothing →
            pure []
        pure $ SST.BinderArray annotation values
      CST.BinderRecord (CST.Wrapped { value: cstValues }) → do
        values ← case cstValues of
          Just (CST.Separated { head: cstValueHead, tail: cstValueTail }) → do
            valueHead ← runEffectFn1 goRecordLabeled cstValueHead
            valueTail ← traverse (Tuple.snd >>> runEffectFn1 goRecordLabeled) cstValueTail
            pure $ Array.cons valueHead valueTail
          Nothing →
            pure []
        pure $ SST.BinderRecord annotation values
      CST.BinderParens (CST.Wrapped { value }) → do
        SST.BinderParens annotation <$> runEffectFn1 go value
      CST.BinderTyped i _ t → do
        SST.BinderTyped annotation <$> runEffectFn1 go i <*> lowerType state t
      CST.BinderOp cstHead cstChain →
        SST.BinderOp annotation
          <$> runEffectFn1 go cstHead
          <*> traverse (runEffectFn2 goChain goOperator) cstChain
      CST.BinderError v →
        absurd v

lowerType ∷ State → CST.Type Void → Effect SST.Type
lowerType state = runEffectFn1 go
  where
  nextIndexWith ∷ CST.SourceRange → Effect SST.TypeIndex
  nextIndexWith range = do
    index ← nextTypeIndex state
    insertTypeSourceRange state index range
    pure index

  goLabeled ∷ ∀ a. EffectFn1 (CST.Labeled a (CST.Type Void)) (Tuple a SST.Type)
  goLabeled = mkEffectFn1 case _ of
    CST.Labeled { label: cstLabel, value: cstValue } →
      Tuple cstLabel <$> runEffectFn1 go cstValue

  goRow ∷ EffectFn1 (CST.Wrapped (CST.Row Void)) SST.Row
  goRow = mkEffectFn1 case _ of
    CST.Wrapped { value: CST.Row { labels: cstLabels, tail: cstTail } } → do
      labels ← case cstLabels of
        Just (CST.Separated { head: cstLabelsHead, tail: cstLabelsTail }) → do
          labelsHead ← runEffectFn1 goLabeled cstLabelsHead
          labelsTail ← traverse (Tuple.snd >>> runEffectFn1 goLabeled) cstLabelsTail
          pure $ Array.cons labelsHead labelsTail
        Nothing →
          pure []
      tail ← traverse (Tuple.snd >>> lowerType state) cstTail
      pure $ SST.Row labels tail

  goBinding
    ∷ EffectFn1
        (CST.TypeVarBinding (CST.Prefixed (CST.Name CST.Ident)) Void)
        (SST.TypeVarBinding (CST.Name CST.Ident))
  goBinding = mkEffectFn1 case _ of
    CST.TypeVarKinded (CST.Wrapped { value: cstValue }) → do
      Tuple (CST.Prefixed { value: n }) v ← runEffectFn1 goLabeled cstValue
      pure $ SST.TypeVarKinded n v
    CST.TypeVarName (CST.Prefixed { value: n }) →
      pure $ SST.TypeVarName n

  goChain ∷ ∀ a b. EffectFn2 (EffectFn1 a b) (Tuple a (CST.Type Void)) (Tuple b SST.Type)
  goChain = mkEffectFn2 \onOperator (Tuple operator operand) →
    Tuple <$> runEffectFn1 onOperator operator <*> runEffectFn1 go operand

  goOperator ∷ EffectFn1 (CST.QualifiedName CST.Operator) (CST.QualifiedName CST.Operator)
  goOperator = mkEffectFn1 pure

  go ∷ EffectFn1 (CST.Type Void) SST.Type
  go = mkEffectFn1 \t → do
    let
      range ∷ CST.SourceRange
      range = rangeOf t
    index ← nextIndexWith range
    let
      annotation ∷ SST.TypeAnnotation
      annotation = SST.Annotation { index }
    insertTypeSourceRange state index range
    case t of
      CST.TypeVar v →
        pure $ SST.TypeVar annotation v
      CST.TypeConstructor c →
        pure $ SST.TypeConstructor annotation c
      CST.TypeWildcard _ →
        pure $ SST.TypeWildcard annotation
      CST.TypeHole h →
        pure $ SST.TypeHole annotation h
      CST.TypeString _ s →
        pure $ SST.TypeString annotation s
      CST.TypeInt n _ i →
        pure $ SST.TypeInt annotation (isJust n) i
      CST.TypeRow r → do
        SST.TypeRow annotation <$> runEffectFn1 goRow r
      CST.TypeRecord r → do
        SST.TypeRecord annotation <$> runEffectFn1 goRow r
      CST.TypeForall _ cstBindings _ cstBody → do
        bindings ← traverse (runEffectFn1 goBinding) cstBindings
        body ← runEffectFn1 go cstBody
        pure $ SST.TypeForall annotation bindings body
      CST.TypeKinded cstType _ cstKind →
        SST.TypeKinded annotation
          <$> runEffectFn1 go cstType
          <*> runEffectFn1 go cstKind
      CST.TypeApp cstType cstArguments →
        SST.TypeApp annotation
          <$> runEffectFn1 go cstType
          <*> traverse (runEffectFn1 go) cstArguments
      CST.TypeOp cstHead cstChain →
        SST.TypeOp annotation
          <$> runEffectFn1 go cstHead
          <*> traverse (runEffectFn2 goChain goOperator) cstChain
      CST.TypeOpName n →
        pure $ SST.TypeOpName annotation n
      CST.TypeArrow cstArgument _ cstReturn →
        SST.TypeArrow annotation
          <$> runEffectFn1 go cstArgument
          <*> runEffectFn1 go cstReturn
      CST.TypeArrowName _ →
        pure $ SST.TypeArrowName annotation
      CST.TypeConstrained cstConstraint _ cstConstrained →
        SST.TypeConstrained annotation
          <$> runEffectFn1 go cstConstraint
          <*> runEffectFn1 go cstConstrained
      CST.TypeParens (CST.Wrapped { value }) →
        SST.TypeParens annotation <$> runEffectFn1 go value
      CST.TypeError v →
        absurd v

lowerLetBinding ∷ State → CST.LetBinding Void → Effect SST.LetBinding
lowerLetBinding state = runEffectFn1 go
  where
  nextIndexWith ∷ CST.SourceRange → Effect SST.LetBindingIndex
  nextIndexWith range = do
    index ← nextLetBindingIndex state
    insertLetBindingSourceRange state index range
    pure index

  go ∷ EffectFn1 (CST.LetBinding Void) SST.LetBinding
  go = mkEffectFn1 \l → do
    let
      range ∷ CST.SourceRange
      range = rangeOf l
    index ← nextIndexWith range
    let
      annotation ∷ SST.LetBindingAnnotation
      annotation = SST.Annotation { index }
    insertLetBindingSourceRange state index range
    case l of
      CST.LetBindingSignature (CST.Labeled { label: cstLabel, value: cstType }) → do
        SST.LetBindingSignature annotation cstLabel <$> lowerType state cstType
      CST.LetBindingName { name: cstName, binders: cstBinders, guarded: cstGuarded } → do
        SST.LetBindingName annotation cstName
          <$> traverse (lowerBinder state) cstBinders
          <*> lowerGuarded state cstGuarded
      CST.LetBindingPattern cstBinder _ cstWhere → do
        SST.LetBindingPattern annotation
          <$> lowerBinder state cstBinder
          <*> lowerWhere state cstWhere
      CST.LetBindingError v →
        absurd v

-- TODO: It might be useful to assign indices to do statements, like we do with let bindings,
-- so we keep the shape similar to other lowerX functions. For instance, indices could improve
-- error reporting for do blocks since we can recover the entire statement rather than just the
-- let binding.
lowerDoStatement ∷ State → CST.DoStatement Void → Effect SST.DoStatement
lowerDoStatement state = runEffectFn1 go
  where
  go ∷ EffectFn1 (CST.DoStatement Void) SST.DoStatement
  go = mkEffectFn1 \d → do
    case d of
      CST.DoLet _ cstLetBindings → do
        SST.DoLet <$> traverse (lowerLetBinding state) cstLetBindings
      CST.DoDiscard cstExpr → do
        SST.DoDiscard <$> lowerExpr state cstExpr
      CST.DoBind cstBinder _ cstExpr → do
        SST.DoBind <$> lowerBinder state cstBinder <*> lowerExpr state cstExpr
      CST.DoError e →
        absurd e
