module PureScript.Surface.Lower where

import Prelude

import Control.Monad.ST.Global (Global)
import Control.Monad.ST.Global as STG
import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Array.ST (STArray)
import Data.Array.ST as STA
import Data.Array.ST.Partial as STAP
import Data.Maybe (Maybe(..))
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

type State =
  { exprIndex ∷ Ref Int
  , typeIndex ∷ Ref Int
  , exprSourceRange ∷ STArray Global CST.SourceRange
  , typeSourceRange ∷ STArray Global CST.SourceRange
  }

defaultState ∷ Effect State
defaultState = do
  exprIndex ← Ref.new 0
  typeIndex ← Ref.new 0
  exprSourceRange ← STG.toEffect $ STA.new
  typeSourceRange ← STG.toEffect $ STA.new
  pure { exprIndex, typeIndex, exprSourceRange, typeSourceRange }

nextExprIndex ∷ State → Effect SST.ExprIndex
nextExprIndex { exprIndex } = do
  index ← Ref.read exprIndex
  Ref.modify_ (_ + 1) exprIndex
  pure $ SST.Index index

nextTypeIndex ∷ State → Effect SST.TypeIndex
nextTypeIndex { exprIndex } = do
  index ← Ref.read exprIndex
  Ref.modify_ (_ + 1) exprIndex
  pure $ SST.Index index

insertExprSourceRange ∷ State → SST.ExprIndex → CST.SourceRange → Effect Unit
insertExprSourceRange { exprSourceRange } (SST.Index exprIndex) exprRange = do
  unsafePartial $ STG.toEffect $ STAP.poke exprIndex exprRange exprSourceRange

insertTypeSourceRange ∷ State → SST.TypeIndex → CST.SourceRange → Effect Unit
insertTypeSourceRange { typeSourceRange } (SST.Index typeIndex) typeRange = do
  unsafePartial $ STG.toEffect $ STAP.poke typeIndex typeRange typeSourceRange

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
      CST.ExprRecordUpdate cstExpr (CST.Wrapped { value: (CST.Separated { head: cstHead, tail: cstTail })}) → do
        expr ← runEffectFn1 go cstExpr
        head <- runEffectFn1 goRecordUpdate cstHead
        tail <- traverse (Tuple.snd >>> runEffectFn1 goRecordUpdate) cstTail
        pure $ SST.ExprRecordUpdate annotation expr $ NEA.cons' head tail
      CST.ExprApp cstHead cstSpine → do
        head ← runEffectFn1 go cstHead
        spine ← traverse (runEffectFn1 goAppSpine) cstSpine
        pure $ SST.ExprApplication annotation head spine
      _ → do
        pure $ SST.ExprNotImplemented annotation

lowerType ∷ State → CST.Type Void → Effect SST.Type
lowerType state = runEffectFn1 go
  where
  nextIndexWith ∷ CST.SourceRange → Effect SST.TypeIndex
  nextIndexWith range = do
    index ← nextTypeIndex state
    insertTypeSourceRange state index range
    pure index

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
    pure $ SST.TypeNotImplemented annotation
