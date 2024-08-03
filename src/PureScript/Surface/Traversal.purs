module PureScript.Surface.Traversal where

import Prelude
import Prim hiding (Row, Type)

import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import PureScript.Surface.Types
  ( AppSpine(..)
  , Binder(..)
  , ClassEquation(..)
  , ClassMethod(..)
  , DataConstructor(..)
  , DataEquation(..)
  , Declaration(..)
  , DoStatement(..)
  , Expr(..)
  , Guarded(..)
  , GuardedExpr(..)
  , LetBinding(..)
  , Module(..)
  , NewtypeConstructor(..)
  , NewtypeEquation(..)
  , PatternGuard(..)
  , RecordLabeled(..)
  , RecordUpdate(..)
  , Row(..)
  , Type(..)
  , TypeEquation(..)
  , TypeVarBinding(..)
  , ValueEquation(..)
  , Where(..)
  )
import Type.Row (type (+))

type Rewrite f t = t → f t

type OnBinder (t ∷ Prim.Type → Prim.Type) r = (onBinder ∷ t Binder | r)
type OnDeclaration (t ∷ Prim.Type → Prim.Type) r = (onDeclaration ∷ t Declaration | r)
type OnExpr (t ∷ Prim.Type → Prim.Type) r = (onExpr ∷ t Expr | r)
type OnType (t ∷ Prim.Type → Prim.Type) r = (onType ∷ t Type | r)

type OnPureScript t =
  ( OnBinder t
      + OnDeclaration t
      + OnExpr t
      + OnType t
      + ()
  )

defaultVisitorM ∷ ∀ f. Applicative f ⇒ { | OnPureScript (Rewrite f) }
defaultVisitorM =
  { onBinder: pure
  , onDeclaration: pure
  , onExpr: pure
  , onType: pure
  }

traverseTuple ∷ ∀ a b m. Monad m ⇒ (a → m a) → (b → m b) → Rewrite m (Tuple a b)
traverseTuple f g (Tuple a b) = Tuple <$> f a <*> g b

traverseModule ∷ ∀ m. Monad m ⇒ { | OnPureScript (Rewrite m) } → Rewrite m Module
traverseModule k (Module m) = do
  declarations' ← traverse (traverseDeclaration k) m.declarations
  pure $ Module $ m { declarations = declarations' }

traverseDeclaration ∷ ∀ m. Monad m ⇒ { | OnPureScript (Rewrite m) } → Rewrite m Declaration
traverseDeclaration k d = case d of
  DeclarationData i n t e →
    DeclarationData i n <$> traverse k.onType t <*> traverseDataEquation k e
  DeclarationType i n t e →
    DeclarationType i n <$> traverse k.onType t <*> traverseTypeEquation k e
  DeclarationNewtype i n t e →
    DeclarationNewtype i n <$> traverse k.onType t <*> traverseNewtypeEquation k e
  DeclarationClass i n t e →
    DeclarationClass i n <$> traverse k.onType t <*> traverseClassEquation k e
  DeclarationValue i n t e →
    DeclarationValue i n <$> traverse k.onType t <*> traverse (traverseValueEquation k) e
  DeclarationNotImplemented _ →
    pure d

traverseDataEquation ∷ ∀ m. Monad m ⇒ { | OnPureScript (Rewrite m) } → Rewrite m DataEquation
traverseDataEquation k (DataEquation { variables, constructors }) = do
  variables' ← traverse (traverseTypeVarBinding k) variables
  constructors' ← traverse (traverse (traverseDataConstructor k)) constructors
  pure $ DataEquation { variables: variables', constructors: constructors' }

traverseDataConstructor ∷ ∀ m. Monad m ⇒ { | OnPureScript (Rewrite m) } → Rewrite m DataConstructor
traverseDataConstructor k (DataConstructor { annotation, name, fields }) = do
  fields' ← traverse k.onType fields
  pure $ DataConstructor { annotation, name, fields: fields' }

traverseTypeEquation ∷ ∀ m. Monad m ⇒ { | OnPureScript (Rewrite m) } → Rewrite m TypeEquation
traverseTypeEquation k (TypeEquation { variables, synonymTo }) = do
  variables' ← traverse (traverseTypeVarBinding k) variables
  synonymTo' ← k.onType synonymTo
  pure $ TypeEquation { variables: variables', synonymTo: synonymTo' }

traverseNewtypeEquation ∷ ∀ m. Monad m ⇒ { | OnPureScript (Rewrite m) } → Rewrite m NewtypeEquation
traverseNewtypeEquation k (NewtypeEquation { variables, constructor }) = do
  variables' ← traverse (traverseTypeVarBinding k) variables
  constructor' ← traverseNewtypeConstructor k constructor
  pure $ NewtypeEquation { variables: variables', constructor: constructor' }

traverseNewtypeConstructor
  ∷ ∀ m. Monad m ⇒ { | OnPureScript (Rewrite m) } → Rewrite m NewtypeConstructor
traverseNewtypeConstructor k (NewtypeConstructor { annotation, name, field }) = do
  field' ← k.onType field
  pure $ NewtypeConstructor { annotation, name, field: field' }

traverseClassEquation ∷ ∀ m. Monad m ⇒ { | OnPureScript (Rewrite m) } → Rewrite m ClassEquation
traverseClassEquation k (ClassEquation { variables, methods }) = do
  variables' ← traverse (traverseTypeVarBinding k) variables
  methods' ← traverse (traverse (traverseClassMethod k)) methods
  pure $ ClassEquation { variables: variables', methods: methods' }

traverseClassMethod ∷ ∀ m. Monad m ⇒ { | OnPureScript (Rewrite m) } → Rewrite m ClassMethod
traverseClassMethod k (ClassMethod { annotation, name, signature }) = do
  signature' ← k.onType signature
  pure $ ClassMethod { annotation, name, signature: signature' }

traverseValueEquation ∷ ∀ m. Monad m ⇒ { | OnPureScript (Rewrite m) } → Rewrite m ValueEquation
traverseValueEquation k (ValueEquation { binders, guarded }) = do
  binders' ← traverse k.onBinder binders
  guarded' ← traverseGuarded k guarded
  pure $ ValueEquation { binders: binders', guarded: guarded' }

traverseGuarded ∷ ∀ m. Monad m ⇒ { | OnPureScript (Rewrite m) } → Rewrite m Guarded
traverseGuarded k = case _ of
  Unconditional w → Unconditional <$> traverseWhere k w
  Guarded g → Guarded <$> traverse (traverseGuardedExpr k) g

traverseWhere ∷ ∀ m. Monad m ⇒ { | OnPureScript (Rewrite m) } → Rewrite m Where
traverseWhere k (Where expr bindings) = do
  expr' ← k.onExpr expr
  bindings' ← traverse (traverseLetBinding k) bindings
  pure $ Where expr' bindings'

traverseGuardedExpr ∷ ∀ m. Monad m ⇒ { | OnPureScript (Rewrite m) } → Rewrite m GuardedExpr
traverseGuardedExpr k (GuardedExpr guards (Where expr bindings)) = do
  guards' ← traverse (traversePatternGuard k) guards
  expr' ← k.onExpr expr
  bindings' ← traverse (traverseLetBinding k) bindings
  pure $ GuardedExpr guards' (Where expr' bindings')

traversePatternGuard ∷ ∀ m. Monad m ⇒ { | OnPureScript (Rewrite m) } → Rewrite m PatternGuard
traversePatternGuard k (PatternGuard binder expr) = do
  binder' ← traverse k.onBinder binder
  expr' ← k.onExpr expr
  pure $ PatternGuard binder' expr'

traverseBinder ∷ ∀ m. Monad m ⇒ { | OnPureScript (Rewrite m) } → Rewrite m Binder
traverseBinder k = case _ of
  BinderNamed i n b →
    BinderNamed i n <$> k.onBinder b
  BinderConstructor i n b →
    BinderConstructor i n <$> traverse k.onBinder b
  BinderArray i v →
    BinderArray i <$> traverse k.onBinder v
  BinderRecord i v →
    BinderRecord i <$> traverse (traverseRecordLabeled k.onBinder) v
  BinderParens i b →
    BinderParens i <$> k.onBinder b
  BinderTyped i b t →
    BinderTyped i <$> k.onBinder b <*> k.onType t
  BinderOp i h t →
    BinderOp i <$> k.onBinder h <*> traverse (traverseTuple pure k.onBinder) t
  b →
    pure b

traverseExpr ∷ ∀ m. Monad m ⇒ { | OnPureScript (Rewrite m) } → Rewrite m Expr
traverseExpr k = case _ of
  ExprArray i v →
    ExprArray i <$> traverse k.onExpr v
  ExprRecord i v →
    ExprRecord i <$> traverse (traverseRecordLabeled k.onExpr) v
  ExprParens i e →
    ExprParens i <$> k.onExpr e
  ExprTyped i e t →
    ExprTyped i <$> k.onExpr e <*> k.onType t
  ExprInfix i h t →
    ExprInfix i <$> k.onExpr h <*> traverse (traverseTuple k.onExpr k.onExpr) t
  ExprOp i h t →
    ExprOp i <$> k.onExpr h <*> traverse (traverseTuple pure k.onExpr) t
  ExprNegate i e →
    ExprNegate i <$> k.onExpr e
  ExprRecordAccessor i e p →
    ExprRecordAccessor i <$> k.onExpr e <*> pure p
  ExprRecordUpdate i e p →
    ExprRecordUpdate i <$> k.onExpr e <*> traverse (traverseRecordUpdate k) p
  ExprApplication i f a →
    ExprApplication i <$> k.onExpr f <*> traverse (traverseAppSpine k) a
  ExprLambda i b e →
    ExprLambda i <$> traverse k.onBinder b <*> k.onExpr e
  ExprIfThenElse i c t e →
    ExprIfThenElse i <$> k.onExpr c <*> k.onExpr t <*> k.onExpr e
  ExprCase i h b →
    ExprCase i
      <$> traverse k.onExpr h
      <*> traverse (traverseTuple (traverse k.onBinder) (traverseGuarded k)) b
  ExprLet i b e →
    ExprLet i <$> traverse (traverseLetBinding k) b <*> k.onExpr e
  ExprDo i d →
    ExprDo i <$> traverse (traverseDoStatement k) d
  ExprAdo i d e →
    ExprAdo i <$> traverse (traverseDoStatement k) d <*> k.onExpr e
  e →
    pure e

traverseRecordLabeled ∷ ∀ t m. Monad m ⇒ (t → m t) → Rewrite m (RecordLabeled t)
traverseRecordLabeled f r = case r of
  RecordPun _ →
    pure r
  RecordField n v →
    RecordField n <$> f v

traverseRecordUpdate ∷ ∀ m. Monad m ⇒ { | OnPureScript (Rewrite m) } → Rewrite m RecordUpdate
traverseRecordUpdate k r = case r of
  RecordUpdateLeaf n v →
    RecordUpdateLeaf n <$> k.onExpr v
  RecordUpdateBranch n p →
    RecordUpdateBranch n <$> traverse (traverseRecordUpdate k) p

traverseAppSpine ∷ ∀ m. Monad m ⇒ { | OnPureScript (Rewrite m) } → Rewrite m AppSpine
traverseAppSpine k s = case s of
  AppTerm v →
    AppTerm <$> k.onExpr v
  AppType t →
    AppType <$> k.onType t

traverseDoStatement ∷ ∀ m. Monad m ⇒ { | OnPureScript (Rewrite m) } → Rewrite m DoStatement
traverseDoStatement k d = case d of
  DoLet i b →
    DoLet i <$> traverse (traverseLetBinding k) b
  DoDiscard i e →
    DoDiscard i <$> k.onExpr e
  DoBind i b e →
    DoBind i <$> k.onBinder b <*> k.onExpr e
  DoError _ →
    pure d
  DoNotImplemented _ →
    pure d

traverseLetBinding ∷ ∀ m. Monad m ⇒ { | OnPureScript (Rewrite m) } → Rewrite m LetBinding
traverseLetBinding k l = case l of
  LetBindingValue i n t e →
    LetBindingValue i n <$> traverse k.onType t <*> traverse (traverseValueEquation k) e
  LetBindingPattern i b w →
    LetBindingPattern i <$> k.onBinder b <*> traverseWhere k w
  LetBindingError _ →
    pure l
  LetBindingNotImplemented _ →
    pure l

traverseType ∷ ∀ m. Monad m ⇒ { | OnPureScript (Rewrite m) } → Rewrite m Type
traverseType k = case _ of
  TypeRow i r →
    TypeRow i <$> traverseRow k r
  TypeRecord i r →
    TypeRecord i <$> traverseRow k r
  TypeForall i v t →
    TypeForall i <$> traverse (traverseTypeVarBinding k) v <*> k.onType t
  TypeKinded i t c →
    TypeKinded i <$> k.onType t <*> k.onType c
  TypeApp i f a →
    TypeApp i <$> k.onType f <*> traverse k.onType a
  TypeOp i h t →
    TypeOp i <$> k.onType h <*> traverse (traverseTuple pure k.onType) t
  TypeArrow i a r →
    TypeArrow i <$> k.onType a <*> k.onType r
  TypeConstrained i c t →
    TypeConstrained i <$> k.onType c <*> k.onType t
  TypeParens i t →
    TypeParens i <$> k.onType t
  t →
    pure t

traverseRow ∷ ∀ m. Monad m ⇒ { | OnPureScript (Rewrite m) } → Rewrite m Row
traverseRow k (Row { labels, tail }) = do
  labels' ← traverse (traverseTuple pure k.onType) labels
  tail' ← traverse k.onType tail
  pure $ Row { labels: labels', tail: tail' }

traverseTypeVarBinding ∷ ∀ m. Monad m ⇒ { | OnPureScript (Rewrite m) } → Rewrite m TypeVarBinding
traverseTypeVarBinding k = case _ of
  TypeVarKinded i v n t →
    TypeVarKinded i v n <$> k.onType t
  TypeVarName i v n →
    pure $ TypeVarName i v n

topDownTraversal ∷ ∀ m. Monad m ⇒ { | OnPureScript (Rewrite m) } → { | OnPureScript (Rewrite m) }
topDownTraversal visitor = visitor'
  where
  visitor' ∷ { | OnPureScript (Rewrite m) }
  visitor' =
    { onBinder: \a → visitor.onBinder a >>= traverseBinder visitor'
    , onDeclaration: \a → visitor.onDeclaration a >>= traverseDeclaration visitor'
    , onExpr: \a → visitor.onExpr a >>= traverseExpr visitor'
    , onType: \a → visitor.onType a >>= traverseType visitor'
    }
