-- @inline export runReader arity=2
-- @inline export functorReader.map arity=2
-- @inline export applyReader.apply arity=2
-- @inline export applicativeReader.pure arity=1
-- @inline export bindReader.bind arity=2
-- @inline export monadSTReader.liftST arity=1
-- @inline export ask always
-- @inline export asks always
-- @inline export local always
module PureScript.Monad.Reader where

import Prelude

import Control.Monad.ST (ST)
import Control.Monad.ST.Class (class MonadST)
import Control.Monad.ST.Uncurried (STFn1, STFn2, mkSTFn1, mkSTFn2, runSTFn1, runSTFn2)

newtype Reader r e a = Reader (∀ c. STFn2 e (STFn1 a r c) r c)

instance functorReader ∷ Functor (Reader r e) where
  map f (Reader k) = Reader
    ( mkSTFn2 \e success →
        runSTFn2 k e
          ( mkSTFn1 \a →
              runSTFn1 success (f a)
          )
    )

instance applyReader ∷ Apply (Reader r e) where
  apply (Reader f) (Reader x) = Reader
    ( mkSTFn2 \e success →
        runSTFn2 f e
          ( mkSTFn1 \f' →
              runSTFn2 x e
                ( mkSTFn1 \x' →
                    runSTFn1 success (f' x')
                )
          )
    )

instance applicativeReader ∷ Applicative (Reader r e) where
  pure a = Reader
    ( mkSTFn2 \_ success →
        runSTFn1 success a
    )

instance bindReader ∷ Bind (Reader r e) where
  bind (Reader m) f = Reader
    ( mkSTFn2 \e success →
        runSTFn2 m e
          ( mkSTFn1 \a →
              case f a of
                Reader n →
                  runSTFn2 n e success
          )
    )

instance monadReader ∷ Monad (Reader r e)

instance monadSTReader ∷ MonadST r (Reader r e) where
  liftST m = Reader
    ( mkSTFn2 \_ success → do
        a ← m
        runSTFn1 success a
    )

ask ∷ ∀ r a. Reader r a a
ask = Reader
  ( mkSTFn2 \e success →
      runSTFn1 success e
  )

asks ∷ ∀ r e a. (e → a) → Reader r e a
asks = flip map ask

local ∷ ∀ r e a. (e → e) → Reader r e a → Reader r e a
local f (Reader k) = Reader
  ( mkSTFn2 \e success →
      runSTFn2 k (f e) success
  )

runReader ∷ ∀ r e a. Reader r e a → e → ST r a
runReader (Reader k) e = runSTFn2 k e (mkSTFn1 pure)
