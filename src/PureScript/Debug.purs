module PureScript.Debug where

import Prelude

import Data.Function.Uncurried (Fn2, runFn2)

trace ∷ ∀ a b. a → (Unit → b) → b
trace a k = runFn2 _trace a k

foreign import _trace ∷ ∀ a b. Fn2 a (Unit → b) b

traceM ∷ ∀ m a. Monad m ⇒ a → m Unit
traceM s = do
  pure unit
  trace s \_ → pure unit
