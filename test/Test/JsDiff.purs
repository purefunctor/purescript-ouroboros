module Test.JsDiff where

import Effect (Effect)
import Effect.Uncurried (EffectFn2, runEffectFn2)

foreign import diffPatchImpl ∷ EffectFn2 String String String

diffPatch ∷ String → String → Effect String
diffPatch = runEffectFn2 diffPatchImpl
