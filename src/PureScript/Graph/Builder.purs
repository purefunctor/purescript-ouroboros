module PureScript.Graph.Builder where

import Prelude

import Control.Monad.ST.Global (Global)
import Control.Monad.ST.Global as STGlobal
import Data.Array.ST (STArray)
import Data.Array.ST as STArray
import Data.Array.ST.Partial as STArrayPartial
import Data.Traversable (traverse)
import Effect (Effect)
import Partial.Unsafe (unsafePartial)
import PureScript.Graph (Graph(..), Index(..))

type State a =
  { vertices ∷ STArray Global a
  , edges ∷ STArray Global (STArray Global Int)
  }

newtype GraphBuilder a = GraphBuilder (State a)

initialize ∷ ∀ a. Effect (GraphBuilder a)
initialize = do
  vertices ← STGlobal.toEffect STArray.new
  edges ← STGlobal.toEffect STArray.new
  pure $ GraphBuilder { vertices, edges }

addVertex ∷ ∀ a. GraphBuilder a → a → Effect (Index a)
addVertex (GraphBuilder { vertices, edges }) vertex = STGlobal.toEffect do
  edge ← STArray.new
  index ← STArray.push vertex vertices
  _ ← STArray.push edge edges
  pure $ Index $ index - 1

addEdge ∷ ∀ a. GraphBuilder a → Index a → Index a → Effect Unit
addEdge (GraphBuilder { edges }) (Index from) (Index to) = STGlobal.toEffect do
  edge ← unsafePartial $ STArrayPartial.peek from edges
  _ ← STArray.push to edge
  pure unit

build ∷ ∀ a. GraphBuilder a → Effect (Graph a)
build (GraphBuilder { vertices, edges }) = STGlobal.toEffect do
  vertices' ← STArray.freeze vertices
  edges' ← STArray.freeze edges >>= traverse STArray.freeze
  pure $ Graph { vertices: vertices', edges: edges' }
