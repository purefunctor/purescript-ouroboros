module PureScript.Driver.GraphMap where

import Prelude

import Control.Monad.ST as ST
import Control.Monad.ST.Uncurried (STFn1, STFn3, mkSTFn1, runSTFn3)
import Data.Array.ST as STArray
import Data.Foldable (traverse_)
import Effect (Effect)
import PureScript.Utils.Mutable.JsMap (JsMap)
import PureScript.Utils.Mutable.JsMap as JsMap

newtype GraphMap a = GraphMap
  { internal ∷ JsMap a { edges ∷ JsMap a Unit }
  }

emptyGraphMap ∷ ∀ a. Effect (GraphMap a)
emptyGraphMap = do
  internal ← JsMap.empty
  pure $ GraphMap { internal }

addNode ∷ ∀ a. GraphMap a → a → Effect Unit
addNode (GraphMap { internal }) node = do
  edges ← JsMap.empty
  JsMap.set node { edges } internal

hasNode ∷ ∀ a. GraphMap a → a → Effect Boolean
hasNode (GraphMap { internal }) node =
  JsMap.has node internal

addEdge ∷ ∀ a. GraphMap a → a → a → Effect Unit
addEdge (GraphMap { internal }) from to = do
  JsMap.get from internal >>= traverse_ \{ edges } →
    JsMap.set to unit edges

clearEdges ∷ ∀ a. GraphMap a → a → Effect Unit
clearEdges (GraphMap { internal }) node = do
  JsMap.get node internal >>= traverse_ \{ edges } →
    JsMap.clear edges

data SCC a = AcyclicSCC a | CyclicSCC (Array a)

derive instance Eq a ⇒ Eq (SCC a)

instance Show a ⇒ Show (SCC a) where
  show = case _ of
    AcyclicSCC i → "[AcyclicSCC " <> show i <> "]"
    CyclicSCC i → "[CyclicSCC " <> show i <> "]"

foreign import tarjanImpl
  ∷ ∀ a r
  . STFn3
      (JsMap a { edges ∷ JsMap a Unit })
      (STFn1 a r Unit)
      (STFn1 (Array a) r Unit)
      r
      Unit

tarjan ∷ ∀ a. GraphMap a → Array (SCC a)
tarjan (GraphMap { internal }) = ST.run do
  scc ← STArray.new

  let
    onAcyclic ∷ STFn1 a _ Unit
    onAcyclic = mkSTFn1 \key →
      void $ STArray.push (AcyclicSCC key) scc

    onCyclic ∷ STFn1 (Array a) _ Unit
    onCyclic = mkSTFn1 \component →
      void $ STArray.push (CyclicSCC component) scc

  runSTFn3 tarjanImpl internal onAcyclic onCyclic
  STArray.freeze scc
