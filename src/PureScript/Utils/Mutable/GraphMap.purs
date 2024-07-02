module PureScript.Utils.Mutable.GraphMap where

import Prelude

import Control.Monad.ST (ST)
import Control.Monad.ST.Uncurried (STFn1, STFn3, mkSTFn1, runSTFn1, runSTFn3)
import Data.Array.ST (STArray)
import Data.Array.ST as STArray
import Data.Foldable (traverse_)
import PureScript.Utils.Mutable.JsMap (JsMap)
import PureScript.Utils.Mutable.JsMap as JsMap

newtype GraphMap r a = GraphMap
  { internal ∷ JsMap r a { edges ∷ JsMap r a Unit }
  }

emptyGraphMap ∷ ∀ r a. ST r (GraphMap r a)
emptyGraphMap = do
  internal ← JsMap.empty
  pure $ GraphMap { internal }

addNode ∷ ∀ r a. GraphMap r a → a → ST r Unit
addNode (GraphMap { internal }) node = do
  edges ← JsMap.empty
  JsMap.set node { edges } internal

hasNode ∷ ∀ r a. GraphMap r a → a → ST r Boolean
hasNode (GraphMap { internal }) node =
  JsMap.has node internal

addEdge ∷ ∀ r a. GraphMap r a → a → a → ST r Unit
addEdge (GraphMap { internal }) from to = do
  JsMap.get from internal >>= traverse_ \{ edges } →
    JsMap.set to unit edges

clearEdges ∷ ∀ r a. GraphMap r a → a → ST r Unit
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
      (JsMap r a { edges ∷ JsMap r a Unit })
      (STFn1 a r Unit)
      (STFn1 (Array a) r Unit)
      r
      { singular ∷ STFn1 a r Unit
      , plural ∷ ST r Unit
      }

tarjan
  ∷ ∀ r a
  . GraphMap r a
  → ST r
      { scc ∷ STArray r (SCC a)
      , singular ∷ STFn1 a r Unit
      , plural ∷ ST r Unit
      }
tarjan (GraphMap { internal }) = do
  scc ← STArray.new

  let
    onAcyclic ∷ STFn1 a _ Unit
    onAcyclic = mkSTFn1 \key →
      void $ STArray.push (AcyclicSCC key) scc

    onCyclic ∷ STFn1 (Array a) _ Unit
    onCyclic = mkSTFn1 \component →
      void $ STArray.push (CyclicSCC component) scc

  { singular, plural } ← runSTFn3 tarjanImpl internal onAcyclic onCyclic
  pure { scc, singular, plural }

tarjanOne ∷ ∀ r a. GraphMap r a → a → ST r (Array (SCC a))
tarjanOne graphMap atKey = do
  { scc, singular } ← tarjan graphMap
  runSTFn1 singular atKey
  STArray.freeze scc

tarjanMany ∷ ∀ r a. GraphMap r a → ST r (Array (SCC a))
tarjanMany graphMap = do
  { scc, plural } ← tarjan graphMap
  plural
  STArray.freeze scc
