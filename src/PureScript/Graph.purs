module PureScript.Graph where

import Prelude

import Control.Monad.ST as ST
import Control.Monad.ST.Uncurried (STFn1, STFn4, mkSTFn1, runSTFn4)
import Data.Array as Array
import Data.Array.ST as STArray
import Data.Maybe (Maybe)
import Safe.Coerce (coerce)

newtype Index ∷ Type → Type
newtype Index a = Index Int

derive newtype instance Eq (Index a)
derive newtype instance Show (Index a)

newtype Graph a = Graph
  { vertices ∷ Array a
  , edges ∷ Array (Array Int)
  }

derive newtype instance Eq a ⇒ Eq (Graph a)
derive newtype instance Show a ⇒ Show (Graph a)

data SCC a = AcyclicSCC (Index a) | CyclicSCC (Array (Index a))

derive instance Eq (SCC a)

instance Show (SCC a) where
  show = case _ of
    AcyclicSCC i → "(AcyclicSCC " <> show i <> ")"
    CyclicSCC i → "(CyclicSCC " <> show i <> ")"

foreign import tarjanImpl
  ∷ ∀ a r
  . STFn4
      (Array a)
      (Array (Array Int))
      (STFn1 Int r Unit)
      (STFn1 (Array Int) r Unit)
      r
      Unit

tarjan ∷ ∀ a. Graph a → Array (SCC a)
tarjan (Graph { vertices, edges }) = ST.run do
  scc ← STArray.new

  let
    onAcyclic ∷ STFn1 Int _ Unit
    onAcyclic = mkSTFn1 \key →
      void $ STArray.push (AcyclicSCC $ coerce key) scc

    onCyclic ∷ STFn1 (Array Int) _ Unit
    onCyclic = mkSTFn1 \component →
      void $ STArray.push (CyclicSCC $ coerce component) scc

  runSTFn4 tarjanImpl vertices edges onAcyclic onCyclic
  STArray.freeze scc

vertex ∷ ∀ a. Graph a → Index a → Maybe a
vertex (Graph { vertices }) (Index index) = Array.index vertices index

edge ∷ ∀ a. Graph a → Index a → Maybe (Array (Index a))
edge (Graph { edges }) (Index index) = coerce $ Array.index edges index
