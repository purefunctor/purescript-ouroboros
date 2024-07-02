module Test.PureScript.Graph where

import Prelude

import Control.Monad.ST (ST)
import Control.Monad.ST.Global (Global, toEffect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import PureScript.Utils.Mutable.GraphMap
  ( GraphMap
  , SCC(..)
  , addEdge
  , addNode
  , tarjanMany
  , tarjanOne
  )
import PureScript.Utils.Mutable.GraphMap as GraphMap
import Test.Snapshot (SnapshotSpec)
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldEqual)

expectSccOne
  ∷ ∀ a. Eq a ⇒ Show a ⇒ ST Global (GraphMap Global a) → a → Array (SCC a) → Aff Unit
expectSccOne makeGraph key expectedScc = do
  scc ← liftEffect <<< toEffect $ do
    graph ← makeGraph
    tarjanOne graph key
  scc `shouldEqual` expectedScc

expectSccMany
  ∷ ∀ a. Eq a ⇒ Show a ⇒ ST Global (GraphMap Global a) → Array (SCC a) → Aff Unit
expectSccMany makeGraph expectedScc = do
  scc ← liftEffect <<< toEffect $ do
    graph ← makeGraph
    tarjanMany graph
  scc `shouldEqual` expectedScc

spec ∷ SnapshotSpec Unit
spec =
  describe "PureScript.GraphMap" do
    describe "Tarjan" do
      let
        dag ∷ ST _ (GraphMap _ String)
        dag = do
          graph ← GraphMap.emptyGraphMap
          addNode graph "a"
          addNode graph "b"
          addNode graph "c"
          addEdge graph "a" "b"
          addEdge graph "b" "c"
          pure graph

      it "tarjanOne: dag" do
        expectSccOne dag "b" [ AcyclicSCC "c", AcyclicSCC "b" ]
      it "tarjanMany: dag" do
        expectSccMany dag [ AcyclicSCC "c", AcyclicSCC "b", AcyclicSCC "a" ]

      let
        selfCyclic ∷ ST _ (GraphMap _ String)
        selfCyclic = do
          graph ← GraphMap.emptyGraphMap
          addNode graph "a"
          addEdge graph "a" "a"
          pure graph

      it "tarjanOne: selfCyclic" do
        expectSccOne selfCyclic "a" [ CyclicSCC [ "a" ] ]
      it "tarjanMany: selfCyclic" do
        expectSccMany selfCyclic [ CyclicSCC [ "a" ] ]

      let
        duoCyclic ∷ ST _ (GraphMap _ String)
        duoCyclic = do
          graph ← GraphMap.emptyGraphMap
          addNode graph "a"
          addNode graph "b"
          addEdge graph "a" "b"
          addEdge graph "b" "a"
          addNode graph "c"
          addNode graph "d"
          addEdge graph "c" "d"
          addEdge graph "d" "c"
          pure graph

      it "tarjanOne: duoCyclic" do
        expectSccOne duoCyclic "a" [ CyclicSCC [ "b", "a" ] ]
      it "tarjanMany: duoCyclic" do
        expectSccMany duoCyclic [ CyclicSCC [ "b", "a" ], CyclicSCC [ "d", "c" ] ]

      let
        island ∷ ST _ (GraphMap _ String)
        island = do
          graph ← GraphMap.emptyGraphMap
          addNode graph "a"
          addNode graph "b"
          addNode graph "c"
          addEdge graph "a" "b"
          addEdge graph "b" "a"
          pure graph

      it "tarjanOne: island" do
        expectSccOne island "c" [ AcyclicSCC "c" ]
      it "tarjanMany: island" do
        expectSccMany island [ CyclicSCC [ "b", "a" ], AcyclicSCC "c" ]
