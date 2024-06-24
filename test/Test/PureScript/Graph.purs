module Test.PureScript.Graph where

import Prelude

import Effect.Class (liftEffect)
import PureScript.Graph (Graph(..), Index(..), SCC(..), tarjan)
import PureScript.Graph.Builder as GraphBuilder
import Safe.Coerce (coerce)
import Test.Snapshot (SnapshotSpec)
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldEqual)

dyad ∷ Graph String
dyad = Graph { vertices: [ "0", "1" ], edges: [ [ 1 ], [ 0 ] ] }

triad ∷ Graph String
triad = Graph { vertices: [ "0", "1", "2" ], edges: [ [ 1 ], [ 2 ], [ 0 ] ] }

quad ∷ Graph String
quad = Graph { vertices: [ "0", "1", "2", "3" ], edges: [ [ 1 ], [ 2 ], [ 3 ], [ 0 ] ] }

self ∷ Graph String
self = Graph { vertices: [ "0" ], edges: [ [ 0 ] ] }

none ∷ Graph String
none = Graph { vertices: [ "0" ], edges: [ [] ] }

island ∷ Graph String
island = Graph { vertices: [ "0", "1" ], edges: [ [], [] ] }

archipelago ∷ Graph String
archipelago = Graph { vertices: [ "0", "1", "2", "3" ], edges: [ [ 1 ], [ 0 ], [ 3 ], [ 2 ] ] }

spec ∷ SnapshotSpec Unit
spec = do
  describe "PureScript.Graph" do
    describe "Tarjan" do
      it "dyad" do
        tarjan dyad `shouldEqual` [ CyclicSCC $ coerce [ 1, 0 ] ]
      it "triad" do
        tarjan triad `shouldEqual` [ CyclicSCC $ coerce [ 2, 1, 0 ] ]
      it "quad" do
        tarjan quad `shouldEqual` [ CyclicSCC $ coerce [ 3, 2, 1, 0 ] ]
      it "self" do
        tarjan self `shouldEqual` [ CyclicSCC $ coerce [ 0 ] ]
      it "none" do
        tarjan none `shouldEqual` [ AcyclicSCC $ coerce 0 ]
      it "island" do
        tarjan island `shouldEqual` [ AcyclicSCC $ coerce 0, AcyclicSCC $ coerce 1 ]
      it "archipelago" do
        tarjan archipelago `shouldEqual`
          [ CyclicSCC $ coerce [ 1, 0 ], CyclicSCC $ coerce [ 3, 2 ] ]
    describe "Builder" do
      it "dyad" do
        g ← liftEffect do
          g ← GraphBuilder.initialize
          a ← GraphBuilder.addVertex g "0"
          b ← GraphBuilder.addVertex g "1"
          GraphBuilder.addEdge g a b
          GraphBuilder.addEdge g b a
          GraphBuilder.build g
        g `shouldEqual` dyad
