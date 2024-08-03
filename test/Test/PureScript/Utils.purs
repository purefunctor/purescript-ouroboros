module Test.PureScript.Utils where

import Prelude

import Data.Array as Array
import Data.Map (Map)
import Data.Map as Map
import PureScript.Utils.Immutable.IntMap (IntMap)
import PureScript.Utils.Immutable.IntMap as IntMap
import Test.Snapshot (SnapshotSpec)
import Test.Spec (describe, it)
import Test.Spec.QuickCheck (quickCheck)

spec ∷ SnapshotSpec Unit
spec = do
  describe "PureScript.Utils.IntMap" do
    describe "Eq" do
      it "satisfies reflexivity" do
        quickCheck \i j k → do
          let
            x ∷ IntMap String
            x = IntMap.fromArray [ i, j, k ]
          x == x
      it "satisfies symmetry" do
        quickCheck \i j k → do
          let
            x ∷ IntMap String
            x = IntMap.fromArray [ i, j, k ]

            y ∷ IntMap String
            y = IntMap.fromArray [ j, k, i ]
          x == y && y == x
      it "satisfies transitifity" do
        quickCheck \i j k → do
          let
            x ∷ IntMap String
            x = IntMap.fromArray [ i, j, k ]

            y ∷ IntMap String
            y = IntMap.fromArray [ k, i, j ]

            z ∷ IntMap String
            z = IntMap.fromArray [ j, k, i ]
          x == y && y == z && x == z

    describe "Ord" do
      it "satisfies reflexivity" do
        quickCheck \i j → do
          let
            x ∷ IntMap String
            x = IntMap.fromArray i

            x' ∷ IntMap String
            x' = IntMap.fromArray j

            y ∷ Map Int String
            y = Map.fromFoldable i

            y' ∷ Map Int String
            y' = Map.fromFoldable j
          [ x <= x, x <= x' ] == [ y <= y, y <= y' ]

      it "satisfies antisymmetry" do
        quickCheck \i j → do
          let
            x ∷ IntMap String
            x = IntMap.fromArray i

            x' ∷ IntMap String
            x' = IntMap.fromArray j

            y ∷ Map Int String
            y = Map.fromFoldable i

            y' ∷ Map Int String
            y' = Map.fromFoldable j
          [ x <= x', x' <= x, x == x' ] == [ y <= y', y' <= y, y == y' ]

      it "satisfies transitivity" do
        quickCheck \i j k → do
          let
            x ∷ IntMap String
            x = IntMap.fromArray i

            y ∷ IntMap String
            y = IntMap.fromArray j

            z ∷ IntMap String
            z = IntMap.fromArray k

            t ∷ Map Int String
            t = Map.fromFoldable i

            u ∷ Map Int String
            u = Map.fromFoldable j

            v ∷ Map Int String
            v = Map.fromFoldable k
          [ x <= y, y <= z, x <= z ] == [ t <= u, u <= v, t <= v ]

    describe "fromArray & toArray" do
      it "sorts automatically" do
        quickCheck \(x ∷ Array (_ Int String)) →
          IntMap.toArray (IntMap.fromArray x) == Array.sort x
