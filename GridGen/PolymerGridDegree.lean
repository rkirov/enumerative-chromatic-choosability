import ListColoring.CycleRotate
import Mathlib.Combinatorics.SimpleGraph.Prod

/-! The degree-four hypothesis for the repository's actual arbitrary rectangles.
`pathG n` has `n + 1` vertices; neither dimension is fixed here. -/

namespace GridGen.Polymer

open Finset SimpleGraph ListColoring
open scoped SimpleGraph

theorem degree_pathG_le_two (n : ℕ) (v : PathV n) : (pathG n).degree v ≤ 2 := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  calc
    ((pathG n).neighborFinset v).card ≤
        ({pathVtx n (pathIdx n v + 1), pathVtx n (pathIdx n v - 1)} : Finset (PathV n)).card := by
      apply Finset.card_le_card
      intro u hu
      have hadj := (SimpleGraph.mem_neighborFinset _ _ _).mp hu
      have h := (pathG_adj_pathVtx n (pathIdx n v) (pathIdx n u)
        (pathIdx_le n v) (pathIdx_le n u)).mp (by
          simpa only [pathVtx_pathIdx] using hadj)
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases h with h | h
      · left
        rw [h, pathVtx_pathIdx]
      · right
        have heq : pathIdx n u = pathIdx n v - 1 := by omega
        rw [← heq, pathVtx_pathIdx]
    _ ≤ 2 := by
      simpa using Finset.card_insert_le (pathVtx n (pathIdx n v + 1))
        {pathVtx n (pathIdx n v - 1)}

/-- Every rectangle has maximum degree at most four, uniformly in both dimensions. -/
theorem degree_full_grid_le_four (n m : ℕ) (v : PathV n × PathV m) :
    (pathG n □ pathG m).degree v ≤ 4 := by
  classical
  rw [SimpleGraph.degree_boxProd]
  have hn := degree_pathG_le_two n v.1
  have hm := degree_pathG_le_two m v.2
  omega

end GridGen.Polymer
