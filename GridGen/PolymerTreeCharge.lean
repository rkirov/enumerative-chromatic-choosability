import GridGen.PolymerTreeGraph
import GridGen.PolymerDeficiency
import GridGen.PolymerEndpoints

/-!
# The graph-combinatorial treewise charge inequality

This combines the actual connected-coefficient bound with list deficiency domination for
each individual spanning tree. No tree-counting estimate or coefficient hypothesis is assumed.
-/

namespace GridGen.Polymer

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem listDeficiency_le_tree_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    {L : ListAssignment V} {k : ℕ} (hL : IsNListAssignment L k)
    {S : Finset V} {T : Finset (Sym2 V)} (hT : T ∈ spanningTreeSets G S) :
    listDeficiency L k S ≤ ∑ e ∈ T, (edgeDef L k e : ℝ) := by
  have hconn := ((mem_blockEdgeSets G).mp ((mem_spanningTreeSets G).mp hT).1).2
  obtain ⟨r, hr⟩ := hconn.1
  have h := deficiency_le_connecting_edges hL S T r hr (hconn.2 r hr)
  have hc : ((k - (listInter L S).card : ℕ) : ℝ) ≤
      ∑ e ∈ T, (edgeDef L k e : ℝ) := by exact_mod_cast h
  simpa only [Nat.cast_sub (card_listInter_le hL ⟨r, hr⟩), listDeficiency] using hc

/-- Each block's coefficient-weighted deficiency is paid for by individual spanning-tree
edges. Keeping these tree edges is what permits the sharper edge-rooted counting bound. -/
theorem coefficient_deficiency_le_tree_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    {L : ListAssignment V} {k : ℕ} (hL : IsNListAssignment L k)
    {S : Finset V} (hS : S.Nonempty) :
    |blockCoefficient G S| * listDeficiency L k S ≤
      ∑ T ∈ spanningTreeSets G S, ∑ e ∈ T, (edgeDef L k e : ℝ) := by
  calc
    _ ≤ (spanningTreeSets G S).card * listDeficiency L k S :=
      mul_le_mul_of_nonneg_right (blockCoefficient_abs_le_trees G S)
        (listDeficiency_nonneg hL hS)
    _ = ∑ T ∈ spanningTreeSets G S, listDeficiency L k S := by simp
    _ ≤ _ := Finset.sum_le_sum fun T hT => listDeficiency_le_tree_edges G hL hT

end GridGen.Polymer
