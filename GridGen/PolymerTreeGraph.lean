import GridGen.PolymerCancellation

/-!
# The tree-graph bound for actual connected-block coefficients

Active connected edge sets cancel in pairs. Every surviving edge set is acyclic, so the
absolute connected coefficient is at most the number of spanning trees on that block.
-/

namespace GridGen.Polymer

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Spanning trees of `G` on a specified nonempty vertex block. Vertices outside the block
are isolated; acyclicity is checked in the common ambient vertex type. -/
noncomputable def spanningTreeSets (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : Finset (Finset (Sym2 V)) := by
  classical
  exact (blockEdgeSets G S).filter (fun T => (edgeGraph T).IsAcyclic)

theorem mem_spanningTreeSets (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} {T : Finset (Sym2 V)} :
    T ∈ spanningTreeSets G S ↔ T ∈ blockEdgeSets G S ∧ (edgeGraph T).IsAcyclic := by
  classical
  exact Finset.mem_filter

section Ordered

variable [LinearOrder (Sym2 V)]

local instance (priority := 2000) treeGraphOrder : PartialOrder (Sym2 V) :=
  (inferInstance : LinearOrder (Sym2 V)).toPartialOrder

theorem blockCoefficient_eq_sum_inactive (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) :
    blockCoefficient G S = ∑ T ∈ (blockEdgeSets G S).filter
      (fun T => ¬(activeEdges (edgesWithin G.edgeFinset S) T).Nonempty),
      (-1 : ℝ) ^ T.card := by
  classical
  have h := Finset.sum_filter_add_sum_filter_not (blockEdgeSets G S)
    (fun T => (activeEdges (edgesWithin G.edgeFinset S) T).Nonempty)
    (fun T => (-1 : ℝ) ^ T.card)
  rw [sum_active_blockEdgeSets_eq_zero, zero_add] at h
  exact h.symm

theorem inactive_subset_spanningTreeSets (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) :
    (blockEdgeSets G S).filter
      (fun T => ¬(activeEdges (edgesWithin G.edgeFinset S) T).Nonempty) ⊆
      spanningTreeSets G S := by
  classical
  intro T hT
  obtain ⟨hT, hactive⟩ := Finset.mem_filter.mp hT
  apply (mem_spanningTreeSets G).mpr
  refine ⟨hT, isAcyclic_of_no_active T ?_⟩
  intro e he hae
  apply hactive
  exact ⟨e, Finset.mem_filter.mpr ⟨((mem_blockEdgeSets G).mp hT).1 he, hae⟩⟩

theorem blockCoefficient_abs_le_trees_ordered (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : |blockCoefficient G S| ≤ (spanningTreeSets G S).card := by
  classical
  rw [blockCoefficient_eq_sum_inactive]
  calc
    _ ≤ ∑ T ∈ (blockEdgeSets G S).filter
        (fun T => ¬(activeEdges (edgesWithin G.edgeFinset S) T).Nonempty),
        |(-1 : ℝ) ^ T.card| := Finset.abs_sum_le_sum_abs _ _
    _ = (((blockEdgeSets G S).filter
        (fun T => ¬(activeEdges (edgesWithin G.edgeFinset S) T).Nonempty)).card : ℝ) := by
      simp
    _ ≤ _ := by exact_mod_cast Finset.card_le_card (inactive_subset_spanningTreeSets G S)

end Ordered

/-- The order-free tree-graph coefficient bound. The auxiliary total order is used only
inside the proof; no tree-counting or sign hypothesis is assumed. -/
theorem blockCoefficient_abs_le_trees (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : |blockCoefficient G S| ≤ (spanningTreeSets G S).card := by
  classical
  let e := Fintype.equivFin (Sym2 V)
  let : LinearOrder (Sym2 V) := LinearOrder.lift' e e.injective
  exact blockCoefficient_abs_le_trees_ordered G S

end GridGen.Polymer
