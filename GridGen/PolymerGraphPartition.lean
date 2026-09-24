import GridGen.PolymerPartition
import ListColoring.Threshold

/-!
# Connected-component partitions and the grouped Whitney expansion

This is the graph-to-partition bridge. The parts of `componentPartition T` are the actual
connected components of the spanning edge subgraph `T`, including isolated vertices.
-/

namespace GridGen.Polymer

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem compFinset_injective (T : Finset (Sym2 V)) :
    Function.Injective (compFinset T) := by
  intro C D h
  obtain ⟨v, hv⟩ := compFinset_nonempty T C
  have hvD : v ∈ compFinset T D := h ▸ hv
  exact (mem_compFinset.mp hv).symm.trans (mem_compFinset.mp hvD)

/-- The component partition of a spanning edge subgraph. -/
noncomputable def componentPartition (T : Finset (Sym2 V)) : Finpartition (univ : Finset V) := by
  classical
  refine Finpartition.ofExistsUnique (univ.image (compFinset T)) (by simp) ?_ ?_
  · intro v _
    refine ⟨compFinset T ((edgeGraph T).connectedComponentMk v), ⟨?_, by simp⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
    · intro S hS
      obtain ⟨C, _, rfl⟩ := Finset.mem_image.mp hS.1
      rw [mem_compFinset.mp hS.2]
  · intro h
    obtain ⟨C, _, hC⟩ := Finset.mem_image.mp h
    exact (compFinset_nonempty T C).ne_empty hC

@[simp] theorem componentPartition_parts (T : Finset (Sym2 V)) :
    (componentPartition T).parts = univ.image (compFinset T) := by
  classical
  rfl

theorem mem_componentPartition_parts (T : Finset (Sym2 V)) (S : Finset V) :
    S ∈ (componentPartition T).parts ↔ ∃ C, compFinset T C = S := by
  classical
  simp [componentPartition_parts]

/-- The list-intersection product in Whitney's formula depends only on the vertex partition. -/
theorem listCount_eq_prod_parts (L : ListAssignment V) (T : Finset (Sym2 V)) :
    listCount L T = ∏ S ∈ (componentPartition T).parts, (listInter L S).card := by
  classical
  rw [componentPartition_parts, Finset.prod_image (compFinset_injective T).injOn]
  exact listCount_eq_prod L T

/-- The total alternating coefficient of one component partition. The factorization into
connected block coefficients is a separate combinatorial identity. -/
noncomputable def partitionCoefficient (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) : ℝ := by
  classical
  exact ∑ T ∈ G.edgeFinset.powerset.filter (fun T => componentPartition T = P),
    (-1 : ℝ) ^ T.card

/-- Whitney's list-coloring expansion grouped by the actual connected-component partition.
No factorization of the coefficient is assumed in this identity. -/
theorem col_eq_sum_partitions (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : ListAssignment V) :
    (G.col L : ℝ) = ∑ P : Finpartition (univ : Finset V),
      partitionCoefficient G P * ∏ S ∈ P.parts, ((listInter L S).card : ℝ) := by
  classical
  have hc : (G.col L : ℝ) = ∑ T ∈ G.edgeFinset.powerset,
      (-1 : ℝ) ^ T.card * (listCount L T : ℝ) := by
    exact_mod_cast G.col_eq_sum_powerset L
  rw [hc, ← Finset.sum_fiberwise G.edgeFinset.powerset componentPartition]
  apply Finset.sum_congr rfl
  intro P _
  rw [partitionCoefficient, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro T hT
  rw [listCount_eq_prod_parts, (Finset.mem_filter.mp hT).2]
  simp only [Nat.cast_prod]

end GridGen.Polymer
