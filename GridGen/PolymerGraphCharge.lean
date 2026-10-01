import GridGen.PolymerActivity

/-! # Actual graph charges and their edge-rooted budget -/

namespace GridGen.Polymer

open SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Charge each individual spanning tree only to edges that it actually contains. -/
noncomputable def graphTreeCharge (L : ListAssignment V) (k : ℕ) (x : ℝ)
    (S : Finset V) (e : Sym2 V) : ℝ :=
  ∑ _T ∈ (spanningTreeSets G S).filter (fun T => e ∈ T), (edgeDef L k e : ℝ) * x ^ S.card

theorem graphTreeCharge_nonneg (L : ListAssignment V) (k : ℕ)
    {x : ℝ} (hx : 0 ≤ x) (S : Finset V) (e : Sym2 V) :
    0 ≤ graphTreeCharge G L k x S e := by
  apply Finset.sum_nonneg
  intro T _
  exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx _)

/-- Nonzero charge forces both endpoints of the charged edge into the block. -/
theorem graphTreeCharge_support (L : ListAssignment V) (k : ℕ) (x : ℝ)
    (S : Finset V) (e : Sym2 V) (hc : graphTreeCharge G L k x S e ≠ 0) :
    e ∈ edgesWithin G.edgeFinset S := by
  classical
  by_contra he
  apply hc
  apply Finset.sum_eq_zero
  intro T hT
  obtain ⟨hT, heT⟩ := Finset.mem_filter.mp hT
  exact (he (((mem_blockEdgeSets G).mp ((mem_spanningTreeSets G).mp hT).1).1 heT)).elim

theorem graphTreeCharge_sum (L : ListAssignment V) (k : ℕ) (x : ℝ)
    {U S : Finset V} (hSU : S ⊆ U) :
    (∑ e ∈ edgesWithin G.edgeFinset U, graphTreeCharge G L k x S e) =
      (∑ T ∈ spanningTreeSets G S, ∑ e ∈ T, (edgeDef L k e : ℝ)) * x ^ S.card := by
  classical
  unfold graphTreeCharge
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro T hT
  have hs := ((mem_blockEdgeSets G).mp ((mem_spanningTreeSets G).mp hT).1).1
  have hTU : T ⊆ edgesWithin G.edgeFinset U := by
    intro e he
    have hh := mem_edgesWithin.mp (hs he)
    exact mem_edgesWithin.mpr ⟨hh.1, fun v hv => hSU (hh.2 v hv)⟩
  rw [Finset.sum_mul]
  calc
    _ = ∑ e ∈ T, if e ∈ T then (edgeDef L k e : ℝ) * x ^ S.card else 0 := by
      symm
      exact Finset.sum_subset hTU (by intro e _ he; simp [he])
    _ = _ := Finset.sum_congr rfl (fun e he => ite_eq_left he)

/-- The coefficient-weighted deficiency is bounded by the total actual edge charge. -/
theorem coefficient_deficiency_le_graphTreeCharge
    {L : ListAssignment V} {k : ℕ} (hL : IsNListAssignment L k)
    {x : ℝ} (hx : 0 ≤ x) {U S : Finset V} (hSU : S ⊆ U) (hS : S.Nonempty) :
    |blockCoefficient G S| * listDeficiency L k S * x ^ S.card ≤
      ∑ e ∈ edgesWithin G.edgeFinset U, graphTreeCharge G L k x S e := by
  rw [graphTreeCharge_sum G L k x hSU]
  exact mul_le_mul_of_nonneg_right (coefficient_deficiency_le_tree_sum G hL hS)
    (pow_nonneg hx _)

end GridGen.Polymer
