import GridGen.PolymerCoefficientFactor
import GridGen.PolymerDerivative

/-!
# The actual coloring-count endpoints of the finite interpolation

The endpoint equalities below are unconditional identities for finite simple graphs.
They do not assume positivity, tree bounds, or the desired ECC conclusion.
-/

namespace GridGen.Polymer

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def listDeficiency (L : ListAssignment V) (k : ℕ) (S : Finset V) : ℝ :=
  (k : ℝ) - (listInter L S).card

theorem listDeficiency_nonneg {L : ListAssignment V} {k : ℕ}
    (hL : IsNListAssignment L k) {S : Finset V} (hS : S.Nonempty) :
    0 ≤ listDeficiency L k S := by
  apply sub_nonneg.mpr
  exact_mod_cast card_listInter_le hL hS

theorem listDeficiency_le (L : ListAssignment V) (k : ℕ) (S : Finset V) :
    listDeficiency L k S ≤ k := by
  unfold listDeficiency
  exact sub_le_self _ (Nat.cast_nonneg _)

@[simp] theorem listDeficiency_singleton {L : ListAssignment V} {k : ℕ}
    (hL : IsNListAssignment L k) (v : V) : listDeficiency L k {v} = 0 := by
  simp [listDeficiency, listInter_singleton, hL v]

theorem listInter_constList (k : ℕ) {S : Finset V} (hS : S.Nonempty) :
    listInter (constList V k) S = Finset.range k := by
  ext a
  rw [mem_listInter hS]
  constructor
  · intro h
    obtain ⟨v, hv⟩ := hS
    exact h v hv
  · intro h v _
    exact h

omit [Fintype V] in
theorem partitionSum_congr_nonempty (w z : Finset V → ℝ)
    (h : ∀ S, S.Nonempty → w S = z S) (U : Finset V) :
    partitionSum w U = partitionSum z U := by
  classical
  apply Finset.sum_congr rfl
  intro P _
  exact Finset.prod_congr rfl fun S hS => h S (P.nonempty_of_mem_parts hS)

/-- At zero the interpolation is the ordinary constant-list coloring count. -/
theorem interpolatedSum_zero (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : ListAssignment V) (k : ℕ) :
    interpolatedSum (blockCoefficient G) (listDeficiency L k) k 0 univ =
      (G.colConst k : ℝ) := by
  rw [colConst, col_eq_partitionSum, interpolatedSum]
  apply partitionSum_congr_nonempty
  intro S hS
  rw [listInter_constList k hS, Finset.card_range]
  simp

/-- At one the interpolation is the given list-coloring count. -/
theorem interpolatedSum_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : ListAssignment V) (k : ℕ) :
    interpolatedSum (blockCoefficient G) (listDeficiency L k) k 1 univ =
      (G.col L : ℝ) := by
  rw [col_eq_partitionSum, interpolatedSum]
  apply partitionSum_congr_nonempty
  intro S _
  simp [listDeficiency]

end GridGen.Polymer
