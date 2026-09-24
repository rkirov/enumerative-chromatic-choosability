import GridGen.PolymerTreeCharge
import GridGen.PolymerSmallBlocks
import GridGen.PolymerModel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # The activity of a block in the actual graph interpolation

`graphActivity G L k x S t` is `c(S) (k - t d(S)) x^|S|`, the weight of the block `S` in the
finite interpolation between the constant and the list colouring counts, normalized by `x`. -/

namespace GridGen.Polymer

open SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def graphActivity (L : ListAssignment V) (k : ℕ) (x : ℝ)
    (S : Finset V) (t : ℝ) : ℝ :=
  blockCoefficient G S * ((k : ℝ) - t * listDeficiency L k S) * x ^ S.card

theorem interpolation_factor_bounds {L : ListAssignment V} {k : ℕ}
    (hL : IsNListAssignment L k) {S : Finset V} (hS : S.Nonempty)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ (k : ℝ) - t * listDeficiency L k S ∧
      (k : ℝ) - t * listDeficiency L k S ≤ k := by
  have hd := listDeficiency_nonneg hL hS
  have hdk := listDeficiency_le L k S
  constructor <;> nlinarith [mul_nonneg ht.1 hd, mul_nonneg (sub_nonneg.mpr ht.2) hd]

theorem graphActivity_abs_le {L : ListAssignment V} {k : ℕ}
    (hL : IsNListAssignment L k) {x t : ℝ} (hx : 0 ≤ x)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) {S : Finset V} (hS : S.Nonempty) :
    |graphActivity G L k x S t| ≤
      (k : ℝ) * x * (∑ _T ∈ spanningTreeSets G S, x ^ (S.card - 1)) := by
  have hf := interpolation_factor_bounds hL hS ht
  have hxpow := pow_nonneg hx S.card
  have hcard : S.card - 1 + 1 = S.card := by have := hS.card_pos; omega
  calc
    _ = |blockCoefficient G S| * ((k : ℝ) - t * listDeficiency L k S) * x ^ S.card := by
      simp only [graphActivity, abs_mul, abs_of_nonneg hf.1, abs_of_nonneg hxpow]
    _ ≤ (spanningTreeSets G S).card * (k : ℝ) * x ^ S.card := by
      apply mul_le_mul_of_nonneg_right _ hxpow
      exact mul_le_mul (blockCoefficient_abs_le_trees G S) hf.2 hf.1 (Nat.cast_nonneg _)
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hpow : x ^ S.card = x ^ (S.card - 1) * x := by rw [← pow_succ, hcard]
      rw [hpow]
      ring

theorem graphActivity_singleton {L : ListAssignment V} {k : ℕ}
    (hL : IsNListAssignment L k) (x t : ℝ) (v : V) :
    graphActivity G L k x {v} t = (k : ℝ) * x := by
  simp [graphActivity, listDeficiency_singleton hL]

end GridGen.Polymer
