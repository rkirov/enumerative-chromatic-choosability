/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import TwoDegenerate.K2n.Witness
import Mathlib.Tactic.IntervalCases

/-!
# `K₂,ₙ` is not ECC at `3`, `4`, `5` beyond the thresholds

For list size `k = 3, 4, 5` and every `n ≥ 12, 26, 44` respectively, the witness family of
`TwoDegenerate/K2n/Witness.lean` has fewer colourings than the constant assignment. Each case
needs the list sizes, the ratio bound `G ≤ (k-1)⁴`, and one base inequality per residue of
`n mod 4`, all checked by `decide`.

Credit: Kaul et al. (Involve 16 (2023), Theorem 7) prove `n ≥ 12`, `n ≥ 27` and `n ≥ 44`; the case
`k = 4`, `n = 26` is new here (it is `K2_26.not_eccAt_four`, with a different presentation).
-/

namespace SimpleGraph.TwoDegenerate.K2n

open Finset

theorem not_eccAt_of_lt {k n : ℕ} (hL : IsNListAssignment (witness k n) k)
    (h : (completeBipartiteGraph (Fin 2) (Fin n)).col (witness k n) <
      (completeBipartiteGraph (Fin 2) (Fin n)).colConst k) :
    ¬ (completeBipartiteGraph (Fin 2) (Fin n)).ECCAt k :=
  fun hecc => absurd (hecc _ hL) (not_le.mpr h)

theorem isNListAssignment_witness {k n : ℕ} (hA : (hubA k).card = k) (hB : (hubB k).card = k)
    (hT : ∀ t < 4, (rightT k t).card = k) : IsNListAssignment (witness k n) k := by
  rintro (i | w)
  · fin_cases i
    · exact hA
    · exact hB
  · show (rightT k w.val).card = k
    rw [← rightT_mod]
    exact hT _ (Nat.mod_lt _ (by norm_num))

/-- `n = 4q + s` with `s < 4`. -/
theorem exists_four_mul_add (n : ℕ) : ∃ q s, s < 4 ∧ n = 4 * q + s :=
  ⟨n / 4, n % 4, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 4).symm⟩

/-! ### List size three: `n ≥ 12` -/

theorem not_eccAt_three {n : ℕ} (hn : 12 ≤ n) :
    ¬ (completeBipartiteGraph (Fin 2) (Fin n)).ECCAt 3 := by
  obtain ⟨q, s, hs, rfl⟩ := exists_four_mul_add n
  refine not_eccAt_of_lt (isNListAssignment_witness (by decide) (by decide) (by decide)) ?_
  have hG : ∀ a ∈ hubA 3, ∀ b ∈ hubB 3, ∏ t ∈ range 4, cnt 3 a b t ≤ (3 - 1) ^ 4 := by decide
  interval_cases s
  · exact col_witness_lt (q₀ := 3) (by norm_num) (by norm_num) hG (by decide) q (by omega)
  · exact col_witness_lt (q₀ := 3) (by norm_num) (by norm_num) hG (by decide) q (by omega)
  · exact col_witness_lt (q₀ := 3) (by norm_num) (by norm_num) hG (by decide) q (by omega)
  · exact col_witness_lt (q₀ := 3) (by norm_num) (by norm_num) hG (by decide) q (by omega)

/-! ### List size four: `n ≥ 26` -/

theorem not_eccAt_four {n : ℕ} (hn : 26 ≤ n) :
    ¬ (completeBipartiteGraph (Fin 2) (Fin n)).ECCAt 4 := by
  obtain ⟨q, s, hs, rfl⟩ := exists_four_mul_add n
  refine not_eccAt_of_lt (isNListAssignment_witness (by decide) (by decide) (by decide)) ?_
  have hG : ∀ a ∈ hubA 4, ∀ b ∈ hubB 4, ∏ t ∈ range 4, cnt 4 a b t ≤ (4 - 1) ^ 4 := by decide
  interval_cases s
  · exact col_witness_lt (q₀ := 7) (by norm_num) (by norm_num) hG (by decide) q (by omega)
  · exact col_witness_lt (q₀ := 7) (by norm_num) (by norm_num) hG (by decide) q (by omega)
  · exact col_witness_lt (q₀ := 6) (by norm_num) (by norm_num) hG (by decide) q (by omega)
  · exact col_witness_lt (q₀ := 6) (by norm_num) (by norm_num) hG (by decide) q (by omega)

/-! ### List size five: `n ≥ 44` -/

theorem not_eccAt_five {n : ℕ} (hn : 44 ≤ n) :
    ¬ (completeBipartiteGraph (Fin 2) (Fin n)).ECCAt 5 := by
  obtain ⟨q, s, hs, rfl⟩ := exists_four_mul_add n
  refine not_eccAt_of_lt (isNListAssignment_witness (by decide) (by decide) (by decide)) ?_
  have hG : ∀ a ∈ hubA 5, ∀ b ∈ hubB 5, ∏ t ∈ range 4, cnt 5 a b t ≤ (5 - 1) ^ 4 := by decide
  interval_cases s
  · exact col_witness_lt (q₀ := 11) (by norm_num) (by norm_num) hG (by decide) q (by omega)
  · exact col_witness_lt (q₀ := 11) (by norm_num) (by norm_num) hG (by decide) q (by omega)
  · exact col_witness_lt (q₀ := 11) (by norm_num) (by norm_num) hG (by decide) q (by omega)
  · exact col_witness_lt (q₀ := 11) (by norm_num) (by norm_num) hG (by decide) q (by omega)

end SimpleGraph.TwoDegenerate.K2n
