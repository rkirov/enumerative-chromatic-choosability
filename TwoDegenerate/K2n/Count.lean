/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import TwoDegenerate.Counterexample

/-!
# The constant-list count of `K₂,ₙ`

`P(K₂,ₙ, k) = k (k-1)ⁿ + k (k-1) (k-2)ⁿ`: fix the colours `a, b` of the two hubs; each of the `n`
other vertices then has `k - 1` colours left if `a = b` and `k - 2` if not.
-/

namespace SimpleGraph.TwoDegenerate.K2n

open Finset

theorem card_range_sdiff_pair {k a b : ℕ} (ha : a < k) (hb : b < k) :
    (range k \ {a, b}).card = if a = b then k - 1 else k - 2 := by
  have hsub : ({a, b} : Finset ℕ) ⊆ range k := by
    intro x hx
    rcases mem_insert.mp hx with rfl | h
    · exact mem_range.mpr ha
    · rw [mem_singleton.mp h]; exact mem_range.mpr hb
  rw [card_sdiff_of_subset hsub, card_range]
  split_ifs with h
  · subst h; simp
  · rw [card_pair h]

/-- The number of `k`-colourings of `K₂,ₙ`. -/
theorem colConst_K2n (k n : ℕ) :
    (completeBipartiteGraph (Fin 2) (Fin n)).colConst k =
      k * (k - 1) ^ n + k * (k - 1) * (k - 2) ^ n := by
  rw [colConst, col_completeBipartite_two_right]
  simp only [constList, prod_const, card_univ, Fintype.card_fin]
  have hinner : ∀ a ∈ range k,
      ∑ b ∈ range k, (range k \ {a, b}).card ^ n = (k - 1) ^ n + (k - 1) * (k - 2) ^ n := by
    intro a ha
    rw [← add_sum_erase _ _ ha, card_range_sdiff_pair (mem_range.mp ha) (mem_range.mp ha),
      if_pos rfl]
    congr 1
    rw [sum_congr rfl fun b hb => by
      rw [card_range_sdiff_pair (mem_range.mp ha) (mem_range.mp (mem_of_mem_erase hb)),
        if_neg (Ne.symm (ne_of_mem_erase hb))]]
    rw [sum_const, card_erase_of_mem ha, card_range, smul_eq_mul]
  rw [sum_congr rfl hinner, sum_const, card_range, smul_eq_mul]
  rw [Nat.mul_add, Nat.mul_assoc]

end SimpleGraph.TwoDegenerate.K2n
