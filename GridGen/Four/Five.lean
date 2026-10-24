/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.Small5k
import GridGen.Four.BitAll5k
import GridGen.Four.Zero5k

/-!
# Height four: the seam inequality at `k = 5`

The mismatches `μᵢ = 5 - |Bᵢ₋₁ ∩ Bᵢ|` are integers in `[0, 5]`. At `(0,0,0)` the inequality holds
state by state (`seam_zero5k`); at the fourteen triples of `ExactTriple5k` by exact certificates
(`seam_exact5k`); at every other triple by a dual certificate over the state bits
(`seam_bit_all5k`). The analysis is `ai_research_notes/H4_K5_ANALYTIC_2026-10-24.md` with the
review `H4_K5_REVIEW_2026-10-24.md` (uniform box `118/125`, its three fixes).
-/

namespace GridGen.Four

open Finset

/-- The covering check, as a boolean. -/
def coverB5k : Bool :=
  (List.range 6).all fun m2 => (List.range 6).all fun m3 => (List.range 6).all fun m4 =>
    (m2 == 0 && m3 == 0 && m4 == 0) || decide (ExactTriple5k m2 m3 m4) ||
      (bitAll5k.map Prod.fst).contains (m2, m3, m4)

theorem coverB5k_ok : coverB5k = true := by decide +kernel

/-- Every mismatch triple is zero, exact, or has a bit certificate. -/
theorem cover5k (m2 : ℕ) (h2 : m2 < 6) (m3 : ℕ) (h3 : m3 < 6) (m4 : ℕ) (h4 : m4 < 6) :
    (m2 = 0 ∧ m3 = 0 ∧ m4 = 0) ∨ ExactTriple5k m2 m3 m4 ∨
      (m2, m3, m4) ∈ bitAll5k.map Prod.fst := by
  have h := coverB5k_ok
  simp only [coverB5k, List.all_eq_true, List.mem_range] at h
  have h' := h m2 h2 m3 h3 m4 h4
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.contains_iff_mem] at h'
  rcases h' with (⟨⟨a, b⟩, c⟩ | h') | h'
  · exact Or.inl ⟨a, b, c⟩
  · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr h')

/-- **The height-four seam inequality at `k = 5`.** -/
theorem seam4Holds_five : Seam4Holds 5 := by
  intro w hw X₁ X₂ X₃ X₄ B₁ B₂ B₃ B₄ hX₁ hX₂ hX₃ hX₄ hB₁ hB₂ hB₃ hB₄
  have k2 : (B₁ ∩ B₂).card ≤ 5 := hB₁ ▸ card_le_card inter_subset_left
  have k3 : (B₂ ∩ B₃).card ≤ 5 := hB₂ ▸ card_le_card inter_subset_left
  have k4 : (B₃ ∩ B₄).card ≤ 5 := hB₃ ▸ card_le_card inter_subset_left
  have x1 : 4 ≤ X₁.card := hX₁.1
  have x2 : 4 ≤ X₂.card := hX₂.1
  have x3 : 4 ≤ X₃.card := hX₃.1
  have x4 : 4 ≤ X₄.card := hX₄.1
  have c2 : (B₁ ∩ B₂).card + (5 - (B₁ ∩ B₂).card) = 5 := by omega
  have c3 : (B₂ ∩ B₃).card + (5 - (B₂ ∩ B₃).card) = 5 := by omega
  have c4 : (B₃ ∩ B₄).card + (5 - (B₃ ∩ B₄).card) = 5 := by omega
  rcases cover5k (5 - (B₁ ∩ B₂).card) (by omega) (5 - (B₂ ∩ B₃).card) (by omega)
      (5 - (B₃ ∩ B₄).card) (by omega) with ⟨z2, z3, z4⟩ | hE | hbit
  · rw [z2] at c2; rw [z3] at c3; rw [z4] at c4
    exact seam_zero5k hw hB₁ hB₂ hB₃ hB₄ c2 c3 c4
  · exact seam_exact5k hw x1 x2 x3 x4 hB₁ hB₂ hB₃ hB₄ hE c2 c3 c4
  · exact seam_bit_all5k hw x1 x2 x3 x4 hB₁ hB₂ hB₃ hB₄ c2 c3 c4 hbit

end GridGen.Four
