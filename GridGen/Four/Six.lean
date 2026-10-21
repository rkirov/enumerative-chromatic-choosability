/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.Small6
import GridGen.Four.Cert6

/-!
# Height four: the seam inequality at `k = 6`

The mismatches `μᵢ = 6 - |Bᵢ₋₁ ∩ Bᵢ|` are integers in `[0, 6]`. At `(0,0,0)` the uncapped
certificate `F6val` is `0`; at the sixteen small nonzero triples (`ExactTriple6`) the lists have one
of 69 shapes, each with an exact certificate (`seam_exact6`); everywhere else the capped
certificate holds (`cert6`).
-/

namespace GridGen.Four

open Finset

theorem mu_nat6 {B C : Finset ℕ} (hB : B.card = 6) :
    ∃ m : ℕ, mu 6 B C = m ∧ m ≤ 6 ∧ (B ∩ C).card + m = 6 := by
  have h : (B ∩ C).card ≤ 6 := hB ▸ Finset.card_le_card Finset.inter_subset_left
  refine ⟨6 - (B ∩ C).card, ?_, by omega, by omega⟩
  unfold mu; push_cast [Nat.cast_sub h]; ring

theorem exactTriple6_of_small {a b c : ℕ} (h : Small6 a b c) (h0 : ¬ (a = 0 ∧ b = 0 ∧ c = 0)) :
    ExactTriple6 a b c := by
  have key : ∀ t ∈ small6, ¬ (t.1 = 0 ∧ t.2.1 = 0 ∧ t.2.2 = 0) →
      ExactTriple6 t.1 t.2.1 t.2.2 := by decide
  exact key (a, b, c) h h0

/-- **The height-four seam inequality at `k = 6`.** -/
theorem seam4Holds_six : Seam4Holds 6 := by
  intro w hw X₁ X₂ X₃ X₄ B₁ B₂ B₃ B₄ hX₁ hX₂ hX₃ hX₄ hB₁ hB₂ hB₃ hB₄
  obtain ⟨m2, e2, h2, c2⟩ := mu_nat6 (C := B₂) hB₁
  obtain ⟨m3, e3, h3, c3⟩ := mu_nat6 (C := B₃) hB₂
  obtain ⟨m4, e4, h4, c4⟩ := mu_nat6 (C := B₄) hB₃
  have X1 := hX₁.1
  have X2 := hX₂.1
  have X3 := hX₃.1
  have X4 := hX₄.1
  by_cases h0 : m2 = 0 ∧ m3 = 0 ∧ m4 = 0
  · -- `(0,0,0)`: the uncapped certificate vanishes
    obtain ⟨rfl, rfl, rfl⟩ := h0
    refine seam_of_cert6 hw X1 X2 X3 X4 hB₁ hB₂ hB₃ hB₄ (Or.inl ?_)
    rw [e2, e3, e4]; norm_num [F6val, F6core, J3, J4]
  by_cases hs : Small6 m2 m3 m4
  · exact seam_exact6 hw X1 X2 X3 X4 hB₁ hB₂ hB₃ hB₄ (exactTriple6_of_small hs h0) c2 c3 c4
  · refine seam_of_cert6 hw X1 X2 X3 X4 hB₁ hB₂ hB₃ hB₄ (Or.inr ?_)
    rw [e2, e3, e4]
    exact cert6 h2 h3 h4 hs

end GridGen.Four
