/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.Small7
import GridGen.Four.Cert7

/-!
# Height four: the seam inequality at `k = 7`

The mismatches `μᵢ = 7 - |Bᵢ₋₁ ∩ Bᵢ|` are integers in `[0, 7]`. At `(0,0,0)` the uncapped
certificate is `0`; at the five smallest nonzero triples the lists have one of eight shapes, each
with an exact certificate (`Small7.lean`); everywhere else the capped certificate holds
(`cert7`).
-/

namespace GridGen.Four

open Finset

theorem mu_nat {B C : Finset ℕ} (hB : B.card = 7) :
    ∃ m : ℕ, mu 7 B C = m ∧ m ≤ 7 ∧ (B ∩ C).card + m = 7 := by
  have h : (B ∩ C).card ≤ 7 := hB ▸ Finset.card_le_card Finset.inter_subset_left
  refine ⟨7 - (B ∩ C).card, ?_, by omega, by omega⟩
  unfold mu; push_cast [Nat.cast_sub h]; ring

/-- **The height-four seam inequality at `k = 7`.** -/
theorem seam4Holds_seven : Seam4Holds 7 := by
  intro w hw X₁ X₂ X₃ X₄ B₁ B₂ B₃ B₄ hX₁ hX₂ hX₃ hX₄ hB₁ hB₂ hB₃ hB₄
  obtain ⟨m2, e2, h2, c2⟩ := mu_nat (C := B₂) hB₁
  obtain ⟨m3, e3, h3, c3⟩ := mu_nat (C := B₃) hB₂
  obtain ⟨m4, e4, h4, c4⟩ := mu_nat (C := B₄) hB₃
  have X1 := hX₁.1
  have X2 := hX₂.1
  have X3 := hX₃.1
  have X4 := hX₄.1
  by_cases hs : Small7 m2 m3 m4
  · rcases hs with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · -- `(0,0,0)`: the uncapped certificate vanishes
      refine seam_of_cert (by norm_num) (by norm_num) hw X1 X2 X3 X4 hB₁ hB₂ hB₃ hB₄
        (Or.inl ?_)
      rw [e2, e3, e4]; norm_num [Fval, J3, J4]
    · -- `(0,1,0)`
      have q12 := eq_of_mu_zero hB₁ hB₂ (by rw [e2]; norm_num)
      have q34 := eq_of_mu_zero hB₃ hB₄ (by rw [e4]; norm_num)
      subst q12 q34
      exact seam_s010 hB₁ hB₃ hB₃ (by omega) (by rw [Finset.inter_self]; exact hB₃) (by omega)
        (by rw [Finset.inter_assoc, Finset.inter_self]; omega) hw X1 X2 X3 X4
    · -- `(1,0,0)`
      have q23 := eq_of_mu_zero hB₂ hB₃ (by rw [e3]; norm_num)
      have q34 := eq_of_mu_zero hB₃ hB₄ (by rw [e4]; norm_num)
      subst q23 q34
      exact seam_s100 hB₁ hB₂ (by omega) hw X1 X2 X3 X4
    · -- `(0,0,1)`
      have q12 := eq_of_mu_zero hB₁ hB₂ (by rw [e2]; norm_num)
      have q23 := eq_of_mu_zero hB₂ hB₃ (by rw [e3]; norm_num)
      subst q12 q23
      exact seam_s001 hB₁ hB₁ hB₄ (by rw [Finset.inter_self]; exact hB₁) (by omega) (by omega)
        (by rw [Finset.inter_self]; omega) hw X1 X2 X3 X4
    · -- `(0,1,1)`: four shapes
      have q12 := eq_of_mu_zero hB₁ hB₂ (by rw [e2]; norm_num)
      subst q12
      obtain ⟨o1, o2, o3, o12, o13, o23⟩ := atoms3 B₁ B₃ B₄
      have hy6 : (B₁ ∩ B₃ ∩ B₄).card ≤ (B₁ ∩ B₃).card :=
        Finset.card_le_card Finset.inter_subset_left
      have hx : (B₁ ∩ B₃ ∩ B₄).card ≤ (B₁ ∩ B₄).card :=
        Finset.card_le_card (by intro c; simp only [Finset.mem_inter]; tauto)
      have hx7 : (B₁ ∩ B₄).card ≤ 7 := hB₁ ▸ Finset.card_le_card Finset.inter_subset_left
      simp only [hB₁, hB₃, hB₄] at o1 o2 o3
      have n1 : (0 : ℤ) ≤ ((B₁ \ (B₃ ∪ B₄)).card : ℤ) := Nat.cast_nonneg _
      have n2 : (0 : ℤ) ≤ ((B₃ \ (B₁ ∪ B₄)).card : ℤ) := Nat.cast_nonneg _
      have hy5 : 5 ≤ (B₁ ∩ B₃ ∩ B₄).card := by omega
      have hxy : (B₁ ∩ B₄).card ≤ (B₁ ∩ B₃ ∩ B₄).card + 1 := by omega
      rcases (show (B₁ ∩ B₃ ∩ B₄).card = 5 ∨ (B₁ ∩ B₃ ∩ B₄).card = 6 by omega) with hy | hy
      · rcases (show (B₁ ∩ B₄).card = 5 ∨ (B₁ ∩ B₄).card = 6 by omega) with hx' | hx'
        · exact seam_s011d hB₁ hB₃ hB₄ (by omega) (by omega) hx' hy hw X1 X2 X3 X4
        · exact seam_s011c hB₁ hB₃ hB₄ (by omega) (by omega) hx' hy hw X1 X2 X3 X4
      · rcases (show (B₁ ∩ B₄).card = 6 ∨ (B₁ ∩ B₄).card = 7 by omega) with hx' | hx'
        · exact seam_s011b hB₁ hB₃ hB₄ (by omega) (by omega) hx' hy hw X1 X2 X3 X4
        · exact seam_s011a hB₁ hB₃ hB₄ (by omega) (by omega) hx' hy hw X1 X2 X3 X4
    · -- `(0,2,0)`
      have q12 := eq_of_mu_zero hB₁ hB₂ (by rw [e2]; norm_num)
      have q34 := eq_of_mu_zero hB₃ hB₄ (by rw [e4]; norm_num)
      subst q12 q34
      exact seam_s020 hB₁ hB₃ hB₃ (by omega) (by rw [Finset.inter_self]; exact hB₃) (by omega)
        (by rw [Finset.inter_assoc, Finset.inter_self]; omega) hw X1 X2 X3 X4
  · refine seam_of_cert (by norm_num) (by norm_num) hw X1 X2 X3 X4 hB₁ hB₂ hB₃ hB₄
      (Or.inr ?_)
    rw [e2, e3, e4]
    exact cert7 h2 h3 h4 hs

end GridGen.Four
