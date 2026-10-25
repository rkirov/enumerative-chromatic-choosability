/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.CountBound
import GridGen.Four.Palette
import GridGen.Four.Pattern
import GridGen.Four.Cone

/-!
# Height four: lemmas for the bound for one state

For a proper column `s` and next lists `B₁, …, B₄` of `k` colours, the actual successor lists are
`Aᵢ = Bᵢ.erase sᵢ`. This file holds what the one-state bound needs about them: the uniform count
of a proper column (`card_sts_canon`), the state bits, the pattern-term weight `eta` and the
pattern sum `PS`, and the passage from a log bound to `GB ≥ GU · (1 + Λ)`
(`mul_one_add_le_of_log`). The bound itself is `state_bound6` (`State6.lean`) at `k = 6`.
-/

namespace GridGen.Four

open Finset Real GridGen.Lookback

/-- The uniform count of a proper column. -/
theorem card_sts_canon {k : ℕ} (hk : 4 ≤ k) {s : T4} (hs : Proper s) :
    ((sts ((range k).erase (r1 (canon s))) ((range k).erase (r2 (canon s)))
        ((range k).erase (r3 (canon s))) ((range k).erase (r4 (canon s)))).card : ℝ)
      = N4U ((k : ℝ) - 1) (c13 s) (c24 s) (c14 s) := by
  obtain ⟨u1, u2, u3, u4, u12, u23, u34, u123, u234, u1234⟩ := uniform_data hk hs
  rw [card_sts_rates, u1, u2, u3, u4, u12, u23, u34, u123, u234, u1234]
  unfold N4U N4; ring

/-- The pattern bits are bits, and `s₁ = s₄` excludes the other two equalities. -/
theorem cbits {s : T4} (hs : Proper s) :
    (c13 s = 0 ∨ c13 s = 1) ∧ (c24 s = 0 ∨ c24 s = 1) ∧ (c14 s = 0 ∨ c14 s = 1) ∧
      c13 s * c14 s = 0 ∧ c24 s * c14 s = 0 := by
  obtain ⟨p12, p23, p34⟩ := hs
  unfold c13 c24 c14
  refine ⟨by split_ifs <;> simp, by split_ifs <;> simp, by split_ifs <;> simp, ?_, ?_⟩
  · split_ifs with h1 h2 <;> simp
    exact p34 (h1 ▸ h2)
  · split_ifs with h1 h2 <;> simp
    exact p12 (h2 ▸ h1.symm ▸ rfl)

theorem mem_of_hb_zero {B : Finset ℕ} {c : ℕ} (h : hb B c = 0) : c ∈ B := by
  unfold hb at h; split_ifs at h with hc; exact hc; norm_num at h

theorem notMem_of_hb_one {B : Finset ℕ} {c : ℕ} (h : hb B c = 1) : c ∉ B := by
  unfold hb at h; split_ifs at h with hc; norm_num at h; exact hc

theorem zz_self (B : Finset ℕ) (a b : ℕ) : zz B B a b = 0 := by
  unfold zz; simp

/-! ### The pattern term and the bound for one state -/

/-- The pattern-term constant `η = (1-ρ)/(ρ(k-3))`. -/
noncomputable def eta (k : ℕ) : ℝ := (1 - rho k) / rho k / ((k - 3 : ℕ) : ℝ)

/-- A state colour in `B ∖ C`. -/
noncomputable def xin (B C : Finset ℕ) (c : ℕ) : ℝ := if c ∈ B ∧ c ∉ C then 1 else 0

theorem rho_pos' {k : ℕ} (hk : 5 ≤ k) : 0 < rho k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 5 := ⟨k - 5, by omega⟩
  by_cases h6 : m = 1
  · subst h6; rw [show (1 + 5 : ℕ) = 6 from rfl, rho_six]; norm_num
  by_cases h5 : m = 0
  · subst h5; rw [show (0 + 5 : ℕ) = 5 from rfl, rho_five]; norm_num
  exact rho_pos (rho_eq h5 h6)

theorem gw_mem {k : ℕ} {w : Wt} (hw : InBox k w) (t : T4) : rho k ≤ gw w t ∧ gw w t ≤ 1 := by
  obtain ⟨ha, ha', hb, hb', hc, hc'⟩ := hw
  have h1 : rho k ≤ 1 := ha.trans ha'
  unfold gw; split_ifs <;> first | exact ⟨h1, le_rfl⟩ | exact ⟨by assumption, by assumption⟩

theorem G_pos {k : ℕ} (hk : 5 ≤ k) {w : Wt} (hw : InBox k w) {A₁ A₂ A₃ A₄ : Finset ℕ}
    (h₁ : 3 ≤ A₁.card) (h₂ : 3 ≤ A₂.card) (h₃ : 3 ≤ A₃.card) (h₄ : 3 ≤ A₄.card) :
    0 < G w A₁ A₂ A₃ A₄ := by
  unfold G
  exact Finset.sum_pos (fun t _ => (rho_pos' hk).trans_le (gw_mem hw t).1)
    (sts_nonempty h₁ h₂ h₃ h₄)

theorem card_sdiff_tri (X Y Z : Finset ℕ) :
    ((X \ Z).card : ℝ) ≤ (X \ Y).card + (Y \ Z).card := by
  have h : X \ Z ⊆ (X \ Y) ∪ (Y \ Z) := by
    intro x; simp only [Finset.mem_sdiff, Finset.mem_union]; tauto
  have := (Finset.card_le_card h).trans (Finset.card_union_le _ _)
  exact_mod_cast this

theorem notin_le (B C : Finset ℕ) (c : ℕ) :
    (if c ∈ C then (0 : ℝ) else 1) ≤ hb B c + xin B C c := by
  unfold hb xin; split_ifs <;> simp_all

/-- The size of the difference from the reference palette. -/
noncomputable def PS (k : ℕ) (B₁ B₂ B₃ B₄ : Finset ℕ) (s : T4) : ℝ :=
  (mu k B₁ B₂ + 2 * mu k B₂ B₃ + mu k B₃ B₄)
    + 4 * (hb B₁ (r1 s) + hb B₂ (r2 s) + hb B₃ (r3 s) + hb B₄ (r4 s))
    + 4 * (xin B₁ B₂ (r1 s) + xin B₃ B₂ (r3 s) + xin B₄ B₂ (r4 s))

end GridGen.Four
