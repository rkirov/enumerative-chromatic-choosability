/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.CountBound
import GridGen.Four.Palette
import GridGen.Four.Pattern
import GridGen.Four.Cone

/-!
# Height four: the bound for one state

For a proper column `s` and next lists `B₁, …, B₄` of `k` colours, the actual successor lists are
`Aᵢ = Bᵢ.erase sᵢ`. Their data (sizes, consecutive, triple and quadruple intersections) are those
of `count_log_bound`, with `μᵢ = k - |Bᵢ₋₁ ∩ Bᵢ|`, the bonus bits `hᵢ = [sᵢ ∉ Bᵢ]` and the state
bits `zᵢ`; so `log (|sts A| / |sts U|) ≥ countBound`, `U` the uniform lists (`count_data`).
Adding the pattern term (`pattern_log_ge` against the reference palette of `exists_palette`)
gives `GB ≥ GU · (1 + Λ)` with `Λ` linear in the state bits (`state_bound`).
-/

namespace GridGen.Four

open Finset Real

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

/-- **The count bound of one state, from the lists.** -/
theorem count_data {k : ℕ} (hk7 : 7 ≤ k) (hkle : k ≤ 7) {B₁ B₂ B₃ B₄ : Finset ℕ}
    (hB₁ : B₁.card = k) (hB₂ : B₂.card = k) (hB₃ : B₃.card = k) (hB₄ : B₄.card = k)
    {s : T4} (hs : Proper s) :
    countBound ((k : ℝ) - 1) (mu k B₁ B₂) (mu k B₂ B₃) (mu k B₃ B₄)
        (zz B₁ B₂ (r1 s) (r2 s)) (zz B₂ B₃ (r2 s) (r3 s)) (zz B₃ B₄ (r3 s) (r4 s))
        (hb B₁ (r1 s)) (hb B₂ (r2 s)) (hb B₃ (r3 s)) (hb B₄ (r4 s)) (c13 s) (c24 s)
      ≤ log (((sts (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s)) (B₄.erase (r4 s))).card : ℝ)
          / (sts ((range k).erase (r1 (canon s))) ((range k).erase (r2 (canon s)))
              ((range k).erase (r3 (canon s))) ((range k).erase (r4 (canon s)))).card) := by
  have hs' := hs
  obtain ⟨p12, p23, p34⟩ := hs'
  obtain ⟨hc13, hc24, hc14, h1314, h2414⟩ := cbits hs
  rw [card_sts_canon (by omega) hs, card_sts_rates]
  set A₁ := B₁.erase (r1 s) with hA₁
  set A₂ := B₂.erase (r2 s) with hA₂
  set A₃ := B₃.erase (r3 s) with hA₃
  set A₄ := B₄.erase (r4 s) with hA₄
  have eN : (A₄.card : ℝ) * ((A₃.card : ℝ) * ((A₁.card : ℝ) * A₂.card - (A₁ ∩ A₂).card)
          - ((A₁.card : ℝ) * (A₂ ∩ A₃).card - (A₁ ∩ A₂ ∩ A₃).card))
        - ((A₁.card : ℝ) * ((A₂.card : ℝ) * (A₃ ∩ A₄).card - (A₂ ∩ A₃ ∩ A₄).card)
          - ((A₁ ∩ A₂).card * (A₃ ∩ A₄).card - (A₁ ∩ A₂ ∩ A₃ ∩ A₄).card))
      = N4 A₁.card A₂.card A₃.card A₄.card (A₁ ∩ A₂).card (A₂ ∩ A₃).card (A₃ ∩ A₄).card
          (A₁ ∩ A₂ ∩ A₃).card (A₂ ∩ A₃ ∩ A₄).card (A₁ ∩ A₂ ∩ A₃ ∩ A₄).card := by
    unfold N4; ring
  rw [eN]
  have cr : ∀ X Y : Finset ℕ, X ⊆ Y → (X.card : ℝ) ≤ Y.card := fun X Y h => by
    exact_mod_cast Finset.card_le_card h
  obtain ⟨hM30, hM3N⟩ := M3_bounds A₁ A₂ A₃
  obtain ⟨hM40, hM4N⟩ := M4_bounds A₁ A₂ A₃ A₄
  refine count_log_bound (by omega) hkle rfl (hb_cases _ _) (hb_cases _ _) (hb_cases _ _) (hb_cases _ _)
    (card_erase_hb hB₁ _) (card_erase_hb hB₂ _) (card_erase_hb hB₃ _) (card_erase_hb hB₄ _)
    (mu_nonneg hB₁) (mu_nonneg hB₂) (mu_nonneg hB₃)
    (by have := mu_le (k := k) B₁ B₂; linarith) (by have := mu_le (k := k) B₂ B₃; linarith)
    (by have := mu_le (k := k) B₃ B₄; linarith)
    (zz_nonneg _ _ _ _) (zz_nonneg _ _ _ _) (zz_nonneg _ _ _ _)
    (by rw [card_inter_erase hB₁ hB₂ p12]; ring) (by rw [card_inter_erase hB₂ hB₃ p23]; ring)
    (by rw [card_inter_erase hB₃ hB₄ p34]; ring)
    (Nat.cast_nonneg _) (cr _ _ inter_subset_left) (cr _ _ inter_subset_right)
    (Nat.cast_nonneg _) (cr _ _ inter_subset_left) (cr _ _ inter_subset_right)
    (Nat.cast_nonneg _) (cr _ _ inter_subset_left)
    (triple_ge A₁ A₂ A₃) (Nat.cast_nonneg _)
    (cr _ _ (inter_subset_left.trans inter_subset_left))
    (triple_ge A₂ A₃ A₄) (cr _ _ inter_subset_left)
    hM30 hM3N (by linarith) (by linarith) hc13 hc24 hc14 h1314 h2414 ?_ ?_
  · -- defect-free first three rows
    intro hμ2 hμ3 hh1 hh2 hh3
    have e12 := eq_of_mu_zero hB₁ hB₂ hμ2
    have e23 := eq_of_mu_zero hB₂ hB₃ hμ3
    have m1 := mem_of_hb_zero hh1
    have m2 := mem_of_hb_zero hh2
    have m3 := mem_of_hb_zero hh3
    rw [← e12] at m2 hB₂ ⊢
    rw [← e23, ← e12] at m3 ⊢
    refine ⟨zz_self _ _ _, zz_self _ _ _, ?_⟩
    rw [hA₁, hA₂, hA₃, ← e23, ← e12, card_erase3 hB₁ m1 m2 m3 p12 p23]
    unfold c13; ring
  · -- defect-free last three rows
    intro hμ2 hμ3 hμ4 hh2 hh3 hh4
    have e12 := eq_of_mu_zero hB₁ hB₂ hμ2
    have e23 := eq_of_mu_zero hB₂ hB₃ hμ3
    have e34 := eq_of_mu_zero hB₃ hB₄ hμ4
    have m2 := mem_of_hb_zero hh2
    have m3 := mem_of_hb_zero hh3
    have m4 := mem_of_hb_zero hh4
    rw [← e23, ← e12] at m3
    rw [← e34, ← e23, ← e12] at m4
    rw [← e12] at m2
    have z3 : zz B₂ B₃ (r2 s) (r3 s) = 0 := by rw [← e23]; exact zz_self _ _ _
    have z4 : zz B₃ B₄ (r3 s) (r4 s) = 0 := by rw [← e34]; exact zz_self _ _ _
    have z2 : zz B₁ B₂ (r1 s) (r2 s) = 0 := by rw [← e12]; exact zz_self _ _ _
    have t234 : ((A₂ ∩ A₃ ∩ A₄).card : ℝ) = (k : ℝ) - 1 - 2 + c24 s := by
      rw [hA₂, hA₃, hA₄, ← e34, ← e23, ← e12, card_erase3 hB₁ m2 m3 m4 p23 p34]
      unfold c24; ring
    refine ⟨z2, z3, z4, t234, ?_, ?_⟩
    · intro hh1
      have m1 := mem_of_hb_zero hh1
      constructor
      · rw [hA₁, hA₂, hA₃, ← e23, ← e12, card_erase3 hB₁ m1 m2 m3 p12 p23]
        unfold c13; ring
      · rw [hA₁, hA₂, hA₃, hA₄, ← e34, ← e23, ← e12, card_erase4 hB₁ m1 m2 m3 m4 p12 p23 p34]
        unfold c13 c24 c14; ring
    · intro hh1
      have n1 := notMem_of_hb_one hh1
      have a1 : A₁ = B₁ := by rw [hA₁]; exact Finset.erase_eq_of_notMem n1
      have n13 : r1 s ≠ r3 s := fun h => n1 (h ▸ m3)
      have n14 : r1 s ≠ r4 s := fun h => n1 (h ▸ m4)
      refine ⟨?_, ?_, by unfold c13; simp [n13], by unfold c14; simp [n14]⟩
      · have : A₁ ∩ A₂ ∩ A₃ = (B₁.erase (r2 s)) ∩ (B₁.erase (r3 s)) := by
          rw [a1, hA₂, hA₃, ← e23, ← e12]
          ext x; simp only [Finset.mem_inter, Finset.mem_erase]; tauto
        rw [this, card_erase2 hB₁ m2 m3 p23]; ring
      · congr 2
        rw [a1, hA₂, hA₃, hA₄, ← e34, ← e23, ← e12]
        ext x; simp only [Finset.mem_inter, Finset.mem_erase]; tauto

/-! ### The pattern term and the bound for one state -/

/-- The pattern-term constant `η = (1-ρ)/(ρ(k-3))`. -/
noncomputable def eta (k : ℕ) : ℝ := (1 - rho k) / rho k / ((k - 3 : ℕ) : ℝ)

/-- A state colour in `B ∖ C`. -/
noncomputable def xin (B C : Finset ℕ) (c : ℕ) : ℝ := if c ∈ B ∧ c ∉ C then 1 else 0

/-- **The log gain of one state.** -/
noncomputable def Lam (k : ℕ) (B₁ B₂ B₃ B₄ : Finset ℕ) (s : T4) : ℝ :=
  countBound ((k : ℝ) - 1) (mu k B₁ B₂) (mu k B₂ B₃) (mu k B₃ B₄)
      (zz B₁ B₂ (r1 s) (r2 s)) (zz B₂ B₃ (r2 s) (r3 s)) (zz B₃ B₄ (r3 s) (r4 s))
      (hb B₁ (r1 s)) (hb B₂ (r2 s)) (hb B₃ (r3 s)) (hb B₄ (r4 s)) (c13 s) (c24 s)
    - eta k * ((mu k B₁ B₂ + 2 * mu k B₂ B₃ + mu k B₃ B₄)
      + 4 * (hb B₁ (r1 s) + hb B₂ (r2 s) + hb B₃ (r3 s) + hb B₄ (r4 s))
      + 4 * (xin B₁ B₂ (r1 s) + xin B₃ B₂ (r3 s) + xin B₄ B₂ (r4 s)))

theorem rho_pos' {k : ℕ} (hk : 5 ≤ k) : 0 < rho k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 5 := ⟨k - 5, by omega⟩
  by_cases h6 : m = 1
  · subst h6; rw [show (1 + 5 : ℕ) = 6 from rfl, rho_six]; norm_num
  exact rho_pos (rho_eq h6)

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

theorem card_sdiff_mu {k : ℕ} {B : Finset ℕ} (hB : B.card = k) (C : Finset ℕ) :
    ((B \ C).card : ℝ) = mu k B C := by
  unfold mu
  have := Finset.card_sdiff_add_card_inter B C
  rw [hB] at this
  have : ((B \ C).card : ℝ) + (B ∩ C).card = k := by exact_mod_cast this
  linarith

theorem mu_comm (k : ℕ) (B C : Finset ℕ) : mu k B C = mu k C B := by
  unfold mu; rw [Finset.inter_comm]

theorem card_sdiff_tri (X Y Z : Finset ℕ) :
    ((X \ Z).card : ℝ) ≤ (X \ Y).card + (Y \ Z).card := by
  have h : X \ Z ⊆ (X \ Y) ∪ (Y \ Z) := by
    intro x; simp only [Finset.mem_sdiff, Finset.mem_union]; tauto
  have := (Finset.card_le_card h).trans (Finset.card_union_le _ _)
  exact_mod_cast this

theorem notin_le (B C : Finset ℕ) (c : ℕ) :
    (if c ∈ C then (0 : ℝ) else 1) ≤ hb B c + xin B C c := by
  unfold hb xin; split_ifs <;> simp_all

theorem card_ge_of_erase {k : ℕ} {B : Finset ℕ} (hB : B.card = k) (c : ℕ) :
    k - 1 ≤ (B.erase c).card := by
  have := Finset.pred_card_le_card_erase (s := B) (a := c); omega

/-- The count part of the gain. -/
noncomputable def CB (k : ℕ) (B₁ B₂ B₃ B₄ : Finset ℕ) (s : T4) : ℝ :=
  countBound ((k : ℝ) - 1) (mu k B₁ B₂) (mu k B₂ B₃) (mu k B₃ B₄)
      (zz B₁ B₂ (r1 s) (r2 s)) (zz B₂ B₃ (r2 s) (r3 s)) (zz B₃ B₄ (r3 s) (r4 s))
      (hb B₁ (r1 s)) (hb B₂ (r2 s)) (hb B₃ (r3 s)) (hb B₄ (r4 s)) (c13 s) (c24 s)

/-- The size of the difference from the reference palette. -/
noncomputable def PS (k : ℕ) (B₁ B₂ B₃ B₄ : Finset ℕ) (s : T4) : ℝ :=
  (mu k B₁ B₂ + 2 * mu k B₂ B₃ + mu k B₃ B₄)
    + 4 * (hb B₁ (r1 s) + hb B₂ (r2 s) + hb B₃ (r3 s) + hb B₄ (r4 s))
    + 4 * (xin B₁ B₂ (r1 s) + xin B₃ B₂ (r3 s) + xin B₄ B₂ (r4 s))

theorem Lam_eq_CB (k : ℕ) (B₁ B₂ B₃ B₄ : Finset ℕ) (s : T4) :
    Lam k B₁ B₂ B₃ B₄ s = CB k B₁ B₂ B₃ B₄ s - eta k * PS k B₁ B₂ B₃ B₄ s := rfl

/-- **The gain with the pattern term capped** at `(1-ρ)/ρ`. -/
noncomputable def Lamc (k : ℕ) (B₁ B₂ B₃ B₄ : Finset ℕ) (s : T4) : ℝ :=
  CB k B₁ B₂ B₃ B₄ s - min (eta k * PS k B₁ B₂ B₃ B₄ s) ((1 - rho k) / rho k)

/-- **The log gain of one state**, with and without the cap. -/
theorem state_log_bound {k : ℕ} (hk7 : 7 ≤ k) (hkle : k ≤ 7) {w : Wt} (hw : InBox k w)
    {B₁ B₂ B₃ B₄ : Finset ℕ}
    (hB₁ : B₁.card = k) (hB₂ : B₂.card = k) (hB₃ : B₃.card = k) (hB₄ : B₄.card = k)
    {s : T4} (hs : Proper s) :
    0 < GU k w s ∧ 0 < GB w B₁ B₂ B₃ B₄ s ∧
      Lamc k B₁ B₂ B₃ B₄ s ≤ log (GB w B₁ B₂ B₃ B₄ s / GU k w s) := by
  obtain ⟨P, f, hPc, hPr, hf, hdiff⟩ := exists_palette (by omega) hB₂ s
  have hk5 : 5 ≤ k := by omega
  have hρ := rho_pos' hk5
  have hρ1 := rho_le_one k hk5
  -- the pattern term
  have hpat := pattern_log_ge (A₁ := B₁.erase (r1 s)) (A₂ := B₂.erase (r2 s))
    (A₃ := B₃.erase (r3 s)) (A₄ := B₄.erase (r4 s)) (U₁ := P.erase (r1 s)) (U₂ := P.erase (r2 s))
    (U₃ := P.erase (r3 s)) (U₄ := P.erase (r4 s)) (by omega)
    (card_ge_of_erase hB₁ _) (card_ge_of_erase hB₂ _) (card_ge_of_erase hB₃ _)
    (card_ge_of_erase hB₄ _) (card_ge_of_erase hPc _) (card_ge_of_erase hPc _)
    (card_ge_of_erase hPc _) (card_ge_of_erase hPc _) w hρ hρ1 (gw_mem hw)
  rw [G_erase_eq_GU w (by omega) hs hPc hPr, card_erase_eq_canon (by omega) hs hPc hPr] at hpat
  -- the size of the differences
  have m12 := card_sdiff_mu hB₁ B₂
  have m21 := card_sdiff_mu hB₂ B₁
  have m23 := card_sdiff_mu hB₂ B₃
  have m32 := card_sdiff_mu hB₃ B₂
  have m34 := card_sdiff_mu hB₃ B₄
  have m43 := card_sdiff_mu hB₄ B₃
  rw [mu_comm k B₂ B₁] at m21
  rw [mu_comm k B₃ B₂] at m32
  rw [mu_comm k B₄ B₃] at m43
  have t42 := card_sdiff_tri B₄ B₃ B₂
  have t24 := card_sdiff_tri B₂ B₃ B₄
  have s22 : ((B₂ \ B₂).card : ℝ) = 0 := by simp
  obtain ⟨d1, d1'⟩ := hdiff B₁ (r1 s)
  obtain ⟨d2, d2'⟩ := hdiff B₂ (r2 s)
  obtain ⟨d3, d3'⟩ := hdiff B₃ (r3 s)
  obtain ⟨d4, d4'⟩ := hdiff B₄ (r4 s)
  have hj : jsum B₂ s ≤ (hb B₁ (r1 s) + hb B₂ (r2 s) + hb B₃ (r3 s) + hb B₄ (r4 s))
      + (xin B₁ B₂ (r1 s) + xin B₃ B₂ (r3 s) + xin B₄ B₂ (r4 s)) := by
    unfold jsum
    have j1 := notin_le B₁ B₂ (r1 s)
    have j3 := notin_le B₃ B₂ (r3 s)
    have j4 := notin_le B₄ B₂ (r4 s)
    have j2 : (if r2 s ∈ B₂ then (0 : ℝ) else 1) = hb B₂ (r2 s) := rfl
    linarith
  set T := mu k B₁ B₂ + 2 * mu k B₂ B₃ + mu k B₃ B₄ with hT
  set Hs := hb B₁ (r1 s) + hb B₂ (r2 s) + hb B₃ (r3 s) + hb B₄ (r4 s) with hHs
  set Xs := xin B₁ B₂ (r1 s) + xin B₃ B₂ (r3 s) + xin B₄ B₂ (r4 s) with hXs
  set SA : ℝ := (((B₁.erase (r1 s)) \ (P.erase (r1 s))).card : ℝ)
    + ((B₂.erase (r2 s)) \ (P.erase (r2 s))).card + ((B₃.erase (r3 s)) \ (P.erase (r3 s))).card
    + ((B₄.erase (r4 s)) \ (P.erase (r4 s))).card with hSA
  set SU : ℝ := (((P.erase (r1 s)) \ (B₁.erase (r1 s))).card : ℝ)
    + ((P.erase (r2 s)) \ (B₂.erase (r2 s))).card + ((P.erase (r3 s)) \ (B₃.erase (r3 s))).card
    + ((P.erase (r4 s)) \ (B₄.erase (r4 s))).card with hSU
  have hmax : max SA SU ≤ T + 4 * Hs + 4 * Xs := by
    apply max_le <;> linarith
  have hk3 : (0 : ℝ) < ((k - 3 : ℕ) : ℝ) := by
    have : 0 < k - 3 := by omega
    exact_mod_cast this
  have hη : -(eta k * (T + 4 * Hs + 4 * Xs))
      ≤ -((1 - rho k) / rho k * (max SA SU / ((k - 3 : ℕ) : ℝ))) := by
    have e : eta k * (T + 4 * Hs + 4 * Xs)
        = (1 - rho k) / rho k * ((T + 4 * Hs + 4 * Xs) / ((k - 3 : ℕ) : ℝ)) := by
      unfold eta; ring
    rw [e, neg_le_neg_iff]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hmax hk3.le)
      (div_nonneg (by linarith) hρ.le)
  -- the count term
  have hcnt := count_data hk7 hkle hB₁ hB₂ hB₃ hB₄ hs
  -- positivity
  have c1 := card_ge_of_erase hB₁ (r1 s)
  have c2 := card_ge_of_erase hB₂ (r2 s)
  have c3 := card_ge_of_erase hB₃ (r3 s)
  have c4 := card_ge_of_erase hB₄ (r4 s)
  have u : ∀ i, 3 ≤ ((range k).erase i).card := fun i => by
    have := card_ge_of_erase (card_range k) i; omega
  have hGA : 0 < G w (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s)) (B₄.erase (r4 s)) :=
    G_pos hk5 hw (by omega) (by omega) (by omega) (by omega)
  have hGU : 0 < GU k w s := G_pos hk5 hw (u _) (u _) (u _) (u _)
  have hNA : (0 : ℝ) < (sts (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s))
      (B₄.erase (r4 s))).card := by
    exact_mod_cast (sts_nonempty (by omega) (by omega) (by omega) (by omega)).card_pos
  have hNU : (0 : ℝ) < (sts ((range k).erase (r1 (canon s))) ((range k).erase (r2 (canon s)))
      ((range k).erase (r3 (canon s))) ((range k).erase (r4 (canon s)))).card := by
    exact_mod_cast (sts_nonempty (u _) (u _) (u _) (u _)).card_pos
  -- combine
  have hlog : Lamc k B₁ B₂ B₃ B₄ s ≤ log (GB w B₁ B₂ B₃ B₄ s / GU k w s) := by
    have e : GB w B₁ B₂ B₃ B₄ s / GU k w s
        = ((sts (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s)) (B₄.erase (r4 s))).card
            / (sts ((range k).erase (r1 (canon s))) ((range k).erase (r2 (canon s)))
              ((range k).erase (r3 (canon s))) ((range k).erase (r4 (canon s)))).card)
          * ((G w (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s)) (B₄.erase (r4 s))
              / (sts (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s)) (B₄.erase (r4 s))).card)
            / (GU k w s / (sts ((range k).erase (r1 (canon s))) ((range k).erase (r2 (canon s)))
              ((range k).erase (r3 (canon s))) ((range k).erase (r4 (canon s)))).card)) := by
      unfold GB; field_simp
    rw [e, Real.log_mul (by positivity) (by positivity)]
    -- the pattern term is at least `log ρ ≥ -(1-ρ)/ρ`
    have hGAlow : rho k * (sts (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s))
        (B₄.erase (r4 s))).card
        ≤ G w (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s)) (B₄.erase (r4 s)) := by
      have := Finset.card_nsmul_le_sum (sts (B₁.erase (r1 s)) (B₂.erase (r2 s))
        (B₃.erase (r3 s)) (B₄.erase (r4 s))) (gw w) (rho k) (fun t _ => (gw_mem hw t).1)
      rw [G]; simpa [nsmul_eq_mul, mul_comm] using this
    have hGUup : GU k w s ≤ (sts ((range k).erase (r1 (canon s))) ((range k).erase (r2 (canon s)))
        ((range k).erase (r3 (canon s))) ((range k).erase (r4 (canon s)))).card := by
      have := Finset.sum_le_card_nsmul (sts ((range k).erase (r1 (canon s)))
        ((range k).erase (r2 (canon s))) ((range k).erase (r3 (canon s)))
        ((range k).erase (r4 (canon s)))) (gw w) 1 (fun t _ => (gw_mem hw t).2)
      unfold GU G; simpa [nsmul_eq_mul] using this
    have hcap : -((1 - rho k) / rho k)
        ≤ log ((G w (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s)) (B₄.erase (r4 s))
              / (sts (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s)) (B₄.erase (r4 s))).card)
            / (GU k w s / (sts ((range k).erase (r1 (canon s))) ((range k).erase (r2 (canon s)))
              ((range k).erase (r3 (canon s))) ((range k).erase (r4 (canon s)))).card)) := by
      have hx : rho k ≤ (G w (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s))
            (B₄.erase (r4 s)) / (sts (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s))
              (B₄.erase (r4 s))).card)
            / (GU k w s / (sts ((range k).erase (r1 (canon s))) ((range k).erase (r2 (canon s)))
              ((range k).erase (r3 (canon s))) ((range k).erase (r4 (canon s)))).card) := by
        rw [div_div_eq_mul_div, le_div_iff₀ hGU, div_mul_eq_mul_div, le_div_iff₀ hNA]
        calc rho k * GU k w s * _ ≤ rho k * _ * _ :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hGUup hρ.le) hNA.le
          _ = _ := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hGAlow hNU.le
      have hl := Real.log_le_log hρ hx
      have hl2 : 1 - 1 / rho k ≤ log (rho k) := by
        have := Real.one_sub_inv_le_log_of_pos hρ; simpa [one_div] using this
      have e : -((1 - rho k) / rho k) = 1 - 1 / rho k := by field_simp; ring
      linarith
    have hη' : -(eta k * PS k B₁ B₂ B₃ B₄ s) ≤ -((1 - rho k) / rho k * (max SA SU
        / ((k - 3 : ℕ) : ℝ))) := hη
    unfold Lamc CB
    rcases le_total (eta k * PS k B₁ B₂ B₃ B₄ s) ((1 - rho k) / rho k) with hm | hm
    · rw [min_eq_left hm]; linarith
    · rw [min_eq_right hm]; linarith
  exact ⟨hGU, by unfold GB; exact hGA, hlog⟩

/-- From a log gain to the product form `GB ≥ GU · (1 + λ)`. -/
theorem mul_one_add_le_of_log {u b l : ℝ} (hu : 0 < u) (hb : 0 < b) (h : l ≤ log (b / u)) :
    u * (1 + l) ≤ b := by
  have hpos : 0 < b / u := div_pos hb hu
  have h2 : exp l ≤ b / u := by rw [← Real.exp_log hpos]; exact Real.exp_le_exp.mpr h
  have h3 : 1 + l ≤ b / u := (by rw [add_comm]; exact Real.add_one_le_exp _ : 1 + l ≤ _).trans h2
  calc u * (1 + l) ≤ u * (b / u) := mul_le_mul_of_nonneg_left h3 hu.le
    _ = b := mul_div_cancel₀ _ hu.ne'

/-- **The bound for one state**, capped: `GB ≥ GU · (1 + Λc)`. -/
theorem state_bound_cap {k : ℕ} (hk7 : 7 ≤ k) (hkle : k ≤ 7) {w : Wt} (hw : InBox k w)
    {B₁ B₂ B₃ B₄ : Finset ℕ}
    (hB₁ : B₁.card = k) (hB₂ : B₂.card = k) (hB₃ : B₃.card = k) (hB₄ : B₄.card = k)
    {s : T4} (hs : Proper s) :
    GU k w s * (1 + Lamc k B₁ B₂ B₃ B₄ s) ≤ GB w B₁ B₂ B₃ B₄ s := by
  obtain ⟨hu, hb, hl⟩ := state_log_bound hk7 hkle hw hB₁ hB₂ hB₃ hB₄ hs
  exact mul_one_add_le_of_log hu hb hl

/-- **The bound for one state**: `GB ≥ GU · (1 + Λ)`. -/
theorem state_bound {k : ℕ} (hk7 : 7 ≤ k) (hkle : k ≤ 7) {w : Wt} (hw : InBox k w)
    {B₁ B₂ B₃ B₄ : Finset ℕ}
    (hB₁ : B₁.card = k) (hB₂ : B₂.card = k) (hB₃ : B₃.card = k) (hB₄ : B₄.card = k)
    {s : T4} (hs : Proper s) :
    GU k w s * (1 + Lam k B₁ B₂ B₃ B₄ s) ≤ GB w B₁ B₂ B₃ B₄ s := by
  obtain ⟨hu, hb, hl⟩ := state_log_bound hk7 hkle hw hB₁ hB₂ hB₃ hB₄ hs
  refine mul_one_add_le_of_log hu hb (le_trans ?_ hl)
  rw [Lam_eq_CB, Lamc]
  linarith [min_le_left (eta k * PS k B₁ B₂ B₃ B₄ s) ((1 - rho k) / rho k)]

end GridGen.Four
