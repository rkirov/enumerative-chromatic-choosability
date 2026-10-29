/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.K5.State
import GridGen.Five.Init5

/-!
# Height five at `k = 5`: the initial inequality

`ai_research_notes/cx/h5k5/NOTE.md` §5 (Codex), checked in `H5_K5_REVIEW_2026-10-28.md` (d).
A column of `5`-lists `X` weighs at least the uniform column `{0,…,4}⁵` for every weight of the
cone (`init55Holds`):

* if the lists coincide, by relabelling (`G_range_eq`);
* otherwise `|sts X| ≥ 1344 = (21/20) · 1280` (the greedy count, `count_init`), and the chain
  polytope at the size vector `(5, 5, 5, 5, 5)` bounds the ratio of the uniform average to the
  actual one by `R_init = 1.019305484…` (`pattern_init`), below `21/20`.
-/

namespace GridGen.Five.K5

open Finset GridGen.Five GridGen.Five.Ex5

/-! ### The pattern lemma against any row -/

/-- The ray checks of a certificate against a row `v` with total `NV` and ratio `R`. -/
def rowOK (C : PatCert) (v : Fin 11 → ℕ) (NV R : ℕ) : Bool :=
  (List.range 5).all (fun k =>
    decide (1000000000 * DP * ∑ j, v j * Fv k j + R * NV * zsumL C.ev (C.zs.getD k [])
      ≤ R * NV * C.lam.getD k 0)) &&
  decide (1000000000 * DP * (∑ j, v j * (qL j + qU j) + 5 * NV)
      + R * NV * (zsumL C.ev (C.zs.getD 5 []) + 5 * DP) ≤ R * NV * C.lam.getD 5 0)

/-- **The pattern lemma against a row**: if a certificate's dual checks pass at all generators
and its ratio checks pass against `v`, then
`10⁹ · |sts A| · Σ vⱼ wⱼ ≤ R · NV · G w A` on the cone. -/
theorem pattern_row {w : Wt5} (hw : InCone5 w) {A₁ A₂ A₃ A₄ A₅ : Finset ℕ} {nv : List ℕ}
    (hX : ∀ i < 5, nv.getD i 0 ≤ (bl A₁ A₂ A₃ A₄ A₅ i).card) (hn : ∀ i < 5, 1 ≤ frcL nv i)
    {C : PatCert} (hev : ∀ ev ∈ C.ev, peelOKB ev = true)
    (hpt : ∀ k < 6, ptOK nv C k = true) (v : Fin 11 → ℕ) (NV R : ℕ) (hNV : ∑ j, v j = NV)
    (hrow : rowOK C v NV R = true) :
    (1000000000 : ℝ) * (sts A₁ A₂ A₃ A₄ A₅).card * ∑ j, (v j : ℝ) * w j
      ≤ R * NV * G w A₁ A₂ A₃ A₄ A₅ := by
  simp only [rowOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq]
    at hrow
  obtain ⟨hray, hmid⟩ := hrow
  have hB : ∀ ev ∈ C.ev, evB nv ev * ((sts A₁ A₂ A₃ A₄ A₅).filter
      (fun t => evHolds ev t = true)).card ≤ (sts A₁ A₂ A₃ A₄ A₅).card :=
    fun ev he => ev_count hX hn ev (hev ev he)
  rw [G_eq_sum]
  have hD : 0 < DP := by decide
  have hE : ((1000000000 : ℕ) : ℝ) = 1000000000 := by norm_num
  rw [← hE]
  rcases hw with hq | ⟨k, hk, rfl⟩
  · have hl := lp_count5 (k := 5) hev hB (hpt 5 (by norm_num))
    have hG' : ((∑ t ∈ sts A₁ A₂ A₃ A₄ A₅, gval 5 (orb t) : ℕ) : ℝ)
        - 5 * (sts A₁ A₂ A₃ A₄ A₅).card ≤ 2000000 * ∑ t ∈ sts A₁ A₂ A₃ A₄ A₅, w (orb t) := by
      push_cast
      rw [Finset.mul_sum, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_le_sum fun t _ => ?_
      have h2' : (qU (orb t) : ℝ) ≤ qL (orb t) + 5 := by exact_mod_cast (qU_le (orb t)).2
      have : (qL (orb t) : ℝ) ≤ 1000000 * w (orb t) := by
        have := (hq (orb t)).1; rw [div_le_iff₀ (by norm_num)] at this; linarith
      simp only [gval, show ¬ (5 < 5) from by norm_num, ite_false]
      push_cast
      linarith
    have hV : 2000000 * ∑ j, (v j : ℝ) * w j
        ≤ ((∑ j, v j * (qL j + qU j) : ℕ) : ℝ) + 5 * NV := by
      rw [← hNV]
      push_cast
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun j _ => ?_
      have h1' : (qL j : ℝ) ≤ qU j := by exact_mod_cast (qU_le j).1
      have : 1000000 * w j ≤ (qU j : ℝ) := by
        have := (hq j).2; rw [le_div_iff₀ (by norm_num)] at this; linarith
      have h2' : (qU j : ℝ) ≤ qL j + 5 := by exact_mod_cast (qU_le j).2
      have hv : (0 : ℝ) ≤ v j := Nat.cast_nonneg _
      nlinarith
    generalize C.lam.getD 5 0 = Λ at hl hmid
    generalize zsumL C.ev (C.zs.getD 5 []) = Z at hl hmid
    generalize ∑ t ∈ sts A₁ A₂ A₃ A₄ A₅, gval 5 (orb t) = S at hl hG'
    generalize (sts A₁ A₂ A₃ A₄ A₅).card = N at hl hG' ⊢
    generalize ∑ j, v j * (qL j + qU j) = Mv at hmid hV
    generalize DP = D at hl hmid hD
    generalize (1000000000 : ℕ) = E at hmid ⊢
    generalize ∑ t ∈ sts A₁ A₂ A₃ A₄ A₅, w (orb t) = G at hG' ⊢
    generalize ∑ j, (v j : ℝ) * w j = Vw at hV ⊢
    have hlR : (Λ : ℝ) * N ≤ D * S + Z * N := by exact_mod_cast hl
    have hmR : (E : ℝ) * D * (Mv + 5 * NV) + R * NV * (Z + 5 * D) ≤ R * NV * Λ := by
      exact_mod_cast hmid
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    have hRN : (0 : ℝ) ≤ R * NV := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hD' : (0 : ℝ) < D := by exact_mod_cast hD
    have hE0 : (0 : ℝ) ≤ E := Nat.cast_nonneg _
    have k1 := mul_le_mul_of_nonneg_left hV (mul_nonneg (mul_nonneg hE0 hD'.le) hN0)
    have k2 := mul_le_mul_of_nonneg_left hG' (mul_nonneg hRN hD'.le)
    have k3 := mul_le_mul_of_nonneg_left hlR hRN
    have k4 := mul_le_mul_of_nonneg_right hmR hN0
    have key : (E : ℝ) * N * Vw * (2000000 * D) ≤ R * NV * G * (2000000 * D) := by linarith
    exact le_of_mul_le_mul_right key (by positivity)
  · have hl := lp_count5 (k := k) hev hB (hpt k (by omega))
    have hr := hray k hk
    have hF0 : (0 : ℝ) < Fv k 0 := by exact_mod_cast Fv_pos k (by omega)
    have eS : ∑ t ∈ sts A₁ A₂ A₃ A₄ A₅, rayW k (orb t)
        = ((∑ t ∈ sts A₁ A₂ A₃ A₄ A₅, gval k (orb t) : ℕ) : ℝ) / Fv k 0 := by
      push_cast; rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [rayW, gval, hk, ite_true]
    have eV : ∑ j, (v j : ℝ) * rayW k j = ((∑ j, v j * Fv k j : ℕ) : ℝ) / Fv k 0 := by
      push_cast; rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [rayW]; ring
    rw [eS, eV]
    generalize C.lam.getD k 0 = Λ at hl hr
    generalize zsumL C.ev (C.zs.getD k []) = Z at hl hr
    generalize ∑ t ∈ sts A₁ A₂ A₃ A₄ A₅, gval k (orb t) = S at hl ⊢
    generalize (sts A₁ A₂ A₃ A₄ A₅).card = N at hl ⊢
    generalize ∑ j, v j * Fv k j = Fw at hr ⊢
    generalize DP = D at hl hr hD
    generalize (1000000000 : ℕ) = E at hr ⊢
    have hlR : (Λ : ℝ) * N ≤ D * S + Z * N := by exact_mod_cast hl
    have hrR : (E : ℝ) * D * Fw + R * NV * Z ≤ R * NV * Λ := by exact_mod_cast hr
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    have hRN : (0 : ℝ) ≤ R * NV := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hD' : (0 : ℝ) < D := by exact_mod_cast hD
    have k1 := mul_le_mul_of_nonneg_right hrR hN0
    have k2 := mul_le_mul_of_nonneg_left hlR hRN
    have keyR : (E : ℝ) * N * Fw * D ≤ R * NV * S * D := by linarith
    have keyR' := le_of_mul_le_mul_right keyR hD'
    rw [mul_div_assoc', mul_div_assoc', div_le_div_iff_of_pos_right hF0]
    linarith

/-! ### The initial inequality -/

/-- The orbit counts of the uniform column `{0,…,4}⁵`. -/
def U0 : Fin 11 → ℕ := ![20, 120, 60, 120, 240, 60, 240, 60, 120, 120, 120]

theorem U0_counts : ∀ o : Fin 11,
    ((sts (range 5) (range 5) (range 5) (range 5) (range 5)).filter (fun t => orb t = o)).card
      = U0 o := by decide +kernel

/-- The ratio bound of the initial inequality, times `10⁹`. -/
def Rinit : ℕ := 1019305484

/-- The certificate at `(5, 5, 5, 5, 5)` passes against the uniform column. -/
theorem init_cert_ok : rowOK (patCerts.getD 31 default) U0 1280 Rinit = true := by decide +kernel

/-- **The count of a mismatched column of `5`-lists.** -/
def countInit : Bool :=
  (List.range 6).all fun a => (List.range 6).all fun b => (List.range 6).all fun c =>
    (List.range 6).all fun d => (a == 5 && b == 5 && c == 5 && d == 5) ||
      decide (1344 + kapM 5 5 5 5 5 a b c d ≤ kapP 5 5 5 5 5 a b c d)

theorem countInit_ok : countInit = true := by decide +kernel

theorem G_eq_orbsum (w : Wt5) (A₁ A₂ A₃ A₄ A₅ : Finset ℕ) :
    G w A₁ A₂ A₃ A₄ A₅
      = ∑ o, (((sts A₁ A₂ A₃ A₄ A₅).filter (fun t => orb t = o)).card : ℝ) * w o :=
  G_eq_sum_orb w A₁ A₂ A₃ A₄ A₅

/-- **The height-five initial inequality at `k = 5`.** -/
theorem init55Holds : Init55Holds := by
  intro w hw X₁ X₂ X₃ X₄ X₅ h₁ h₂ h₃ h₄ h₅
  show G w (range 5) (range 5) (range 5) (range 5) (range 5) ≤ G w X₁ X₂ X₃ X₄ X₅
  have i2 : (X₁ ∩ X₂).card ≤ 5 := h₁ ▸ card_le_card inter_subset_left
  have i3 : (X₂ ∩ X₃).card ≤ 5 := h₂ ▸ card_le_card inter_subset_left
  have i4 : (X₃ ∩ X₄).card ≤ 5 := h₃ ▸ card_le_card inter_subset_left
  have i5 : (X₄ ∩ X₅).card ≤ 5 := h₄ ▸ card_le_card inter_subset_left
  by_cases hS : (X₁ ∩ X₂).card = 5 ∧ (X₂ ∩ X₃).card = 5 ∧ (X₃ ∩ X₄).card = 5 ∧
      (X₄ ∩ X₅).card = 5
  · -- no mismatch: the lists are equal
    have eq : ∀ {U V : Finset ℕ}, U.card = 5 → V.card = 5 → (U ∩ V).card = 5 → U = V := by
      intro U V hU hV h
      have h1 : U ∩ V = U := Finset.eq_of_subset_of_card_le inter_subset_left (by omega)
      have h2 : U ∩ V = V := Finset.eq_of_subset_of_card_le inter_subset_right (by omega)
      rw [← h1, h2]
    obtain ⟨s2, s3, s4, s5⟩ := hS
    have e12 := eq h₁ h₂ s2
    have e23 := eq h₂ h₃ s3
    have e34 := eq h₃ h₄ s4
    have e45 := eq h₄ h₅ s5
    subst e12 e23 e34 e45
    rw [G_range_eq w h₁]
  · -- a mismatch: at least `1344` columns
    have hN : 1344 ≤ (sts X₁ X₂ X₃ X₄ X₅).card := by
      have hg := N5g_le_card4 (A₁ := X₁) (A₂ := X₂) (A₃ := X₃) (A₄ := X₄) (A₅ := X₅)
        (by omega) (by omega) (by omega) (by omega)
      rw [h₁, h₂, h₃, h₄, h₅, ← kapP_kapM] at hg
      have hc := countInit_ok
      simp only [countInit, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.and_eq_true,
        beq_iff_eq, decide_eq_true_eq] at hc
      rcases hc (X₁ ∩ X₂).card (by omega) (X₂ ∩ X₃).card (by omega) (X₃ ∩ X₄).card (by omega)
        (X₄ ∩ X₅).card (by omega) with h | h
      · exact absurd ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩ hS
      · omega
    have hX : ∀ i < 5, [5, 5, 5, 5, 5].getD i 0 ≤ (bl X₁ X₂ X₃ X₄ X₅ i).card := by
      intro i hi; interval_cases i <;> simp [bl, h₁, h₂, h₃, h₄, h₅]
    have hn : ∀ i < 5, 1 ≤ frcL [5, 5, 5, 5, 5] i := by
      intro i hi; interval_cases i <;> decide
    have hok : patOK [5, 5, 5, 5, 5] (patCerts.getD 31 default) = true := by
      have h := allPat_ok
      simp only [allPat, List.all_eq_true] at h
      exact h 5 (by simp) 5 (by simp) 5 (by simp) 5 (by simp) 5 (by simp)
    simp only [patOK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hok
    obtain ⟨⟨⟨hev, hpt⟩, -⟩, -⟩ := hok
    have hp := pattern_row hw hX hn hev hpt U0 1280 Rinit (by decide) init_cert_ok
    have hU : G w (range 5) (range 5) (range 5) (range 5) (range 5) = ∑ j, (U0 j : ℝ) * w j := by
      rw [G_eq_orbsum]
      exact Finset.sum_congr rfl fun o _ => by rw [U0_counts]
    rw [hU]
    have hU0 : 0 ≤ ∑ j, (U0 j : ℝ) * w j :=
      Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (cone_nonneg hw j)
    have hN' : (1344 : ℝ) ≤ (sts X₁ X₂ X₃ X₄ X₅).card := by exact_mod_cast hN
    have hR : (Rinit : ℝ) = 1019305484 := by norm_num [Rinit]
    rw [hR] at hp
    push_cast at hp
    have k1 : (1000000000 : ℝ) * 1344 * ∑ j, (U0 j : ℝ) * w j
        ≤ 1000000000 * (sts X₁ X₂ X₃ X₄ X₅).card * ∑ j, (U0 j : ℝ) * w j :=
      mul_le_mul_of_nonneg_right (by linarith) hU0
    linarith

end GridGen.Five.K5
