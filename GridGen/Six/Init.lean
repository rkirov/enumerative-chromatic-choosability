/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Six.State
import GridGen.Six.Bridge

/-!
# Height six at `k = 6`: the initial inequality

`ai_research_notes/cx/h6k6/NOTE.md` ("Exact residual pins and Init", Codex, OpenAI), checked in
`H6_K6_REVIEW_2026-10-29.md` §3 (Init); `GridGen/Five/K5/Init.lean` with six rows. A column of
`6`-lists `X` weighs at least the uniform column `{0,…,5}⁶` for every weight of the cone
(`init66Holds`):

* if the lists coincide, by relabelling (`G_range_eq6`);
* otherwise `|sts X| ≥ 19375 = 18750 + 625` (the greedy count, `countInit`; Codex's bound is
  `18750 + 625 Σμ`), and the chain polytope at the size vector `(6, …, 6)` bounds the ratio of the
  uniform average to the actual one by `R_init = 1.009711950857…` (`init_cert_ok`), below
  `19375/18750`.
-/

namespace GridGen.Six

open Finset

/-! ### The pattern lemma against any row -/

/-- The ray checks of a certificate against a row `v` with total `NV` and ratio `R`. -/
def rowOK (C : PatCert) (v : Fin 32 → ℕ) (NV R : ℕ) : Bool :=
  (List.range 5).all (fun k =>
    decide (1000000000000 * DP * ∑ j, v j * Fv k j + R * NV * zsumL C.ev (C.zs.getD k [])
      ≤ R * NV * C.lam.getD k 0)) &&
  decide (1000000000000 * DP * (∑ j, v j * (qL j + qU j) + 7 * NV)
      + R * NV * (zsumL C.ev (C.zs.getD 5 []) + 7 * DP) ≤ R * NV * C.lam.getD 5 0)

theorem row_mid {w : Wt6} (hq : InQ6 w) (v : Fin 32 → ℕ) :
    20000000 * ∑ j, (v j : ℝ) * w j ≤ ((∑ j, v j * (qL j + qU j) : ℕ) : ℝ) + 7 * ∑ j, (v j : ℝ) := by
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  have h1' : (qL j : ℝ) ≤ qU j := by exact_mod_cast (qU_le j).1
  have : 10000000 * w j ≤ (qU j : ℝ) := by
    have := (hq j).2; rw [le_div_iff₀ (by norm_num)] at this; linarith
  have h2' : (qU j : ℝ) ≤ qL j + 7 := by exact_mod_cast (qU_le j).2
  have hv : (0 : ℝ) ≤ v j := Nat.cast_nonneg _
  generalize (v j : ℝ) = a at hv ⊢
  generalize (qL j : ℝ) = b at h1' h2' this ⊢
  generalize (qU j : ℝ) = c at h1' h2' this ⊢
  generalize w j = x at this ⊢
  nlinarith

/-- The arithmetic of a ray. -/
theorem coreRay {Λ Z S N R D E NV Fw : ℝ} (hN : 0 ≤ N) (hRN : 0 ≤ R * NV) (hD : 0 < D)
    (hl : Λ * N ≤ D * S + Z * N) (hr : E * D * Fw + R * NV * Z ≤ R * NV * Λ) :
    E * N * Fw ≤ R * NV * S := by
  have k1 := mul_le_mul_of_nonneg_right hr hN
  have k2 := mul_le_mul_of_nonneg_left hl hRN
  have keyR : E * N * Fw * D ≤ R * NV * S * D := by nlinarith
  exact le_of_mul_le_mul_right keyR hD

/-- **The pattern lemma against a row**: if a certificate's dual checks pass at all generators
and its ratio checks pass against `v`, then `10¹² · |sts A| · Σ vⱼ wⱼ ≤ R · NV · G w A` on the
cone. -/
theorem pattern_row {w : Wt6} (hw : InCone6 w) {A₁ A₂ A₃ A₄ A₅ A₆ : Finset ℕ} {nv : List ℕ}
    (hX : ∀ i < 6, nv.getD i 0 ≤ (bl A₁ A₂ A₃ A₄ A₅ A₆ i).card) (hn : ∀ i < 6, 1 ≤ frcL nv i)
    {C : PatCert} (hev : ∀ ev ∈ C.ev, peelOKB ev = true)
    (hpt : ∀ k < 6, ptOK nv C k = true) (v : Fin 32 → ℕ) (NV R : ℕ) (hNV : ∑ j, v j = NV)
    (hrow : rowOK C v NV R = true) :
    (1000000000000 : ℝ) * (sts A₁ A₂ A₃ A₄ A₅ A₆).card * ∑ j, (v j : ℝ) * w j
      ≤ R * NV * G w A₁ A₂ A₃ A₄ A₅ A₆ := by
  simp only [rowOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq]
    at hrow
  obtain ⟨hray, hmid⟩ := hrow
  have hB : ∀ ev ∈ C.ev, evB nv ev * ((sts A₁ A₂ A₃ A₄ A₅ A₆).filter
      (fun t => evHolds ev t = true)).card ≤ (sts A₁ A₂ A₃ A₄ A₅ A₆).card :=
    fun ev he => ev_count hX hn ev (hev ev he)
  rw [G_eq_sum]
  have hD : 0 < DP := by decide
  have hE : ((1000000000000 : ℕ) : ℝ) = 1000000000000 := by norm_num
  rw [← hE]
  have hNVr : ∑ j, (v j : ℝ) = NV := by exact_mod_cast hNV
  rcases hw with hq | ⟨k, hk, rfl⟩
  · have hl := lp_count6 (k := 5) hev hB (hpt 5 (by norm_num))
    have hG' := sum_gval5_le hq (sts A₁ A₂ A₃ A₄ A₅ A₆)
    have hV := row_mid hq v
    rw [hNVr] at hV
    generalize C.lam.getD 5 0 = Λ at hl hmid
    generalize zsumL C.ev (C.zs.getD 5 []) = Z at hl hmid
    generalize ∑ t ∈ sts A₁ A₂ A₃ A₄ A₅ A₆, gval 5 (orb t) = S at hl hG'
    generalize (sts A₁ A₂ A₃ A₄ A₅ A₆).card = N at hl hG' ⊢
    generalize ∑ j, v j * (qL j + qU j) = Mv at hmid hV
    generalize DP = D at hl hmid hD
    generalize (1000000000000 : ℕ) = E at hmid ⊢
    generalize ∑ t ∈ sts A₁ A₂ A₃ A₄ A₅ A₆, w (orb t) = G at hG' ⊢
    generalize ∑ j, (v j : ℝ) * w j = Vw at hV ⊢
    have hlR : (Λ : ℝ) * N ≤ D * S + Z * N := by exact_mod_cast hl
    have hmR : (E : ℝ) * D * (Mv + 7 * NV) + R * NV * (Z + 7 * D) ≤ R * NV * Λ := by
      exact_mod_cast hmid
    exact coreQ (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (by exact_mod_cast hD) (Nat.cast_nonneg _) hlR hmR hG' hV
  · have hl := lp_count6 (k := k) hev hB (hpt k (by omega))
    have hr := hray k hk
    have hF0 : (0 : ℝ) < Fv k 0 := by exact_mod_cast Fv_pos k (by omega)
    have eS : ∑ t ∈ sts A₁ A₂ A₃ A₄ A₅ A₆, rayW k (orb t)
        = ((∑ t ∈ sts A₁ A₂ A₃ A₄ A₅ A₆, gval k (orb t) : ℕ) : ℝ) / Fv k 0 := by
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
    generalize ∑ t ∈ sts A₁ A₂ A₃ A₄ A₅ A₆, gval k (orb t) = S at hl ⊢
    generalize (sts A₁ A₂ A₃ A₄ A₅ A₆).card = N at hl ⊢
    generalize ∑ j, v j * Fv k j = Fw at hr ⊢
    generalize DP = D at hl hr hD
    generalize (1000000000000 : ℕ) = E at hr ⊢
    have hlR : (Λ : ℝ) * N ≤ D * S + Z * N := by exact_mod_cast hl
    have hrR : (E : ℝ) * D * Fw + R * NV * Z ≤ R * NV * Λ := by exact_mod_cast hr
    have key := coreRay (Nat.cast_nonneg N) (mul_nonneg (Nat.cast_nonneg R) (Nat.cast_nonneg NV))
      (by exact_mod_cast hD) hlR hrR
    rw [mul_div_assoc', mul_div_assoc', div_le_div_iff_of_pos_right hF0]
    linarith

/-! ### The initial inequality -/

/-- The orbit counts of the uniform column `{0,…,5}⁶`. -/
def U0L : List ℕ := [30, 240, 240, 240, 720, 240, 720, 240, 120, 720, 720, 720, 360, 1440, 120,
  720, 240, 720, 720, 360, 1440, 720, 120, 360, 720, 1440, 360, 1440, 360, 720, 720, 720]

def U0 (o : Fin 32) : ℕ := U0L.getD o 0

theorem U0_cnt : ∀ o < 32, cntO o [63, 63, 63, 63, 63, 63] = (U0L.getD o 0 : ℤ) := by
  decide +kernel

theorem range6_mask : range 6 = setOf 63 := by decide

theorem U0_counts (o : Fin 32) :
    ((sts (range 6) (range 6) (range 6) (range 6) (range 6) (range 6)).filter
      (fun t => orb t = o)).card = U0 o := by
  have h := card_orb_setOf [63, 63, 63, 63, 63, 63] o
  rw [U0_cnt o o.2] at h
  simp only [List.getD_cons_zero, List.getD_cons_succ] at h
  rw [range6_mask]
  exact_mod_cast h

theorem U0_sum : ∑ j, U0 j = 18750 := by decide +kernel

/-- The ratio bound of the initial inequality, times `10¹²`. -/
def Rinit : ℕ := 1009711950857

/-- The certificate at `(6, …, 6)` passes against the uniform column. -/
theorem init_cert_ok : rowOK (patCerts.getD 63 default) U0 18750 Rinit = true := by
  decide +kernel

/-- **The count of a mismatched column of `6`-lists**, for first intersection `a`. -/
def countInitA (a : ℕ) : Bool :=
  (List.range 7).all fun b => (List.range 7).all fun c => (List.range 7).all fun d =>
    (List.range 7).all fun e => (a == 6 && b == 6 && c == 6 && d == 6 && e == 6) ||
      decide (19375 + N6gM 6 6 6 6 6 6 a b c d e ≤ N6gP 6 6 6 6 6 6 a b c d e)

theorem countInit0 : countInitA 0 = true := by decide +kernel
theorem countInit1 : countInitA 1 = true := by decide +kernel
theorem countInit2 : countInitA 2 = true := by decide +kernel
theorem countInit3 : countInitA 3 = true := by decide +kernel
theorem countInit4 : countInitA 4 = true := by decide +kernel
theorem countInit5 : countInitA 5 = true := by decide +kernel
theorem countInit6 : countInitA 6 = true := by decide +kernel

theorem countInit_ok {a : ℕ} (ha : a ≤ 6) : countInitA a = true := by
  interval_cases a
  exacts [countInit0, countInit1, countInit2, countInit3, countInit4, countInit5, countInit6]

/-- The uniform column weighs as much as the constant column of any `k`-set. -/
theorem G_range_eq6 (w : Wt6) {k : ℕ} {P : Finset ℕ} (hP : P.card = k) :
    G w (range k) (range k) (range k) (range k) (range k) (range k) = G w P P P P P P := by
  set e := P.orderEmbOfFin hP
  let f : ℕ → ℕ := fun i => if h : i < k then e ⟨i, h⟩ else 0
  have hinj : Set.InjOn f ↑(range k) := by
    intro i hi j hj hij
    simp only [coe_range, Set.mem_Iio] at hi hj
    simp only [f, hi, hj, dite_true] at hij
    exact congrArg Fin.val (e.injective hij)
  have himg : (range k).image f = P := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro x hx
      have hx' : x ∈ Set.range e := by rw [Finset.range_orderEmbOfFin]; exact hx
      obtain ⟨i, rfl⟩ := hx'
      refine Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr i.2, ?_⟩
      simp [f, i.2]
    · rw [Finset.card_image_of_injOn hinj, card_range, hP]
  have hinj' : Set.InjOn f ↑(range k ∪ range k ∪ range k ∪ range k ∪ range k ∪ range k) := by
    simpa only [union_self] using hinj
  rw [← G_image w hinj', himg]

/-- The final arithmetic of the initial inequality. -/
theorem init_arith {N U G : ℝ} (hU : 0 ≤ U) (hN : 19375 ≤ N)
    (hp : 1000000000000 * N * U ≤ 1009711950857 * 18750 * G) : U ≤ G := by
  nlinarith

/-- **The height-six initial inequality at `k = 6`.** -/
theorem init66Holds : Init66Holds := by
  intro w hw X₁ X₂ X₃ X₄ X₅ X₆ h₁ h₂ h₃ h₄ h₅ h₆
  show G w (range 6) (range 6) (range 6) (range 6) (range 6) (range 6) ≤ G w X₁ X₂ X₃ X₄ X₅ X₆
  have i2 : (X₁ ∩ X₂).card ≤ 6 := h₁ ▸ card_le_card inter_subset_left
  have i3 : (X₂ ∩ X₃).card ≤ 6 := h₂ ▸ card_le_card inter_subset_left
  have i4 : (X₃ ∩ X₄).card ≤ 6 := h₃ ▸ card_le_card inter_subset_left
  have i5 : (X₄ ∩ X₅).card ≤ 6 := h₄ ▸ card_le_card inter_subset_left
  have i6 : (X₅ ∩ X₆).card ≤ 6 := h₅ ▸ card_le_card inter_subset_left
  by_cases hS : (X₁ ∩ X₂).card = 6 ∧ (X₂ ∩ X₃).card = 6 ∧ (X₃ ∩ X₄).card = 6 ∧
      (X₄ ∩ X₅).card = 6 ∧ (X₅ ∩ X₆).card = 6
  · -- no mismatch: the lists are equal
    have eq : ∀ {U V : Finset ℕ}, U.card = 6 → V.card = 6 → (U ∩ V).card = 6 → U = V := by
      intro U V hU hV h
      have h1 : U ∩ V = U := Finset.eq_of_subset_of_card_le inter_subset_left (by omega)
      have h2 : U ∩ V = V := Finset.eq_of_subset_of_card_le inter_subset_right (by omega)
      rw [← h1, h2]
    obtain ⟨s2, s3, s4, s5, s6⟩ := hS
    have e12 := eq h₁ h₂ s2
    have e23 := eq h₂ h₃ s3
    have e34 := eq h₃ h₄ s4
    have e45 := eq h₄ h₅ s5
    have e56 := eq h₅ h₆ s6
    subst e12 e23 e34 e45 e56
    rw [G_range_eq6 w h₁]
  · -- a mismatch: at least `19375` columns
    have hN : 19375 ≤ (sts X₁ X₂ X₃ X₄ X₅ X₆).card := by
      have hg := N6g_le_card (A₁ := X₁) (A₂ := X₂) (A₃ := X₃) (A₄ := X₄) (A₅ := X₅) (A₆ := X₆)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      rw [h₁, h₂, h₃, h₄, h₅, h₆, ← N6gPM_eq] at hg
      have hc := countInit_ok i2
      simp only [countInitA, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.and_eq_true,
        beq_iff_eq, decide_eq_true_eq] at hc
      rcases hc (X₂ ∩ X₃).card (by omega) (X₃ ∩ X₄).card (by omega) (X₄ ∩ X₅).card (by omega)
        (X₅ ∩ X₆).card (by omega) with h | h
      · exact absurd ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩ hS
      · omega
    have hX : ∀ i < 6, [6, 6, 6, 6, 6, 6].getD i 0 ≤ (bl X₁ X₂ X₃ X₄ X₅ X₆ i).card := by
      intro i hi; interval_cases i <;> simp [bl, h₁, h₂, h₃, h₄, h₅, h₆]
    have hn : ∀ i < 6, 1 ≤ frcL [6, 6, 6, 6, 6, 6] i := by
      intro i hi; interval_cases i <;> decide
    have hok : patOK [6, 6, 6, 6, 6, 6] (patCerts.getD 63 default) = true := by
      have h := allPat6
      simp only [allPatA, List.all_eq_true] at h
      exact h 6 (by simp) 6 (by simp) 6 (by simp) 6 (by simp) 6 (by simp)
    simp only [patOK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hok
    obtain ⟨⟨⟨hev, hpt⟩, -⟩, -⟩ := hok
    have hp := pattern_row hw hX hn hev hpt U0 18750 Rinit U0_sum init_cert_ok
    have hU : G w (range 6) (range 6) (range 6) (range 6) (range 6) (range 6)
        = ∑ j, (U0 j : ℝ) * w j := by
      rw [G_eq_sum_orb]
      exact Finset.sum_congr rfl fun o _ => by rw [U0_counts]
    rw [hU]
    have hU0 : 0 ≤ ∑ j, (U0 j : ℝ) * w j :=
      Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (cone_nonneg hw j)
    have hN' : (19375 : ℝ) ≤ (sts X₁ X₂ X₃ X₄ X₅ X₆).card := by exact_mod_cast hN
    have hR : (Rinit : ℝ) = 1009711950857 := by norm_num [Rinit]
    rw [hR] at hp
    push_cast at hp
    exact init_arith hU0 hN' hp

end GridGen.Six
