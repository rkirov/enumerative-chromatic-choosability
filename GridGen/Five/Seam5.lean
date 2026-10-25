/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.LogB5

/-!
# Height five, `k = 6`: the averaged certificate

`ai_research_notes/H5_K6_ANALYTIC_2026-10-23.md` §3.1, the analogue of
`GridGen/Four/Seam6.lean`.

* **The state bound** (`state_bound5`): `GB ≥ GU · (1 + Λ)` with
  `Λ(s) = Kr (o(s)) + Σⱼ Lr Bⱼ₋₁ Bⱼ sⱼ₋₁ sⱼ`, from the count (`count_state`) and the pattern
  lemma (`pattern5`).
* **The measure.** Previous columns `s ∈ sts X` are weighted by `GU 6 w s = rowV (o(s)) w`; any
  two of these weights are within the factor `1000/959` (the box is invariant and its lowest edge
  is `959/1000`, `GU_ratio5`). A row pinned to one colour, or to the colour of a row two or more
  away, then weighs at most `qₑ = 1000/3877` of the total for an end row (four other values) and
  `qₘ = 500/1459` for a middle row (three other values) (`pin_row1` … `pin_row5`).
* **The row terms** (`sum_Lr`): `Σ GU · Lr ≥ hrow q q' μ · Σ GU`, since the state colours in the
  difference sets of a seam are pinned to `μ` colours each.
* **The orbit constants** (`sum_Kr`): `Σ GU · Kr (o(s)) ≥ K̄ · Σ GU`, by a dual certificate of the
  linear programme over the fifteen patterns with the six pair pins (Lemma 9).
* **The seam** (`seam_of_F5`): if `F5 = Σⱼ hrow + K̄ ≥ 0`, the seam inequality holds.
-/

namespace GridGen.Five

open Finset Real

/-! ### The uniform weights -/

theorem lo5_ge : ∀ i : Fin 11, (959 / 1000 : ℚ) ≤ lo5 i := by decide +kernel

theorem Vmat_pos : ∀ i j : Fin 11, 0 < Vmat i j := by decide +kernel

theorem rowsum_pos (i : Fin 11) : 0 < ∑ j, (Vmat i j : ℝ) :=
  Finset.sum_pos (fun j _ => by exact_mod_cast Vmat_pos i j) Finset.univ_nonempty

theorem rowV_bounds {w : Wt5} (hw : InBox5 w) (i : Fin 11) :
    (959 / 1000 : ℝ) * rowV 0 w ≤ rowV i w ∧ rowV i w ≤ rowV 0 w := by
  have hpos := rowV_pos hw
  obtain ⟨hl, hu⟩ := nextW_inBox hw i
  unfold nextW at hl hu
  rw [le_div_iff₀ hpos] at hl
  rw [div_le_one hpos] at hu
  have h : ((959 / 1000 : ℚ) : ℝ) ≤ (lo5 i : ℝ) := by exact_mod_cast lo5_ge i
  push_cast at h
  exact ⟨le_trans (mul_le_mul_of_nonneg_right h hpos.le) hl, hu⟩

theorem GU_pos5 {w : Wt5} (hw : InBox5 w) {s : T5} (hs : Proper s) : 0 < GU 6 w s := by
  rw [GU_six w hs]
  have := rowV_bounds hw (orb s)
  have := rowV_pos hw
  linarith

theorem GU_nonneg5 {w : Wt5} (hw : InBox5 w) (t : T5) : 0 ≤ GU 6 w t := by
  unfold GU G
  refine Finset.sum_nonneg fun x _ => ?_
  unfold gw
  have h : ((959 / 1000 : ℚ) : ℝ) ≤ (lo5 (orb x) : ℝ) := by exact_mod_cast lo5_ge (orb x)
  have := (hw (orb x)).1
  push_cast at h
  linarith

theorem GU_ratio5 {w : Wt5} (hw : InBox5 w) {t t' : T5} (ht : Proper t) (ht' : Proper t') :
    GU 6 w t ≤ 1000 / 959 * GU 6 w t' := by
  rw [GU_six w ht, GU_six w ht']
  have a := rowV_bounds hw (orb t)
  have b := rowV_bounds hw (orb t')
  linarith

/-! ### The state bound -/

/-- The gain of one state. -/
noncomputable def Lam5 (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) (s : T5) : ℝ :=
  Kr (orb s) + (Lr B₁ B₂ (r1 s) (r2 s) + Lr B₂ B₃ (r2 s) (r3 s) + Lr B₃ B₄ (r3 s) (r4 s)
    + Lr B₄ B₅ (r4 s) (r5 s))

/-- **The bound for one state from a count bound**: if `log κ + L ≤ log (|sts A| / (5 t⁴))`,
then `GB ≥ GU · (1 + Kr (o(s)) + L)` (with the pattern lemma). -/
theorem state_bound_of_count {w : Wt5} (hw : InBox5 w) {B₁ B₂ B₃ B₄ B₅ : Finset ℕ}
    (hB₁ : B₁.card = 6) (hB₂ : B₂.card = 6) (hB₃ : B₃.card = 6) (hB₄ : B₄.card = 6)
    (hB₅ : B₅.card = 6) {s : T5} (hs : Proper s) {L : ℝ}
    (hN : 0 < ((sts (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s)) (B₄.erase (r4 s))
        (B₅.erase (r5 s))).card : ℝ))
    (hc : log (123125 / 128018) + L
      ≤ log (((sts (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s)) (B₄.erase (r4 s))
        (B₅.erase (r5 s))).card : ℝ) / (194481 / 125))) :
    GU 6 w s * (1 + (Kr (orb s) + L)) ≤ GB w B₁ B₂ B₃ B₄ B₅ s := by
  have c5 : ∀ (B : Finset ℕ) (c : ℕ), B.card = 6 → 5 ≤ (B.erase c).card := fun B c hB => by
    have := Lookback.card_ge_of_erase hB c; omega
  have hp := pattern5 hw (orb s) (c5 B₁ (r1 s) hB₁) (c5 B₂ (r2 s) hB₂) (c5 B₃ (r3 s) hB₃)
    (c5 B₄ (r4 s) hB₄) (c5 B₅ (r5 s) hB₅)
  set N : ℝ := ((sts (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s)) (B₄.erase (r4 s))
    (B₅.erase (r5 s))).card : ℝ) with hNdef
  set Gv := G w (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s)) (B₄.erase (r4 s))
    (B₅.erase (r5 s)) with hGv
  set R := ∑ j, (Vmat (orb s) j : ℝ) with hRdef
  have hR := rowsum_pos (orb s)
  have hU := GU_pos5 hw hs
  rw [GU_six w hs] at hU ⊢
  set V := rowV (orb s) w with hV
  have hlow : 0 < 971038 / 1000000 * N * V / R := by positivity
  have hGlow : 971038 / 1000000 * N * V / R ≤ Gv := by
    rw [div_le_iff₀ hR]; linarith
  have hG : 0 < Gv := lt_of_lt_of_le hlow hGlow
  apply Lookback.mul_one_add_le_of_log hU hG
  have hratio : 971038 / 1000000 * N / R ≤ Gv / V := by
    rw [le_div_iff₀ hU]
    calc 971038 / 1000000 * N / R * V = 971038 / 1000000 * N * V / R := by ring
      _ ≤ Gv := hGlow
  have hl := Real.log_le_log (by positivity) hratio
  have e : log (971038 / 1000000 * N / R)
      = log (971038 / 1000000) + log (N / (194481 / 125)) + log (194481 / 125) - log R := by
    rw [Real.log_div (by positivity) hR.ne', Real.log_mul (by norm_num) hN.ne',
      Real.log_div hN.ne' (by norm_num)]
    ring
  rw [e] at hl
  unfold Kr
  rw [← hRdef]
  show _ ≤ log (Gv / V)
  linarith

/-- **The bound for one state**: `GB ≥ GU · (1 + Λ)`. -/
theorem state_bound5 {w : Wt5} (hw : InBox5 w) {B₁ B₂ B₃ B₄ B₅ : Finset ℕ}
    (hB₁ : B₁.card = 6) (hB₂ : B₂.card = 6) (hB₃ : B₃.card = 6) (hB₄ : B₄.card = 6)
    (hB₅ : B₅.card = 6) {s : T5} (hs : Proper s) :
    GU 6 w s * (1 + Lam5 B₁ B₂ B₃ B₄ B₅ s) ≤ GB w B₁ B₂ B₃ B₄ B₅ s := by
  obtain ⟨hN, hc⟩ := count_state hB₁ hB₂ hB₃ hB₄ hB₅ hs
  exact state_bound_of_count hw hB₁ hB₂ hB₃ hB₄ hB₅ hs hN hc

/-! ### Pins -/

/-- A sum against an indicator is a filtered sum. -/
theorem sum_mul_ite5 {Ω : Finset T5} (w : T5 → ℝ) (p : T5 → Prop) [DecidablePred p] :
    ∑ t ∈ Ω, w t * (if p t then 1 else 0) = ∑ t ∈ Ω.filter p, w t := by
  rw [Finset.sum_filter]; refine Finset.sum_congr rfl (fun t _ => ?_); split_ifs <;> simp

/-- **A one-colour pin for a set of colours**: `Σ u·[g ∈ D] ≤ min (q|D|, 1) · Σ u`. -/
theorem pin_min5 {Ω : Finset T5} (u : T5 → ℝ) (hu0 : ∀ t, 0 ≤ u t) (g : T5 → ℕ) {q : ℝ}
    (hc : ∀ c, ∑ t ∈ Ω.filter (fun t => g t = c), u t ≤ q * ∑ t ∈ Ω, u t) (D : Finset ℕ) :
    ∑ t ∈ Ω, u t * (if g t ∈ D then 1 else 0) ≤ min (q * D.card) 1 * ∑ t ∈ Ω, u t := by
  have hW : 0 ≤ ∑ t ∈ Ω, u t := Finset.sum_nonneg (fun t _ => hu0 t)
  have h1 : ∑ t ∈ Ω, u t * (if g t ∈ D then 1 else 0) ≤ q * D.card * ∑ t ∈ Ω, u t := by
    rw [sum_mul_ite5]
    have e : ∑ t ∈ Ω.filter (fun t => g t ∈ D), u t
        = ∑ c ∈ D, ∑ t ∈ Ω.filter (fun t => g t = c), u t := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := g) (t := D)
        (fun x hx => (Finset.mem_filter.mp hx).2)]
      refine Finset.sum_congr rfl (fun c hc => ?_)
      rw [Finset.filter_filter]
      congr 1
      ext t; simp only [Finset.mem_filter]
      constructor
      · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨h1, h3 ▸ hc, h3⟩
    rw [e]
    calc ∑ c ∈ D, ∑ t ∈ Ω.filter (fun t => g t = c), u t
        ≤ ∑ c ∈ D, q * ∑ t ∈ Ω, u t := Finset.sum_le_sum (fun c _ => hc c)
      _ = q * D.card * ∑ t ∈ Ω, u t := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have h2 : ∑ t ∈ Ω, u t * (if g t ∈ D then 1 else 0) ≤ ∑ t ∈ Ω, u t :=
    Finset.sum_le_sum (fun t _ => by split_ifs <;> simp [hu0 t])
  rcases le_total (q * D.card) 1 with h | h
  · rw [min_eq_left h]; exact h1
  · rw [min_eq_right h, one_mul]; exact h2

section pins

variable {w : Wt5} (hw : InBox5 w) {X₁ X₂ X₃ X₄ X₅ : Finset ℕ}

include hw in
theorem ratio_on {Ω : Finset T5} (hΩ : ∀ t ∈ Ω, Proper t) :
    ∀ t ∈ Ω.filter (fun _ => True), ∀ t' ∈ Ω.filter (fun _ => True),
      GU 6 w t ≤ 1000 / 959 * GU 6 w t' := fun t ht t' ht' =>
  GU_ratio5 hw (hΩ t (Finset.mem_filter.mp ht).1) (hΩ t' (Finset.mem_filter.mp ht').1)

theorem filter_true5 (Ω : Finset T5) : Ω.filter (fun _ => True) = Ω :=
  Finset.filter_true_of_mem (fun _ _ => trivial)

theorem qe_of (S P : ℝ) (h : (1000 / 959 + (((4 : ℕ) : ℝ) - 1)) * P ≤ 1000 / 959 * S) :
    P ≤ qe5 * S := by
  unfold qe5; norm_num at h ⊢; linarith

theorem qm_of (S P : ℝ) (h : (1000 / 959 + (((3 : ℕ) : ℝ) - 1)) * P ≤ 1000 / 959 * S) :
    P ≤ qm5 * S := by
  unfold qm5; norm_num at h ⊢; linarith

include hw in
/-- **Pin on row 1** (an end row). -/
theorem pin_row1 (h₁ : 5 ≤ X₁.card) (P : T5 → Prop) [DecidablePred P] (φ : T5 → ℕ)
    (hφ : ∀ t x, φ (set1 t x) = φ t) (hP : ∀ t, P t → r1 t = φ t) :
    ∑ t ∈ (sts X₁ X₂ X₃ X₄ X₅).filter P, GU 6 w t ≤ qe5 * ∑ t ∈ sts X₁ X₂ X₃ X₄ X₅, GU 6 w t := by
  have h := fibre_row1 (A₂ := X₂) (A₃ := X₃) (A₄ := X₄) (A₅ := X₅) (GU 6 w)
    (fun t => (GU_nonneg5 hw t)) (fun _ => True) (fun _ _ => Iff.rfl) P φ hφ hP (m := 4)
    (by norm_num) (by omega) (by norm_num) (ratio_on hw (fun t ht => proper_of_mem_sts ht))
  rw [filter_true5] at h
  exact qe_of _ _ h

include hw in
/-- **Pin on row 2** (a middle row). -/
theorem pin_row2 (h₂ : 5 ≤ X₂.card) (P : T5 → Prop) [DecidablePred P] (φ : T5 → ℕ)
    (hφ : ∀ t x, φ (set2 t x) = φ t) (hP : ∀ t, P t → r2 t = φ t) :
    ∑ t ∈ (sts X₁ X₂ X₃ X₄ X₅).filter P, GU 6 w t ≤ qm5 * ∑ t ∈ sts X₁ X₂ X₃ X₄ X₅, GU 6 w t := by
  have h := fibre_row2 (A₁ := X₁) (A₃ := X₃) (A₄ := X₄) (A₅ := X₅) (GU 6 w)
    (fun t => (GU_nonneg5 hw t)) (fun _ => True) (fun _ _ => Iff.rfl) P φ hφ hP (m := 3)
    (by norm_num) (by omega) (by norm_num) (ratio_on hw (fun t ht => proper_of_mem_sts ht))
  rw [filter_true5] at h
  exact qm_of _ _ h

include hw in
/-- **Pin on row 3** (a middle row). -/
theorem pin_row3 (h₃ : 5 ≤ X₃.card) (P : T5 → Prop) [DecidablePred P] (φ : T5 → ℕ)
    (hφ : ∀ t x, φ (set3 t x) = φ t) (hP : ∀ t, P t → r3 t = φ t) :
    ∑ t ∈ (sts X₁ X₂ X₃ X₄ X₅).filter P, GU 6 w t ≤ qm5 * ∑ t ∈ sts X₁ X₂ X₃ X₄ X₅, GU 6 w t := by
  have h := fibre_row3 (A₁ := X₁) (A₂ := X₂) (A₄ := X₄) (A₅ := X₅) (GU 6 w)
    (fun t => (GU_nonneg5 hw t)) (fun _ => True) (fun _ _ => Iff.rfl) P φ hφ hP (m := 3)
    (by norm_num) (by omega) (by norm_num) (ratio_on hw (fun t ht => proper_of_mem_sts ht))
  rw [filter_true5] at h
  exact qm_of _ _ h

include hw in
/-- **Pin on row 4** (a middle row). -/
theorem pin_row4 (h₄ : 5 ≤ X₄.card) (P : T5 → Prop) [DecidablePred P] (φ : T5 → ℕ)
    (hφ : ∀ t x, φ (set4 t x) = φ t) (hP : ∀ t, P t → r4 t = φ t) :
    ∑ t ∈ (sts X₁ X₂ X₃ X₄ X₅).filter P, GU 6 w t ≤ qm5 * ∑ t ∈ sts X₁ X₂ X₃ X₄ X₅, GU 6 w t := by
  have h := fibre_row4 (A₁ := X₁) (A₂ := X₂) (A₃ := X₃) (A₅ := X₅) (GU 6 w)
    (fun t => (GU_nonneg5 hw t)) (fun _ => True) (fun _ _ => Iff.rfl) P φ hφ hP (m := 3)
    (by norm_num) (by omega) (by norm_num) (ratio_on hw (fun t ht => proper_of_mem_sts ht))
  rw [filter_true5] at h
  exact qm_of _ _ h

include hw in
/-- **Pin on row 5** (an end row). -/
theorem pin_row5 (h₅ : 5 ≤ X₅.card) (P : T5 → Prop) [DecidablePred P] (φ : T5 → ℕ)
    (hφ : ∀ t x, φ (set5 t x) = φ t) (hP : ∀ t, P t → r5 t = φ t) :
    ∑ t ∈ (sts X₁ X₂ X₃ X₄ X₅).filter P, GU 6 w t ≤ qe5 * ∑ t ∈ sts X₁ X₂ X₃ X₄ X₅, GU 6 w t := by
  have h := fibre_row5 (A₁ := X₁) (A₂ := X₂) (A₃ := X₃) (A₄ := X₄) (GU 6 w)
    (fun t => (GU_nonneg5 hw t)) (fun _ => True) (fun _ _ => Iff.rfl) P φ hφ hP (m := 4)
    (by norm_num) (by omega) (by norm_num) (ratio_on hw (fun t ht => proper_of_mem_sts ht))
  rw [filter_true5] at h
  exact qe_of _ _ h

end pins

/-! ### The row terms -/

/-- **The averaged row term.** -/
theorem sum_Lr {Ω : Finset T5} (u : T5 → ℝ) (hu0 : ∀ t, 0 ≤ u t) (ga gb : T5 → ℕ)
    {B C : Finset ℕ} (hB : B.card = 6) (hC : C.card = 6) {qa qb : ℝ}
    (hqa : ∀ c, ∑ t ∈ Ω.filter (fun t => ga t = c), u t ≤ qa * ∑ t ∈ Ω, u t)
    (hqb : ∀ c, ∑ t ∈ Ω.filter (fun t => gb t = c), u t ≤ qb * ∑ t ∈ Ω, u t) :
    hrow qa qb (Lookback.mu 6 B C) * ∑ t ∈ Ω, u t ≤ ∑ t ∈ Ω, u t * Lr B C (ga t) (gb t) := by
  have b1 := pin_min5 u hu0 ga hqa (B \ C)
  have b2 := pin_min5 u hu0 gb hqb (C \ B)
  rw [Lookback.card_sdiff_mu hB] at b1
  rw [Lookback.card_sdiff_mu hC, Lookback.mu_comm 6 C B] at b2
  have hz : 0 ≤ Lookback.zslope 5 (Lookback.mu 6 B C) :=
    Lookback.zslope_nonneg (by norm_num) (Lookback.mu_nonneg hB)
  have e1 : ∀ t, u t * Lr B C (ga t) (gb t) = log (1 + Lookback.mu 6 B C / 21) * u t
      - Lookback.zslope 5 (Lookback.mu 6 B C) * (u t * (if ga t ∈ B \ C then 1 else 0)
        + u t * (if gb t ∈ C \ B then 1 else 0)) := fun t => by
    unfold Lr; rw [Lookback.zz_eq]; ring
  have e : ∑ t ∈ Ω, u t * Lr B C (ga t) (gb t)
      = log (1 + Lookback.mu 6 B C / 21) * ∑ t ∈ Ω, u t
        - Lookback.zslope 5 (Lookback.mu 6 B C) * (∑ t ∈ Ω, u t * (if ga t ∈ B \ C then 1 else 0)
          + ∑ t ∈ Ω, u t * (if gb t ∈ C \ B then 1 else 0)) := by
    rw [Finset.sum_congr rfl (fun t _ => e1 t), Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, Finset.sum_add_distrib]
  rw [e]
  unfold hrow
  have := mul_le_mul_of_nonneg_left (add_le_add b1 b2) hz
  nlinarith

/-! ### The orbit constants -/

/-- The dual level, times `10⁹`. -/
def K0 : ℤ := -62663909

/-- **The pointwise dual check** for the orbit constants: the pair events `(1,3)`, `(2,4)`,
`(3,5)`, `(1,5)` (event indices `4, 10, 13, 11`) with multipliers `y/10⁹`. -/
def kOK : Bool :=
  canons.all fun c => decide (K0 ≤ KLL.getD (orb c) 0
    + ((if evb 4 c then 10922463 else 0) + (if evb 10 c then 10282872 else 0)
      + (if evb 13 c then 10922463 else 0) + (if evb 11 c then 639591 else 0)))

theorem kOK_true : kOK = true := by decide +kernel

/-- The averaged orbit constant `K̄ = (K0 - Σₑ yₑ qₑ)/10⁹`. -/
noncomputable def Kbar : ℝ :=
  ((K0 : ℝ) - (10922463 * qe5 + 10282872 * qm5 + 10922463 * qe5 + 639591 * qe5)) / 10 ^ 9

/-- **The averaged orbit constant** (Lemma 9). -/
theorem sum_Kr {w : Wt5} (hw : InBox5 w) {X₁ X₂ X₃ X₄ X₅ : Finset ℕ} (h₁ : 5 ≤ X₁.card)
    (h₂ : 5 ≤ X₂.card) (_h₃ : 5 ≤ X₃.card) (_h₄ : 5 ≤ X₄.card) (h₅ : 5 ≤ X₅.card) :
    Kbar * ∑ t ∈ sts X₁ X₂ X₃ X₄ X₅, GU 6 w t
      ≤ ∑ t ∈ sts X₁ X₂ X₃ X₄ X₅, GU 6 w t * Kr (orb t) := by
  set Ω := sts X₁ X₂ X₃ X₄ X₅ with hΩ
  set W := ∑ t ∈ Ω, GU 6 w t with hW
  have hu0 : ∀ t, 0 ≤ GU 6 w t := GU_nonneg5 hw
  -- the pointwise inequality
  have hpt : ∀ t ∈ Ω, (K0 : ℝ) / 10 ^ 9
      - (10922463 * (if evb 4 t then 1 else 0) + 10282872 * (if evb 10 t then 1 else 0)
        + 10922463 * (if evb 13 t then 1 else 0) + 639591 * (if evb 11 t then 1 else 0)) / 10 ^ 9
      ≤ Kr (orb t) := by
    intro t ht
    have hs := proper_of_mem_sts ht
    have hc := List.all_eq_true.mp kOK_true (canon t) (canon_mem hs)
    rw [decide_eq_true_eq] at hc
    rw [← orb_congr (samePat_canon hs), ← evb_congr (samePat_canon hs),
      ← evb_congr (samePat_canon hs), ← evb_congr (samePat_canon hs),
      ← evb_congr (samePat_canon hs)] at hc
    have hK := KL_le (orb t)
    have hc' : ((K0 : ℤ) : ℝ) ≤ ((KLL.getD (orb t) 0 : ℤ) : ℝ)
        + (((if evb 4 t = true then (10922463 : ℤ) else 0)
          + (if evb 10 t = true then 10282872 else 0) + (if evb 13 t = true then 10922463 else 0)
          + (if evb 11 t = true then 639591 else 0) : ℤ) : ℝ) := by
      exact_mod_cast hc
    have i1 : ((if evb 4 t = true then (10922463 : ℤ) else 0 : ℤ) : ℝ)
        = 10922463 * (if evb 4 t then 1 else 0) := by split_ifs <;> simp
    have i2 : ((if evb 10 t = true then (10282872 : ℤ) else 0 : ℤ) : ℝ)
        = 10282872 * (if evb 10 t then 1 else 0) := by split_ifs <;> simp
    have i3 : ((if evb 13 t = true then (10922463 : ℤ) else 0 : ℤ) : ℝ)
        = 10922463 * (if evb 13 t then 1 else 0) := by split_ifs <;> simp
    have i4 : ((if evb 11 t = true then (639591 : ℤ) else 0 : ℤ) : ℝ)
        = 639591 * (if evb 11 t then 1 else 0) := by split_ifs <;> simp
    simp only [Int.cast_add] at hc'
    rw [i1, i2, i3, i4] at hc'
    have : (K0 : ℝ) / 10 ^ 9
        - (10922463 * (if evb 4 t then 1 else 0) + 10282872 * (if evb 10 t then 1 else 0)
          + 10922463 * (if evb 13 t then 1 else 0) + 639591 * (if evb 11 t then 1 else 0))
          / 10 ^ 9 ≤ ((KLL.getD (orb t) 0 : ℤ) : ℝ) / 10 ^ 9 := by
      rw [← sub_nonneg]; field_simp; linarith
    linarith
  -- the pair pins
  have p13 : ∑ t ∈ Ω, GU 6 w t * (if evb 4 t then 1 else 0) ≤ qe5 * W := by
    rw [sum_mul_ite5]
    exact pin_row1 hw h₁ _ r3 (fun _ _ => rfl) (fun t h => (evb_4 t).mp h)
  have p24 : ∑ t ∈ Ω, GU 6 w t * (if evb 10 t then 1 else 0) ≤ qm5 * W := by
    rw [sum_mul_ite5]
    exact pin_row2 hw h₂ _ r4 (fun _ _ => rfl) (fun t h => (evb_10 t).mp h)
  have p35 : ∑ t ∈ Ω, GU 6 w t * (if evb 13 t then 1 else 0) ≤ qe5 * W := by
    rw [sum_mul_ite5]
    exact pin_row5 hw h₅ _ r3 (fun _ _ => rfl) (fun t h => (evb_13 t).mp h)
  have p15 : ∑ t ∈ Ω, GU 6 w t * (if evb 11 t then 1 else 0) ≤ qe5 * W := by
    rw [sum_mul_ite5]
    exact pin_row1 hw h₁ _ r5 (fun _ _ => rfl) (fun t h => (evb_11 t).mp h)
  have hsum : ∑ t ∈ Ω, GU 6 w t * ((K0 : ℝ) / 10 ^ 9
      - (10922463 * (if evb 4 t then 1 else 0) + 10282872 * (if evb 10 t then 1 else 0)
        + 10922463 * (if evb 13 t then 1 else 0) + 639591 * (if evb 11 t then 1 else 0)) / 10 ^ 9)
      ≤ ∑ t ∈ Ω, GU 6 w t * Kr (orb t) :=
    Finset.sum_le_sum fun t ht => mul_le_mul_of_nonneg_left (hpt t ht) (hu0 t)
  have e : ∑ t ∈ Ω, GU 6 w t * ((K0 : ℝ) / 10 ^ 9
      - (10922463 * (if evb 4 t then 1 else 0) + 10282872 * (if evb 10 t then 1 else 0)
        + 10922463 * (if evb 13 t then 1 else 0) + 639591 * (if evb 11 t then 1 else 0)) / 10 ^ 9)
      = ((K0 : ℝ) * W - (10922463 * ∑ t ∈ Ω, GU 6 w t * (if evb 4 t then 1 else 0)
        + 10282872 * ∑ t ∈ Ω, GU 6 w t * (if evb 10 t then 1 else 0)
        + 10922463 * ∑ t ∈ Ω, GU 6 w t * (if evb 13 t then 1 else 0)
        + 639591 * ∑ t ∈ Ω, GU 6 w t * (if evb 11 t then 1 else 0))) / 10 ^ 9 := by
    rw [hW]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  rw [e] at hsum
  unfold Kbar
  have e2 : ((K0 : ℝ) - (10922463 * qe5 + 10282872 * qm5 + 10922463 * qe5 + 639591 * qe5))
      / 10 ^ 9 * W = ((K0 : ℝ) * W - (10922463 * (qe5 * W) + 10282872 * (qm5 * W)
        + 10922463 * (qe5 * W) + 639591 * (qe5 * W))) / 10 ^ 9 := by ring
  rw [e2]
  refine le_trans ?_ hsum
  apply div_le_div_of_nonneg_right _ (by norm_num)
  linarith

/-! ### The seam -/

/-- **The certificate value** of a mismatch quad. -/
noncomputable def F5 (m2 m3 m4 m5 : ℝ) : ℝ :=
  hrow qe5 qm5 m2 + hrow qm5 qm5 m3 + hrow qm5 qm5 m4 + hrow qm5 qe5 m5 + Kbar

/-- **The seam inequality from the averaged certificate.** -/
theorem seam_of_F5 {w : Wt5} (hw : InBox5 w) {X₁ X₂ X₃ X₄ X₅ B₁ B₂ B₃ B₄ B₅ : Finset ℕ}
    (hX₁ : 5 ≤ X₁.card) (hX₂ : 5 ≤ X₂.card) (hX₃ : 5 ≤ X₃.card) (hX₄ : 5 ≤ X₄.card)
    (hX₅ : 5 ≤ X₅.card) (hB₁ : B₁.card = 6) (hB₂ : B₂.card = 6) (hB₃ : B₃.card = 6)
    (hB₄ : B₄.card = 6) (hB₅ : B₅.card = 6)
    (hF : 0 ≤ F5 (Lookback.mu 6 B₁ B₂) (Lookback.mu 6 B₂ B₃) (Lookback.mu 6 B₃ B₄)
      (Lookback.mu 6 B₄ B₅)) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 6 w s ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GB w B₁ B₂ B₃ B₄ B₅ s := by
  set Ω := sts X₁ X₂ X₃ X₄ X₅ with hΩ
  set W := ∑ t ∈ Ω, GU 6 w t with hW
  have hu0 : ∀ t, 0 ≤ GU 6 w t := GU_nonneg5 hw
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun t _ => hu0 t
  have hsum : ∑ s ∈ Ω, GU 6 w s * (1 + Lam5 B₁ B₂ B₃ B₄ B₅ s) ≤ ∑ s ∈ Ω, GB w B₁ B₂ B₃ B₄ B₅ s :=
    Finset.sum_le_sum fun s hs =>
      state_bound5 hw hB₁ hB₂ hB₃ hB₄ hB₅ (proper_of_mem_sts hs)
  -- the single-colour pins
  have f1 : ∀ c, ∑ t ∈ Ω.filter (fun t => r1 t = c), GU 6 w t ≤ qe5 * W := fun c =>
    pin_row1 hw hX₁ _ (fun _ => c) (fun _ _ => rfl) (fun _ h => h)
  have f2 : ∀ c, ∑ t ∈ Ω.filter (fun t => r2 t = c), GU 6 w t ≤ qm5 * W := fun c =>
    pin_row2 hw hX₂ _ (fun _ => c) (fun _ _ => rfl) (fun _ h => h)
  have f3 : ∀ c, ∑ t ∈ Ω.filter (fun t => r3 t = c), GU 6 w t ≤ qm5 * W := fun c =>
    pin_row3 hw hX₃ _ (fun _ => c) (fun _ _ => rfl) (fun _ h => h)
  have f4 : ∀ c, ∑ t ∈ Ω.filter (fun t => r4 t = c), GU 6 w t ≤ qm5 * W := fun c =>
    pin_row4 hw hX₄ _ (fun _ => c) (fun _ _ => rfl) (fun _ h => h)
  have f5 : ∀ c, ∑ t ∈ Ω.filter (fun t => r5 t = c), GU 6 w t ≤ qe5 * W := fun c =>
    pin_row5 hw hX₅ _ (fun _ => c) (fun _ _ => rfl) (fun _ h => h)
  have l2 := sum_Lr (GU 6 w) hu0 r1 r2 hB₁ hB₂ f1 f2
  have l3 := sum_Lr (GU 6 w) hu0 r2 r3 hB₂ hB₃ f2 f3
  have l4 := sum_Lr (GU 6 w) hu0 r3 r4 hB₃ hB₄ f3 f4
  have l5 := sum_Lr (GU 6 w) hu0 r4 r5 hB₄ hB₅ f4 f5
  have lk := sum_Kr hw hX₁ hX₂ hX₃ hX₄ hX₅
  have e : ∑ s ∈ Ω, GU 6 w s * (1 + Lam5 B₁ B₂ B₃ B₄ B₅ s)
      = W + (∑ t ∈ Ω, GU 6 w t * Kr (orb t) + ∑ t ∈ Ω, GU 6 w t * Lr B₁ B₂ (r1 t) (r2 t)
        + ∑ t ∈ Ω, GU 6 w t * Lr B₂ B₃ (r2 t) (r3 t) + ∑ t ∈ Ω, GU 6 w t * Lr B₃ B₄ (r3 t) (r4 t)
        + ∑ t ∈ Ω, GU 6 w t * Lr B₄ B₅ (r4 t) (r5 t)) := by
    rw [hW]
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    unfold Lam5; ring
  have hFW := mul_nonneg hF hW0
  unfold F5 at hFW
  linarith

/-- The mismatch quads certified by a dual certificate over the state bits
(`GridGen/Five/BitLP5.lean`): twenty reflection classes with mismatch sum `3` or `4`. -/
def bitQuads5 : List (ℕ × ℕ × ℕ × ℕ) :=
  [(0, 0, 0, 3), (0, 0, 1, 2), (0, 0, 1, 3), (0, 0, 2, 2), (0, 0, 3, 1), (0, 1, 0, 2),
   (0, 1, 0, 3), (0, 1, 1, 2), (0, 1, 2, 1), (0, 1, 3, 0), (0, 2, 0, 2), (0, 2, 1, 1),
   (0, 2, 2, 0), (0, 3, 0, 1), (0, 3, 1, 0), (1, 0, 0, 2), (1, 0, 1, 1), (1, 0, 1, 2),
   (1, 0, 2, 1), (1, 0, 3, 0), (1, 1, 0, 1), (1, 1, 0, 2), (1, 1, 1, 1), (1, 1, 2, 0),
   (1, 2, 0, 1), (1, 2, 1, 0), (1, 3, 0, 0), (2, 0, 0, 1), (2, 0, 1, 0), (2, 0, 1, 1),
   (2, 0, 2, 0), (2, 1, 0, 0), (2, 1, 0, 1), (2, 1, 1, 0), (2, 2, 0, 0), (3, 0, 0, 0),
   (3, 0, 1, 0), (3, 1, 0, 0)]

end GridGen.Five
