/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.MarkThreeFour
import Outerplanar.SqMultiRuns
import Outerplanar.HexEven

/-!
# The five- and six-mark classes

Research note `ai_research_notes/OUTERPLANAR_THIRTEEN_AND_GAUGE_OBSTRUCTION_2026-11-23.md`, Steps 1
and 2: *a branch with five marks dominates a mixture of `B` and `A^{4/3} H`*, *a branch with six
marks dominates a mixture of `B` and `D₆ H`*, `D₆ = A^{4/3}/K`, `A = 17/16`, `K = 59/56`.

* the constants `κq = (32/27)^{1/3}`, `κA = (17/16)^{1/3}`, `a5 = A κA = A^{4/3}`,
  `d6 = (56/59) a5`, and the inequalities between them (`d6_sq`: `D₆² ≥ K`, i.e. `A⁸ ≥ K⁹`);
* `Alt2 P Q` — a table dominating the sum of a `P` table and a `Q` table, the constants adding
  (`coneAlt2`); `P5 = Alt2 B (a5 H)`, `P6 = Alt2 B (d6 H)`;
* **`Kc6 k`** — the class of a branch with `k` marks (`Kc` below five, then `Mx P5`, `Mx P6`),
  with its closure: `Kc6_mono`, `Kc6_swap`, `Kc6_lift`, `Kc6_mul_dom`, `Kc6_nonneg_mul` (products of
  branches with at most six marks), `Kc6_hex` (every class is in `H`), `markVertex6_sound`.

The face rule is in `Outerplanar/MarkFiveSixRule.lean`. The theorem of the note is due to another
AI session of this repository's collaboration (audited); formalized by Claude.
-/

namespace Outerplanar

open Finset

/-! ### The constants -/

/-- `(32/27)^{1/3}`, the scale of the one-mark bijection surplus. -/
noncomputable def κq : ℝ := (32 / 27 : ℝ) ^ ((1 : ℝ) / 3)

/-- `(17/16)^{1/3}`, the scale of the two-mark bijection surplus. -/
noncomputable def κA : ℝ := (17 / 16 : ℝ) ^ ((1 : ℝ) / 3)

/-- `A^{4/3}`, the hexagon scale of five marks. -/
noncomputable def a5 : ℝ := 17 / 16 * κA

/-- `D₆ = A^{4/3} / K`, the hexagon scale of six marks. -/
noncomputable def d6 : ℝ := 56 / 59 * a5

theorem κq_cube : κq ^ 3 = 32 / 27 := rpow_third_cube (by norm_num)

theorem κA_cube : κA ^ 3 = 17 / 16 := rpow_third_cube (by norm_num)

theorem κq_pos : 0 < κq := Real.rpow_pos_of_pos (by norm_num) _

theorem κA_pos : 0 < κA := Real.rpow_pos_of_pos (by norm_num) _

theorem le_of_cube_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x ^ 3 ≤ y ^ 3) : x ≤ y :=
  (pow_le_pow_iff_left₀ hx hy (by norm_num : (3 : ℕ) ≠ 0)).mp h

theorem one_le_κA : 1 ≤ κA := le_of_cube_le zero_le_one κA_pos.le (by rw [κA_cube]; norm_num)

theorem κA_le_κq : κA ≤ κq :=
  le_of_cube_le κA_pos.le κq_pos.le (by rw [κA_cube, κq_cube]; norm_num)

theorem one_le_κq : 1 ≤ κq := one_le_κA.trans κA_le_κq

theorem a5_pos : 0 < a5 := mul_pos (by norm_num) κA_pos

theorem a5_ge : 17 / 16 ≤ a5 := by
  unfold a5; nlinarith [one_le_κA]

theorem one_le_a5 : 1 ≤ a5 := le_trans (by norm_num) a5_ge

theorem d6_pos : 0 < d6 := mul_pos (by norm_num) a5_pos

theorem d6_le_a5 : d6 ≤ a5 := by unfold d6; nlinarith [a5_pos]

theorem a5_cube : a5 ^ 3 = (17 / 16) ^ 4 := by
  unfold a5; rw [mul_pow, κA_cube]; norm_num

theorem d6_cube : d6 ^ 3 = (56 / 59) ^ 3 * (17 / 16) ^ 4 := by
  unfold d6; rw [mul_pow, a5_cube]

theorem one_le_d6 : 1 ≤ d6 :=
  le_of_cube_le zero_le_one d6_pos.le (by rw [d6_cube]; norm_num)

/-- **`D₆² ≥ K`** (`A⁸ ≥ K⁹`). -/
theorem d6_sq : 1 ≤ 56 / 59 * (d6 * d6) := by
  have h0 : 0 ≤ 56 / 59 * (d6 * d6) := by have := d6_pos; positivity
  refine le_of_cube_le zero_le_one h0 ?_
  have e : (56 / 59 * (d6 * d6)) ^ 3 = (56 / 59) ^ 3 * (d6 ^ 3) ^ 2 := by ring
  rw [e, d6_cube]
  norm_num

theorem d6_le_κq : d6 ≤ κq :=
  le_of_cube_le d6_pos.le κq_pos.le (by rw [d6_cube, κq_cube]; norm_num)

theorem a5_le_Aκq : a5 ≤ 17 / 16 * κq := by
  unfold a5; nlinarith [κA_le_κq]

theorem a5_le_Aκq2 : a5 ≤ 17 / 16 * (κq * κq) := by
  have := one_le_κq
  have : κq ≤ κq * κq := by nlinarith
  unfold a5; nlinarith [κA_le_κq]

/-! ### Cones -/

theorem coneB : ConeP fun S T Y v => InBall S T Y v where
  zero _ _ := InBall.zero fun _ _ => le_rfl
  add := fun hv hv' h0 h0' h h' => InBall.add hv hv' h0 h0' h h'
  smul := fun l hl hv _ h => InBall.smul hl hv h
  mono := fun h0 hle h => InBall.mono h h0 hle
  weaken := fun hv' hle _ h => InBall.weaken hv' hle h

theorem coneH {κ : ℝ} (hκ : 0 ≤ κ) : ConeP fun S T Y v => Hex S T Y (v * κ) where
  zero _ _ := by
    rw [zero_mul]; exact Dominant.hex (fun _ _ _ _ _ => le_rfl) le_rfl
  add := by
    intro S T Y Y' v v' hv hv' h0 h0' h h'
    have := Hex.add (by positivity) (by positivity) h0 h0' h h'
    rwa [show v * κ + v' * κ = (v + v') * κ by ring] at this
  smul := by
    intro S T Y v l hl hv h0 h
    have := Hex.smul hl (by positivity) h
    rwa [show l * (v * κ) = l * v * κ by ring] at this
  mono := fun h0 hle h => h.mono h0 hle
  weaken := fun hv' hle _ h => h.weaken (by positivity) (mul_le_mul_of_nonneg_right hle hκ)

/-- **Two alternatives**: the table dominates a `P` table plus a `Q` table, the constants adding. -/
def Alt2 (P Q : Finset ℕ → Finset ℕ → (ℕ → ℕ → ℝ) → ℝ → Prop) (S T : Finset ℕ)
    (Y : ℕ → ℕ → ℝ) (v : ℝ) : Prop :=
  ∃ (Y₁ Y₂ : ℕ → ℕ → ℝ) (v₁ v₂ : ℝ), 0 ≤ v₁ ∧ 0 ≤ v₂ ∧ v₁ + v₂ = v ∧ (∀ c d, 0 ≤ Y₁ c d) ∧
    (∀ c d, 0 ≤ Y₂ c d) ∧ (∀ c ∈ S, ∀ d ∈ T, c ≠ d → Y₁ c d + Y₂ c d ≤ Y c d) ∧
    P S T Y₁ v₁ ∧ Q S T Y₂ v₂

section Alt

variable {P Q : Finset ℕ → Finset ℕ → (ℕ → ℕ → ℝ) → ℝ → Prop}

theorem coneAlt2 (hP : ConeP P) (hQ : ConeP Q) : ConeP (Alt2 P Q) where
  zero S T := ⟨fun _ _ => 0, fun _ _ => 0, 0, 0, le_rfl, le_rfl, by simp, fun _ _ => le_rfl,
    fun _ _ => le_rfl, fun _ _ _ _ _ => by simp, hP.zero S T, hQ.zero S T⟩
  add := by
    intro S T Y Y' v v' _ _ _ _ h h'
    obtain ⟨Y₁, Y₂, v₁, v₂, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
    obtain ⟨Y₁', Y₂', v₁', v₂', h1', h2', h3', h4', h5', h6', h7', h8'⟩ := h'
    refine ⟨fun c d => Y₁ c d + Y₁' c d, fun c d => Y₂ c d + Y₂' c d, v₁ + v₁', v₂ + v₂',
      by positivity, by positivity, by linarith, fun c d => add_nonneg (h4 c d) (h4' c d),
      fun c d => add_nonneg (h5 c d) (h5' c d), fun c hc d hd hcd => ?_,
      hP.add h1 h1' h4 h4' h7 h7', hQ.add h2 h2' h5 h5' h8 h8'⟩
    have := h6 c hc d hd hcd
    have := h6' c hc d hd hcd
    show Y₁ c d + Y₁' c d + (Y₂ c d + Y₂' c d) ≤ Y c d + Y' c d
    linarith
  smul := by
    intro S T Y v l hl _ _ h
    obtain ⟨Y₁, Y₂, v₁, v₂, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
    refine ⟨fun c d => l * Y₁ c d, fun c d => l * Y₂ c d, l * v₁, l * v₂, by positivity,
      by positivity, by rw [← h3]; ring, fun c d => mul_nonneg hl (h4 c d),
      fun c d => mul_nonneg hl (h5 c d), fun c hc d hd hcd => ?_, hP.smul l hl h1 h4 h7,
      hQ.smul l hl h2 h5 h8⟩
    have := h6 c hc d hd hcd
    show l * Y₁ c d + l * Y₂ c d ≤ l * Y c d
    nlinarith
  mono := by
    intro S T Y Y' v _ hle h
    obtain ⟨Y₁, Y₂, v₁, v₂, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
    exact ⟨Y₁, Y₂, v₁, v₂, h1, h2, h3, h4, h5, fun c hc d hd hcd =>
      (h6 c hc d hd hcd).trans (hle c hc d hd hcd), h7, h8⟩
  weaken := by
    intro S T Y v v' hv' hle _ h
    obtain ⟨Y₁, Y₂, v₁, v₂, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
    rcases le_total v' v₁ with h9 | h9
    · exact ⟨Y₁, Y₂, v', 0, hv', le_rfl, by ring, h4, h5, h6, hP.weaken hv' h9 h4 h7,
        hQ.weaken le_rfl h2 h5 h8⟩
    · exact ⟨Y₁, Y₂, v₁, v' - v₁, h1, by linarith, by ring, h4, h5, h6, h7,
        hQ.weaken (by linarith) (by linarith) h5 h8⟩

theorem Alt2.imp {P' Q' : Finset ℕ → Finset ℕ → (ℕ → ℕ → ℝ) → ℝ → Prop}
    (hp : ∀ {S T : Finset ℕ} {Y : ℕ → ℕ → ℝ} {v : ℝ}, 0 ≤ v → (∀ c d, 0 ≤ Y c d) →
      P S T Y v → P' S T Y v)
    (hq : ∀ {S T : Finset ℕ} {Y : ℕ → ℕ → ℝ} {v : ℝ}, 0 ≤ v → (∀ c d, 0 ≤ Y c d) →
      Q S T Y v → Q' S T Y v)
    {S T : Finset ℕ} {Y : ℕ → ℕ → ℝ} {v : ℝ} (h : Alt2 P Q S T Y v) : Alt2 P' Q' S T Y v := by
  obtain ⟨Y₁, Y₂, v₁, v₂, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨Y₁, Y₂, v₁, v₂, h1, h2, h3, h4, h5, h6, hp h1 h4 h7, hq h2 h5 h8⟩

theorem Alt2.of_left (hQ : ConeP Q) {S T : Finset ℕ} {Y : ℕ → ℕ → ℝ} {v : ℝ} (hv : 0 ≤ v)
    (h0 : ∀ c d, 0 ≤ Y c d) (h : P S T Y v) : Alt2 P Q S T Y v :=
  ⟨Y, fun _ _ => 0, v, 0, hv, le_rfl, by ring, h0, fun _ _ => le_rfl,
    fun _ _ _ _ _ => by simp, h, hQ.zero S T⟩

theorem Alt2.of_right (hP : ConeP P) {S T : Finset ℕ} {Y : ℕ → ℕ → ℝ} {v : ℝ} (hv : 0 ≤ v)
    (h0 : ∀ c d, 0 ≤ Y c d) (h : Q S T Y v) : Alt2 P Q S T Y v :=
  ⟨fun _ _ => 0, Y, 0, v, le_rfl, hv, by ring, fun _ _ => le_rfl, h0,
    fun _ _ _ _ _ => by simp, hP.zero S T, h⟩

end Alt

/-! ### The five- and six-mark tables -/

/-- The tables of five marks: `B` plus `A^{4/3} H`. -/
def P5 : Finset ℕ → Finset ℕ → (ℕ → ℕ → ℝ) → ℝ → Prop :=
  Alt2 (fun S T Y v => InBall S T Y v) (fun S T Y v => Hex S T Y (v * a5))

/-- The tables of six marks: `B` plus `D₆ H`. -/
def P6 : Finset ℕ → Finset ℕ → (ℕ → ℕ → ℝ) → ℝ → Prop :=
  Alt2 (fun S T Y v => InBall S T Y v) (fun S T Y v => Hex S T Y (v * d6))

theorem cone5 : ConeP P5 := coneAlt2 coneB (coneH a5_pos.le)

theorem cone6 : ConeP P6 := coneAlt2 coneB (coneH d6_pos.le)

section Tables

variable {S T U : Finset ℕ} {Y Y' : ℕ → ℕ → ℝ} {v v' : ℝ}

theorem pB_p5 (hv : 0 ≤ v) (h0 : ∀ c d, 0 ≤ Y c d) (h : InBall S T Y v) : P5 S T Y v :=
  Alt2.of_left (coneH a5_pos.le) hv h0 h

theorem pB_p6 (hv : 0 ≤ v) (h0 : ∀ c d, 0 ≤ Y c d) (h : InBall S T Y v) : P6 S T Y v :=
  Alt2.of_left (coneH d6_pos.le) hv h0 h

theorem pH_p5 (hv : 0 ≤ v) (h0 : ∀ c d, 0 ≤ Y c d) (h : Hex S T Y (v * a5)) : P5 S T Y v :=
  Alt2.of_right coneB hv h0 h

theorem pH_p6 (hv : 0 ≤ v) (h0 : ∀ c d, 0 ≤ Y c d) (h : Hex S T Y (v * d6)) : P6 S T Y v :=
  Alt2.of_right coneB hv h0 h

theorem p4_p5 (hv : 0 ≤ v) (h0 : ∀ c d, 0 ≤ Y c d) (h : P4 S T Y v) : P5 S T Y v :=
  pB_p5 hv h0 h.1

theorem p5_p6 (h : P5 S T Y v) : P6 S T Y v :=
  Alt2.imp (fun _ _ h => h) (fun hv _ h => h.weaken (by have := d6_pos; positivity)
    (mul_le_mul_of_nonneg_left d6_le_a5 hv)) h

theorem p5_swap (h : P5 S T Y v) : P5 T S (fun d c => Y c d) v := by
  obtain ⟨Y₁, Y₂, v₁, v₂, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨fun d c => Y₁ c d, fun d c => Y₂ c d, v₁, v₂, h1, h2, h3, fun _ _ => h4 _ _,
    fun _ _ => h5 _ _, fun d hd c hc hdc => h6 c hc d hd (Ne.symm hdc), h7.swap, h8.swap'⟩

theorem p6_swap (h : P6 S T Y v) : P6 T S (fun d c => Y c d) v := by
  obtain ⟨Y₁, Y₂, v₁, v₂, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨fun d c => Y₁ c d, fun d c => Y₂ c d, v₁, v₂, h1, h2, h3, fun _ _ => h4 _ _,
    fun _ _ => h5 _ _, fun d hd c hc hdc => h6 c hc d hd (Ne.symm hdc), h7.swap, h8.swap'⟩

theorem liftV_mono_proper {T : Finset ℕ} {X X' : ℕ → ℕ → ℝ} {c : ℕ} (hc : c ∈ S)
    (hle : ∀ c ∈ S, ∀ d ∈ T, c ≠ d → X c d ≤ X' c d) : liftV T X c ≤ liftV T X' c := by
  unfold liftV
  exact Finset.sum_le_sum fun e he => by
    split_ifs with h
    · exact hle c hc e he h
    · exact le_rfl

theorem liftV_add {T : Finset ℕ} (X X' : ℕ → ℕ → ℝ) (c : ℕ) :
    liftV T (fun c d => X c d + X' c d) c = liftV T X c + liftV T X' c := by
  unfold liftV
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun e _ => by split_ifs <;> simp

theorem alt_lift (hS : S.card = 3) (hT : T.card = 3) (hU : U.card = 3) {κ : ℝ} (hκ : 0 ≤ κ)
    (hv : 0 ≤ v) (h0 : ∀ c d, 0 ≤ Y c d)
    (h : Alt2 (fun S T Y v => InBall S T Y v) (fun S T Y v => Hex S T Y (v * κ)) S T Y v) :
    Alt2 (fun S T Y v => InBall S T Y v) (fun S T Y v => Hex S T Y (v * κ)) S U
      (fun c _ => liftV T Y c) (2 * v) := by
  obtain ⟨Y₁, Y₂, v₁, v₂, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨fun c _ => liftV T Y₁ c, fun c _ => liftV T Y₂ c, 2 * v₁, 2 * v₂, by positivity,
    by positivity, by rw [← h3]; ring, fun c _ => liftV_nonneg h4 c, fun c _ => liftV_nonneg h5 c,
    fun c hc d _ _ => ?_, lift_ball hS hT hU h4 h1 h7, ?_⟩
  · rw [← liftV_add]
    exact liftV_mono_proper hc h6
  · have := lift_hex (U := U) hS hT h5 (by positivity) h8
    rwa [show 2 * (v₂ * κ) = 2 * v₂ * κ by ring] at this

theorem p5_lift (hS : S.card = 3) (hT : T.card = 3) (hU : U.card = 3) (hv : 0 ≤ v)
    (h0 : ∀ c d, 0 ≤ Y c d) (h : P5 S T Y v) : P5 S U (fun c _ => liftV T Y c) (2 * v) :=
  alt_lift hS hT hU a5_pos.le hv h0 h

theorem p6_lift (hS : S.card = 3) (hT : T.card = 3) (hU : U.card = 3) (hv : 0 ≤ v)
    (h0 : ∀ c d, 0 ≤ Y c d) (h : P6 S T Y v) : P6 S U (fun c _ => liftV T Y c) (2 * v) :=
  alt_lift hS hT hU d6_pos.le hv h0 h

theorem alt_hex {κ : ℝ} (hκ : 1 ≤ κ) (hv : 0 ≤ v) (h0 : ∀ c d, 0 ≤ Y c d)
    (h : Alt2 (fun S T Y v => InBall S T Y v) (fun S T Y v => Hex S T Y (v * κ)) S T Y v) :
    Hex S T Y v := by
  obtain ⟨Y₁, Y₂, v₁, v₂, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have hb : Hex S T Y₁ v₁ := fun _ _ hm hpq => h7.hex h1 h4 hm hpq
  have hh : Hex S T Y₂ v₂ := h8.weaken h2 (by nlinarith)
  have := Hex.add h1 h2 h4 h5 hb hh
  rw [h3] at this
  exact this.mono (fun c d => add_nonneg (h4 c d) (h5 c d)) h6

/-- Products: `P5 · P1 ⊆ P6` (`B · AB ⊆ B`, `A^{4/3} H · A H ⊆ D₆ H`). -/
theorem p5_p1_p6 (hv : 0 ≤ v) (hv' : 0 ≤ v') (h0 : ∀ c d, 0 ≤ Y c d) (h0' : ∀ c d, 0 ≤ Y' c d)
    (h : P5 S T Y v) (h' : P1 S T Y' v') : P6 S T (fun c d => Y c d * Y' c d) (v * v') := by
  obtain ⟨Y₁, Y₂, v₁, v₂, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have hb' : InBall S T Y' v' := h'.2.2.2.1.weaken hv' (by linarith)
  have hh' : Hex S T Y' v' := fun _ _ hm hpq => hb'.hex hv' h0' hm hpq
  refine ⟨fun c d => Y₁ c d * Y' c d, fun c d => Y₂ c d * Y' c d, v₁ * v', v₂ * v',
    by positivity, by positivity, by rw [← h3]; ring, fun c d => mul_nonneg (h4 c d) (h0' c d),
    fun c d => mul_nonneg (h5 c d) (h0' c d), fun c hc d hd hcd => ?_, h7.mul h1 hv' hb', ?_⟩
  · have := h6 c hc d hd hcd
    have := h0' c d
    show Y₁ c d * Y' c d + Y₂ c d * Y' c d ≤ Y c d * Y' c d
    nlinarith
  · have := h8.mul (by have := a5_pos; positivity) hv' hh'
    refine this.weaken (by have := d6_pos; positivity) ?_
    have := d6_le_a5
    have := d6_pos
    nlinarith [mul_nonneg h2 hv']

end Tables

/-! ### The classes -/

/-- **The class of a branch with `k` marks.** -/
def Kc6 : ℕ → Finset ℕ → Finset ℕ → (ℕ → ℕ → ℝ) → ℝ → Prop
  | 0 => Dominant
  | 1 => Mx P1
  | 2 => Mx P2
  | 3 => Mx P3
  | 4 => Mx P4
  | 5 => Mx P5
  | _ => Mx P6

section Kc6

variable {S T U : Finset ℕ} {W W' : ℕ → ℕ → ℝ} {N N' : ℝ}

theorem Kc6_eq {k : ℕ} (hk : k ≤ 4) : Kc6 k = Kc k := by
  interval_cases k <;> rfl

theorem Kc6_six {k : ℕ} (hk : 6 ≤ k) : Kc6 k = Mx P6 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 6 := ⟨k - 6, by omega⟩
  rfl

theorem Kc6_succ (hN : 0 ≤ N) (k : ℕ) (h : Kc6 k S T W N) : Kc6 (k + 1) S T W N := by
  rcases Nat.lt_or_ge k 4 with hk | hk
  · rw [Kc6_eq (by omega)]
    rw [Kc6_eq (by omega)] at h
    exact Kc_succ hN k h
  rcases Nat.lt_or_ge k 5 with hk' | hk'
  · obtain rfl : k = 4 := by omega
    exact Mx.imp (fun hv h0 h => p4_p5 hv h0 h) h
  rcases Nat.lt_or_ge k 6 with hk'' | hk''
  · obtain rfl : k = 5 := by omega
    exact Mx.imp (fun _ _ h => p5_p6 h) h
  · rw [Kc6_six (by omega)]
    rwa [Kc6_six hk''] at h

theorem Kc6_mono (hN : 0 ≤ N) {a b : ℕ} (hab : a ≤ b) (h : Kc6 a S T W N) : Kc6 b S T W N := by
  induction b, hab using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact Kc6_succ hN n ih

theorem Kc6_mx6 (hN : 0 ≤ N) (k : ℕ) (h : Kc6 k S T W N) : Mx P6 S T W N := by
  have := Kc6_mono (b := k + 6) hN (by omega) h
  rwa [Kc6_six (by omega)] at this

theorem Kc6_swap (k : ℕ) (h : Kc6 k S T W N) : Kc6 k T S (fun d c => W c d) N := by
  rcases Nat.lt_or_ge k 5 with hk | hk
  · rw [Kc6_eq (by omega)] at h ⊢
    exact Kc_swap k h
  rcases Nat.lt_or_ge k 6 with hk' | hk'
  · obtain rfl : k = 5 := by omega
    exact Mx.swap p5_swap h
  · rw [Kc6_six hk'] at h ⊢
    exact Mx.swap p6_swap h

theorem Kc6_lift (hS : S.card = 3) (hT : T.card = 3) (hU : U.card = 3) (hN : 0 ≤ N) (k : ℕ)
    (h : Kc6 k S T W N) : Kc6 k S U (fun c _ => liftV T W c) (2 * N) := by
  rcases Nat.lt_or_ge k 5 with hk | hk
  · rw [Kc6_eq (by omega)] at h ⊢
    exact Kc_lift hS hT hU hN k h
  rcases Nat.lt_or_ge k 6 with hk' | hk'
  · obtain rfl : k = 5 := by omega
    exact Mx.lift (fun hv h0 h => p5_lift hS hT hU hv h0 h) hT h
  · rw [Kc6_six hk'] at h ⊢
    exact Mx.lift (fun hv h0 h => p6_lift hS hT hU hv h0 h) hT h

theorem Kc6_mono_table (hle : ∀ c ∈ S, ∀ d ∈ T, c ≠ d → W c d ≤ W' c d) (k : ℕ)
    (h : Kc6 k S T W N) : Kc6 k S T W' N := by
  rcases Nat.lt_or_ge k 5 with hk | hk
  · rw [Kc6_eq (by omega)] at h ⊢
    exact Kc_mono_table hle k h
  rcases Nat.lt_or_ge k 6 with hk' | hk'
  · obtain rfl : k = 5 := by omega
    exact Mx.mono h hle
  · rw [Kc6_six hk'] at h ⊢
    exact Mx.mono h hle

theorem Kc6_mul_dom (hN : 0 ≤ N) (hN' : 0 ≤ N') (hW0 : ∀ c d, 0 ≤ W c d)
    (hd : Dominant S T W' N') (k : ℕ) (h : Kc6 k S T W N) :
    Kc6 k S T (fun c d => W' c d * W c d) (N' * N) := by
  rcases Nat.lt_or_ge k 5 with hk | hk
  · rw [Kc6_eq (by omega)] at h ⊢
    exact Kc_mul_dom hN hN' hW0 hd k h
  rcases Nat.lt_or_ge k 6 with hk' | hk'
  · obtain rfl : k = 5 := by omega
    exact Mx.mul_dom cone5 hN' hW0 hd h
  · rw [Kc6_six hk'] at h ⊢
    exact Mx.mul_dom cone6 hN' hW0 hd h

/-- **Every class has the hexagon bound** with its constant. -/
theorem Kc6_hex (hN : 0 ≤ N) (h0 : ∀ c d, 0 ≤ W c d) (k : ℕ) (h : Kc6 k S T W N) :
    Hex S T W N := by
  obtain ⟨u, v, Y, hu, hv, hNuv, hY0, hY, hW⟩ := Kc6_mx6 hN k h
  have h1 : Hex S T (fun c d => if c ≠ d then u else 0) u :=
    Dominant.hex (fun c _ d _ hcd => by simp [hcd]) hu
  have h2 := Hex.add hu hv (fun c d => by split_ifs <;> simp [hu]) hY0 h1
    (alt_hex one_le_d6 hv hY0 hY)
  refine (h2.mono (fun c d => add_nonneg (by split_ifs <;> simp [hu]) (hY0 c d))
    fun c hc d hd hcd => ?_).weaken hN hNuv
  simpa [hcd] using hW c hc d hd hcd

/-- Products of two classes, the marks adding up to at most six. -/
theorem Kc6_nonneg_mul {a b : ℕ} (hN : 0 ≤ N) (hN' : 0 ≤ N') (hW0 : ∀ c d, 0 ≤ W c d)
    (hW0' : ∀ c d, 0 ≤ W' c d) (hab : a + b ≤ 6) (h : Kc6 a S T W N) (h' : Kc6 b S T W' N') :
    Kc6 (a + b) S T (fun c d => W c d * W' c d) (N * N') := by
  rcases Nat.lt_or_ge (a + b) 5 with h4 | h5
  · rw [Kc6_eq (by omega)] at h h' ⊢
    exact Kc_nonneg_mul hN hN' hW0 hW0' (by omega) h h'
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [zero_add]
    exact Kc6_mul_dom hN' hN hW0' h b h'
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · rw [add_zero]
    have := Kc6_mul_dom hN hN' hW0 h' a h
    exact Kc6_mono_table (fun c _ d _ _ => le_of_eq (mul_comm _ _)) a
      (by rwa [mul_comm N' N] at this)
  -- both factors carry marks
  have hB : ∀ {k : ℕ}, k ≤ 4 → ∀ {X : ℕ → ℕ → ℝ} {M : ℝ}, 0 ≤ M → Kc6 k S T X M →
      Mx (fun S T Y v => InBall S T Y v) S T X M := fun hk X M hM hX => by
    rw [Kc6_eq hk] at hX
    exact Mx.imp (fun _ _ h => h.1) (Kc_mx4 hM _ hX)
  have hgoal : ∀ k, 5 ≤ k → k ≤ 6 → ∀ {X : ℕ → ℕ → ℝ} {M : ℝ},
      Mx (fun S T Y v => InBall S T Y v) S T X M → Kc6 k S T X M := fun k hk5 hk6 X M hX => by
    rcases (show k = 5 ∨ k = 6 by omega) with rfl | rfl
    · exact Mx.imp (fun hv h0 h => pB_p5 hv h0 h) hX
    · exact Mx.imp (fun hv h0 h => pB_p6 hv h0 h) hX
  rcases Nat.lt_or_ge a 5 with ha4 | ha5
  · rcases Nat.lt_or_ge b 5 with hb4 | hb5
    · refine hgoal _ h5 hab (Mx.mul coneB hN' (fun _ _ h => h) (fun _ _ h => h)
        (fun hv hv' _ _ h h' => h.mul hv hv' h') (hB (by omega) hN h) (hB (by omega) hN' h'))
    · -- `1 + 5`
      obtain ⟨rfl, rfl⟩ : a = 1 ∧ b = 5 := by omega
      have := Mx.mul cone6 hN (fun _ _ h => p5_p6 h)
        (fun hv _ h => pB_p6 hv (by assumption) (h.2.2.2.1.weaken hv (by linarith)))
        (fun hv hv' h0 h0' h h' => p5_p1_p6 hv hv' h0 h0' h h') h' h
      have e : (1 : ℕ) + 5 = 6 := rfl
      rw [e]
      exact Mx.mono (by rwa [mul_comm N' N] at this) fun c _ d _ _ => le_of_eq (mul_comm _ _)
  · -- `5 + 1`
    obtain ⟨rfl, rfl⟩ : a = 5 ∧ b = 1 := by omega
    exact Mx.mul cone6 hN' (fun _ _ h => p5_p6 h)
      (fun hv _ h => pB_p6 hv (by assumption) (h.2.2.2.1.weaken hv (by linarith)))
      (fun hv hv' h0 h0' h h' => p5_p1_p6 hv hv' h0 h0' h h') h h'

end Kc6

/-! ### The vertex rule -/

/-- **The vertex rule**: a branch of `t₁` marks hanging at a corner of a side of `t₀` marks. -/
theorem markVertex6_sound {t t₀ t₁ : ℕ} (h : t₀ + t₁ ≤ t ∧ t ≤ 6) (Lv Ly Lw : Finset ℕ)
    (hv : Lv.card = 3) (hy : Ly.card = 3) (hw : Lw.card = 3) (W X X' : ℕ → ℕ → ℝ)
    (hW : ∀ c d, 0 ≤ W c d) (hX : ∀ c d, 0 ≤ X c d) (hX' : ∀ c d, 0 ≤ X' c d) (A A₁ A₂ : ℝ)
    (hA : 0 < A) (hA₁ : 0 < A₁) (hA₂ : 0 < A₂) (h₀ : Kc6 t₀ Lv Ly W A) (h₁ : Kc6 t₁ Lv Lw X A₁)
    (h₂ : Dominant Lw Lv X' A₂) :
    Kc6 t Lv Ly (fun c d => W c d * ∑ e ∈ Lw, X c e * X' e c) (A * (2 * A₁ * A₂)) := by
  have hL := Kc6_lift (U := Ly) hv hw hy hA₁.le t₁ h₁
  have hL' := Kc6_mul_dom (W' := fun _ _ => A₂) (by positivity) hA₂.le
    (fun c _ => liftV_nonneg hX c) (fun _ _ _ _ _ => le_refl _) t₁ hL
  have hB : Kc6 t₁ Lv Ly (fun c _ => ∑ e ∈ Lw, X c e * X' e c) (A₂ * (2 * A₁)) :=
    Kc6_mono_table (fun c hc _ _ _ => branch_ge hX hX' h₂ hc) t₁ hL'
  have hprod := Kc6_nonneg_mul hA.le (by positivity) hW
    (fun c _ => Finset.sum_nonneg fun e _ => mul_nonneg (hX _ _) (hX' _ _)) (by omega) h₀ hB
  rw [show A * (2 * A₁ * A₂) = A * (A₂ * (2 * A₁)) by ring]
  exact Kc6_mono (by positivity) h.1 hprod

end Outerplanar
