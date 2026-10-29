/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.Bridge

/-!
# Height five at `k = 5`: the uniform transfer and its invariant cone

The cone route of Codex (OpenAI), `ai_research_notes/cx/h5k5/NOTE.md` §1, checked independently
in `ai_research_notes/H5_K5_REVIEW_2026-10-28.md` (a).

**The uniform transfer at `k = 5`.** For each of the fifteen canonical patterns `c`, the uniform
successors of `c` (the proper colourings from `{0, …, 4} ∖ {cᵢ}`) are counted by orbit
(`cntU5_canons`); the rows depend only on the orbit and form the reduced transfer matrix `Vmat5`.
A proper column in orbit `i` has weighted uniform successor count `rowV5 i w` (`GU_five`).

**The cone.** Its generators are five transient rays `F_d = T^d 1` (`d ≤ 4`, integer vectors
`Fv d`, normalised to `rayW d`) and a narrow box `Q` around the Perron vector (`InQ`, edges
`qL/10⁶ ≤ w ≤ qU/10⁶`, with `w₀ = 1`). The weights used are the uniform futures `wseq5 i`: for
`i ≤ 4` they are the normalised rays (`wseq5_ray`), `wseq5 5 = rayW 5` lies in `Q`, and the
transfer maps `Q` into itself (`nextW5_inQ`, a separable kernel check of 22 linear forms), so every
`wseq5 i` lies in the union `InCone5` of `Q` and the five rays (`wseq5_inCone`). As the review
notes, the convex hull is never needed.

**Linear forms on the cone** (`lin_cone`): a form with integer coefficients is nonnegative on
`InCone5` when its five ray values and its separable minimum over `Q` are nonnegative (`coneOK`).
This gives the weight facts used later: `w₀ = 1`, `w ≥ 0`, and the uniform ratio
`rowV5 i w ≥ (911/1000) · rowV5 j w` (`rowV5_ratio`).
-/

namespace GridGen.Five.K5

open Finset GridGen.Five

/-! ### The uniform transfer at `k = 5` -/

/-- The reduced uniform transfer at `k = 5`: `Vmat5 i j` is the number of uniform successors in
orbit `j` of a column in orbit `i` (orbit numbering of `GridGen/Five/Defs.lean`). -/
def Vmat5 : Fin 11 → Fin 11 → ℕ :=
  ![![13, 60, 30, 42, 96, 12, 60, 30, 42, 48, 36],
    ![10, 55, 24, 40, 88, 17, 74, 23, 50, 38, 40],
    ![10, 48, 32, 46, 100, 14, 64, 24, 36, 50, 36],
    ![7, 40, 23, 49, 86, 23, 88, 17, 38, 36, 40],
    ![8, 44, 25, 43, 92, 19, 79, 19, 40, 39, 42],
    ![4, 34, 14, 46, 76, 32, 100, 16, 36, 36, 40],
    ![5, 37, 16, 44, 79, 25, 93, 18, 39, 39, 42],
    ![10, 46, 24, 34, 76, 16, 72, 32, 50, 50, 40],
    ![7, 50, 18, 38, 80, 18, 78, 25, 53, 40, 42],
    ![8, 38, 25, 36, 78, 18, 78, 25, 40, 53, 42],
    ![6, 40, 18, 40, 84, 20, 84, 20, 42, 42, 44]]

/-- The number of uniform successors of `c` at `k = 5` whose pattern lies in orbit `o`. -/
def cntU5 (c : T5) (o : Fin 11) : ℕ :=
  ((sts ((range 5).erase (r1 c)) ((range 5).erase (r2 c)) ((range 5).erase (r3 c))
    ((range 5).erase (r4 c)) ((range 5).erase (r5 c))).filter (fun t => orb t = o)).card

/-- **The uniform orbit counts at `k = 5`**, for all fifteen canonical patterns. -/
theorem cntU5_canons : ∀ c ∈ canons, cntU5 c = Vmat5 (orb c) := by
  decide +kernel

/-- The reduced uniform transfer, row `i`, applied to the weights. -/
noncomputable def rowV5 (i : Fin 11) (w : Wt5) : ℝ := ∑ j, (Vmat5 i j : ℝ) * w j

/-- **The uniform successors at `k = 5`.** -/
theorem GU_five (w : Wt5) {s : T5} (hs : Proper s) : GU 5 w s = rowV5 (orb s) w := by
  have h := cntU5_canons _ (canon_mem hs)
  unfold GU
  rw [G_eq_sum_orb, rowV5, orb_congr (samePat_canon hs), ← h]
  rfl

/-- The next weights of the uniform transfer, normalised by the `01010` row. -/
noncomputable def nextW5 (w : Wt5) : Wt5 := fun i => rowV5 i w / rowV5 0 w

/-! ### The cone -/

/-- The rays `F_d = T^d 1`, `d ≤ 6`. -/
def FL : List (List ℕ) :=
  [[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [469, 459, 460, 447, 450, 434, 437, 450, 449, 441, 440],
   [210205, 205329, 205902, 199452, 201027, 193112, 194687, 201150, 200564, 196847, 196262],
   [93875881, 91680307, 91943420, 89033797, 89748434, 86181438, 86896075, 89813338, 89542585,
    87880877, 87610712],
   [41910174805, 40929163673, 41046972634, 39746676186, 40066233431, 38472377524, 38791934769,
    40095773898, 39974422256, 39232571727, 39111492014],
   [18709870804573, 18271883592103, 18324492360472, 17743944756767, 17886627043502,
    17175024130274, 17317706417009, 17899842839502, 17845645252345, 17514464395401,
    17460388703744]]

/-- Entry `j` of the ray `F_d`. -/
def Fv (d : ℕ) (j : Fin 11) : ℕ := (FL.getD d []).getD j 0

/-- The lower edges of `Q`, times `10⁶`. -/
def qL : Fin 11 → ℕ :=
  ![1000000, 976588, 979400, 948370, 955997, 917963, 925589, 956703, 953806, 936105, 933215]

/-- The upper edges of `Q`, times `10⁶`. -/
def qU : Fin 11 → ℕ :=
  ![1000000, 976593, 979405, 948375, 956002, 917968, 925594, 956708, 953811, 936110, 933220]

/-- The narrow box `Q` around the Perron vector (Codex's bounds, `NOTE.md` §1). -/
def InQ (w : Wt5) : Prop := ∀ j, (qL j : ℝ) / 1000000 ≤ w j ∧ w j ≤ (qU j : ℝ) / 1000000

/-- The normalised ray `F_d / (F_d)₀`. -/
noncomputable def rayW (d : ℕ) : Wt5 := fun j => (Fv d j : ℝ) / Fv d 0

/-- **The weights of the cone**: a point of `Q` or one of the five normalised transient rays. -/
def InCone5 (w : Wt5) : Prop := InQ w ∨ ∃ d, d < 5 ∧ w = rayW d

/-! ### Linear forms on the cone -/

/-- The separable minimum of `10⁶ · Σ cⱼ wⱼ` over `Q`. -/
def qmin (c : Fin 11 → ℤ) : ℤ := ∑ j, min (c j * qL j) (c j * qU j)

/-- The value of a linear form at the ray `F_d`. -/
def rdot (c : Fin 11 → ℤ) (d : ℕ) : ℤ := ∑ j, c j * Fv d j

/-- A linear form is nonnegative on the cone: its separable minimum on `Q` and its five ray
values are nonnegative. -/
def coneOK (c : Fin 11 → ℤ) : Bool :=
  decide (0 ≤ qmin c) && (List.range 5).all (fun d => decide (0 ≤ rdot c d))

theorem Fv_pos : ∀ d < 6, 0 < Fv d 0 := by decide

/-- A linear form on `Q` is at least its separable minimum. -/
theorem lin_Q {w : Wt5} (hw : InQ w) (c : Fin 11 → ℤ) :
    (qmin c : ℝ) ≤ 1000000 * ∑ j, (c j : ℝ) * w j := by
  unfold qmin
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  obtain ⟨hl, hu⟩ := hw j
  rcases le_total 0 (c j : ℝ) with hc | hc
  · refine (min_le_left _ _).trans ?_
    have := mul_le_mul_of_nonneg_left hl hc
    have e : (c j : ℝ) * ((qL j : ℝ) / 1000000) * 1000000 = (c j : ℝ) * qL j := by ring
    nlinarith
  · refine (min_le_right _ _).trans ?_
    have := mul_le_mul_of_nonpos_left hu hc
    nlinarith

/-- A linear form at a normalised ray. -/
theorem lin_ray (d : ℕ) (c : Fin 11 → ℤ) :
    ∑ j, (c j : ℝ) * rayW d j = (rdot c d : ℝ) / Fv d 0 := by
  unfold rdot rayW
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **A linear form with a cone certificate is nonnegative on the cone.** -/
theorem lin_cone {w : Wt5} (hw : InCone5 w) {c : Fin 11 → ℤ} (h : coneOK c = true) :
    0 ≤ ∑ j, (c j : ℝ) * w j := by
  simp only [coneOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
    at h
  obtain ⟨hq, hr⟩ := h
  rcases hw with hw | ⟨d, hd, rfl⟩
  · have := lin_Q hw c
    have hq' : (0 : ℝ) ≤ qmin c := by exact_mod_cast hq
    nlinarith
  · rw [lin_ray]
    have h1 : (0 : ℝ) ≤ rdot c d := by exact_mod_cast hr d hd
    have h2 : (0 : ℝ) < Fv d 0 := by exact_mod_cast Fv_pos d (by omega)
    positivity

/-! ### Weights on the cone -/

theorem qL_zero : qL 0 = 1000000 := rfl
theorem qU_zero : qU 0 = 1000000 := rfl

theorem cone_w0 {w : Wt5} (hw : InCone5 w) : w 0 = 1 := by
  rcases hw with hw | ⟨d, hd, rfl⟩
  · obtain ⟨hl, hu⟩ := hw 0
    rw [qL_zero] at hl; rw [qU_zero] at hu
    norm_num at hl hu
    linarith
  · have h2 : (0 : ℝ) < Fv d 0 := by exact_mod_cast Fv_pos d (by omega)
    simp only [rayW]
    exact div_self h2.ne'

theorem cone_nonneg {w : Wt5} (hw : InCone5 w) (j : Fin 11) : 0 ≤ w j := by
  rcases hw with hw | ⟨d, hd, rfl⟩
  · have := (hw j).1
    have : (0 : ℝ) ≤ (qL j : ℝ) / 1000000 := by positivity
    linarith
  · simp only [rayW]; positivity

theorem rowV5_ge {w : Wt5} (hw : InCone5 w) (i : Fin 11) : (Vmat5 i 0 : ℝ) ≤ rowV5 i w := by
  unfold rowV5
  rw [Fin.sum_univ_succ]
  have h0 : (Vmat5 i 0 : ℝ) * w 0 = Vmat5 i 0 := by rw [cone_w0 hw, mul_one]
  have hr : 0 ≤ ∑ j : Fin 10, (Vmat5 i j.succ : ℝ) * w j.succ :=
    Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (cone_nonneg hw _)
  linarith

theorem Vmat5_pos : ∀ i : Fin 11, 0 < Vmat5 i 0 := by decide

theorem rowV5_pos {w : Wt5} (hw : InCone5 w) (i : Fin 11) : 0 < rowV5 i w := by
  have := rowV5_ge hw i
  have h : (0 : ℝ) < Vmat5 i 0 := by exact_mod_cast Vmat5_pos i
  linarith

/-- The uniform ratio forms `1000 · rowV5 i - 911 · rowV5 j`. -/
def ratioC (i j : Fin 11) : Fin 11 → ℤ := fun o => 1000 * (Vmat5 i o : ℤ) - 911 * Vmat5 j o

theorem ratio_checks : ∀ i j : Fin 11, coneOK (ratioC i j) = true := by decide +kernel

/-- **The uniform ratio on the cone**: any two uniform rows are within the factor `1000/911`. -/
theorem rowV5_ratio {w : Wt5} (hw : InCone5 w) (i j : Fin 11) :
    (911 / 1000 : ℝ) * rowV5 j w ≤ rowV5 i w := by
  have h := lin_cone hw (ratio_checks i j)
  have e : ∑ o, ((ratioC i j o : ℤ) : ℝ) * w o = 1000 * rowV5 i w - 911 * rowV5 j w := by
    unfold ratioC rowV5
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun o _ => ?_
    ring
  rw [e] at h
  linarith

/-! ### The invariance of `Q` -/

/-- The coefficients of `10⁶ · rowV5 i - qL i · rowV5 0`. -/
def lowQ (i : Fin 11) : Fin 11 → ℤ := fun j => 1000000 * (Vmat5 i j : ℤ) - qL i * Vmat5 0 j

/-- The coefficients of `qU i · rowV5 0 - 10⁶ · rowV5 i`. -/
def upQ (i : Fin 11) : Fin 11 → ℤ := fun j => (qU i : ℤ) * Vmat5 0 j - 1000000 * Vmat5 i j

/-- **The box checks**: the separable minima over `Q` are nonnegative (Codex, review (a)). -/
theorem q_checks : ∀ i : Fin 11, 0 ≤ qmin (lowQ i) ∧ 0 ≤ qmin (upQ i) := by
  decide +kernel

theorem inQ_cone {w : Wt5} (hw : InQ w) : InCone5 w := Or.inl hw

/-- **Invariance of `Q`.** -/
theorem nextW5_inQ {w : Wt5} (hw : InQ w) : InQ (nextW5 w) := by
  have hpos := rowV5_pos (inQ_cone hw) 0
  intro i
  obtain ⟨hl, hu⟩ := q_checks i
  have hl' := lin_Q hw (lowQ i)
  have hu' := lin_Q hw (upQ i)
  have el : ∑ j, ((lowQ i j : ℤ) : ℝ) * w j = 1000000 * rowV5 i w - qL i * rowV5 0 w := by
    unfold lowQ rowV5
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun o _ => ?_
    ring
  have eu : ∑ j, ((upQ i j : ℤ) : ℝ) * w j = qU i * rowV5 0 w - 1000000 * rowV5 i w := by
    unfold upQ rowV5
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun o _ => ?_
    ring
  rw [el] at hl'
  rw [eu] at hu'
  have hl'' : (0 : ℝ) ≤ qmin (lowQ i) := by exact_mod_cast hl
  have hu'' : (0 : ℝ) ≤ qmin (upQ i) := by exact_mod_cast hu
  unfold nextW5
  constructor
  · rw [div_le_div_iff₀ (by norm_num) hpos]; nlinarith
  · rw [div_le_div_iff₀ hpos (by norm_num)]; nlinarith

/-! ### The uniform futures -/

/-- The pattern weights of the uniform futures at `k = 5`. -/
noncomputable def wseq5 : ℕ → Wt5
  | 0 => fun _ => 1
  | i + 1 => nextW5 (wseq5 i)

/-- The `01010` value of the uniform futures at `k = 5`. -/
noncomputable def fseq5 : ℕ → ℝ
  | 0 => 1
  | i + 1 => fseq5 i * rowV5 0 (wseq5 i)

/-- The rays are the iterates of the transfer. -/
theorem FL_step : ∀ d < 5, ∀ i : Fin 11, Fv (d + 1) i = ∑ j, Vmat5 i j * Fv d j := by
  decide +kernel

theorem rowV5_rayW {d : ℕ} (hd : d < 5) (i : Fin 11) :
    rowV5 i (rayW d) = (Fv (d + 1) i : ℝ) / Fv d 0 := by
  unfold rowV5 rayW
  rw [FL_step d hd i]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem nextW5_rayW {d : ℕ} (hd : d < 5) : nextW5 (rayW d) = rayW (d + 1) := by
  funext i
  unfold nextW5
  rw [rowV5_rayW hd, rowV5_rayW hd]
  have h1 : (0 : ℝ) < Fv d 0 := by exact_mod_cast Fv_pos d (by omega)
  have h2 : (0 : ℝ) < Fv (d + 1) 0 := by exact_mod_cast Fv_pos (d + 1) (by omega)
  simp only [rayW]
  field_simp

theorem rayW_zero : rayW 0 = fun _ => 1 := by
  funext j
  simp only [rayW]
  have : Fv 0 j = 1 := by fin_cases j <;> rfl
  rw [this]; norm_num [Fv, FL]

theorem wseq5_ray : ∀ d, d ≤ 5 → wseq5 d = rayW d
  | 0, _ => rayW_zero.symm
  | d + 1, h => by
      show nextW5 (wseq5 d) = rayW (d + 1)
      rw [wseq5_ray d (by omega), nextW5_rayW (by omega)]

/-- `F₅` lies in `Q`. -/
theorem ray5_checks : ∀ j : Fin 11, qL j * Fv 5 0 ≤ 1000000 * Fv 5 j ∧
    1000000 * Fv 5 j ≤ qU j * Fv 5 0 := by
  decide +kernel

theorem rayW5_inQ : InQ (rayW 5) := by
  intro j
  obtain ⟨h1, h2⟩ := ray5_checks j
  have h0 : (0 : ℝ) < Fv 5 0 := by exact_mod_cast Fv_pos 5 (by omega)
  have h1' : (qL j : ℝ) * Fv 5 0 ≤ 1000000 * Fv 5 j := by exact_mod_cast h1
  have h2' : (1000000 : ℝ) * Fv 5 j ≤ qU j * Fv 5 0 := by exact_mod_cast h2
  simp only [rayW]
  constructor
  · rw [div_le_div_iff₀ (by norm_num) h0]; linarith
  · rw [div_le_div_iff₀ h0 (by norm_num)]; linarith

theorem wseq5_inQ : ∀ i, 5 ≤ i → InQ (wseq5 i)
  | 0, h => absurd h (by norm_num)
  | i + 1, h => by
      rcases Nat.lt_or_ge i 5 with hi | hi
      · have : i + 1 = 5 := by omega
        rw [this, wseq5_ray 5 le_rfl]; exact rayW5_inQ
      · exact nextW5_inQ (wseq5_inQ i hi)

/-- **Every uniform future lies in the cone.** -/
theorem wseq5_inCone (i : ℕ) : InCone5 (wseq5 i) := by
  rcases Nat.lt_or_ge i 5 with hi | hi
  · exact Or.inr ⟨i, hi, wseq5_ray i (by omega)⟩
  · exact Or.inl (wseq5_inQ i hi)

theorem fseq5_pos : ∀ i, 0 < fseq5 i
  | 0 => one_pos
  | i + 1 => mul_pos (fseq5_pos i) (rowV5_pos (wseq5_inCone i) 0)

/-- **The uniform transfer maps a pattern weight to a pattern weight** at `k = 5`. -/
theorem GU_eq5 (w : Wt5) (hA : rowV5 0 w ≠ 0) {s : T5} (hs : Proper s) :
    GU 5 w s = rowV5 0 w * gw (nextW5 w) s := by
  rw [GU_five w hs, gw, nextW5, mul_div_cancel₀ _ hA]

/-- **The uniform futures by pattern** at `k = 5`. -/
theorem Fu_eq5 : ∀ i (s : T5), Proper s → RowsIn s (range 5) →
    Fu 5 i s = fseq5 i * gw (wseq5 i) s
  | 0, s, _, _ => by simp [Fu, fseq5, wseq5, gw]
  | i + 1, s, hs, hP => by
      have hA := (rowV5_pos (wseq5_inCone i) 0).ne'
      have hsum : Fu 5 (i + 1) s = fseq5 i * GU 5 (wseq5 i) s := by
        simp only [Fu]
        rw [Finset.sum_congr rfl (fun t ht => Fu_eq5 i t (proper_of_mem_sts ht)
          (rowsIn_of_mem_sts_erase ht)), ← Finset.mul_sum,
          ← G_erase_eq_GU (wseq5 i) (by norm_num) hs (card_range 5) hP]
        rfl
      rw [hsum, GU_eq5 _ hA hs]
      simp only [fseq5, wseq5]
      ring

/-- One step of the uniform futures at `k = 5`. -/
theorem Fu_succ_eq5 (i : ℕ) {s : T5} (hs : Proper s) (hP : RowsIn s (range 5)) :
    Fu 5 (i + 1) s = fseq5 i * GU 5 (wseq5 i) s := by
  rw [Fu_eq5 (i + 1) s hs hP, GU_eq5 _ (rowV5_pos (wseq5_inCone i) 0).ne' hs]
  simp only [fseq5, wseq5]
  ring

end GridGen.Five.K5
