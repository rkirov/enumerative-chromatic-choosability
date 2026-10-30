/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Six.Uniform

/-!
# Height six at `k = 6`: the uniform transfer and its invariant cone

The cone route of Codex (OpenAI), `ai_research_notes/cx/h6k6/NOTE.md`, checked independently in
`ai_research_notes/H6_K6_REVIEW_2026-10-29.md` §1; `GridGen/Five/K5/Cone.lean` with six rows.

**The cone.** Its generators are five transient rays `F_d = T^d 1` (`d ≤ 4`, integer vectors
`Fv d`, normalised to `rayW d`) and a narrow box `Q` around the Perron vector (`InQ6`, edges
`qL/10⁷ ≤ w ≤ qU/10⁷`, widths `7·10⁻⁷`, with `w₀ = 1`). The weights used are the uniform futures
`wseq6 i`: for `i ≤ 4` they are the normalised rays (`wseq6_ray`), `wseq6 5 = rayW 5` lies in `Q`,
and the transfer maps `Q` into itself (`nextW6_inQ`, a separable kernel check of 64 linear forms),
so every `wseq6 i` lies in the union `InCone6` of `Q` and the five rays (`wseq6_inCone`).

**Linear forms on the cone** (`lin_cone6`): a form with integer coefficients is nonnegative on
`InCone6` when its five ray values and its separable minimum over `Q` are nonnegative
(`coneOK6`). This gives `w₀ = 1`, `w ≥ 0`, and the uniform ratio
`rowV6 i w ≥ (9483/10000) · rowV6 j w` (`rowV6_ratio`).
-/

namespace GridGen.Six

open Finset

/-- The next weights of the uniform transfer, normalised by the alternating row. -/
noncomputable def nextW6 (w : Wt6) : Wt6 := fun i => rowV6 i w / rowV6 0 w

/-! ### The cone -/

/-- The rays `F_d = T^d 1`, `d ≤ 5`. -/
def FL : List (List ℕ) := data% "[[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1],[6765,6693,6608,6697,6625,6629,6625,6524,6613,6541,6540,6561,6629,6557,6436,6453,6541,6537,6473,6452,6469,6558,6621,6622,6553,6554,6494,6490,6469,6470,6485,6486],[44288437,43792714,43198265,43819702,43323996,43360222,43328363,42616829,43233891,42742552,42733938,42891504,43351001,42859662,42009727,42134005,42747308,42715449,42282957,42126837,42251115,42871586,43295311,43304061,42830984,42839727,42439077,42407235,42249548,42258283,42366657,42375393],[289461704061,286212109662,282309246766,286388072723,283138614728,283382511997,283170547850,278496484708,282543310526,279325785653,279267879570,280309017063,283314714193,280097189320,274518193505,275336408475,279361201697,279149237550,276319639885,275289597172,276107812142,280179416667,282949776558,283008877928,279908409362,279967452520,277349682598,277137854855,276095647304,276154623445,276867042166,276926027112],[1891687307712305,1870446658686449,1844932725721117,1871596147585976,1850356407271350,1851954121686116,1850566922806219,1820010391897336,1846462848550851,1825433623771094,1825054288663485,1831863870271017,1851506804882107,1830477580102350,1794008070497429,1799357753308091,1825667735688244,1824280536808347,1805787999808014,1799052026828685,1804401709639347,1831017418498906,1849121596841099,1849509046788009,1829243159783467,1829630219619009,1812523972787343,1811137682618676,1804320825959686,1804707436118753,1809364722725835,1809751392450009],[12362461587768733281,12223649114851428195,12056908170767660825,12231160909702811323,12092354384715730231,12102797513953341866,12093731015702404975,11894034770073679343,12066907932272864374,11929478038272458026,11926998574733190813,11971502783817643902,12099872127497337353,11962442233496931005,11724104535428428249,11759066544594093660,11931009389288302756,11921942891037365865,11801091290139279536,11757068730652901228,11792030739818566639,11965971398453968167,12084284356015984716,12086817051421830502,11954374759981514704,11956904900203031276,11845113849625657844,11836053299304944947,11791501359287533222,11794028553759759071,11824465163947044692,11826992748984232050]]"

/-- Entry `j` of the ray `F_d`. -/
def Fv (d : ℕ) (j : Fin 32) : ℕ := (FL.getD d []).getD j 0

/-- The lower edges of `Q`, times `10⁷`. -/
def qLL : List ℕ := data% "[10000000,9887711,9752834,9893787,9781506,9789954,9782620,9621085,9760923,9649756,9647750,9683750,9787588,9676420,9483629,9511910,9650994,9643660,9545904,9510294,9538574,9679275,9774979,9777027,9669895,9671941,9581514,9574184,9538146,9540190,9564811,9566855]"

/-- The upper edges of `Q`, times `10⁷`. -/
def qUL : List ℕ := data% "[10000000,9887718,9752841,9893794,9781513,9789961,9782627,9621092,9760930,9649763,9647757,9683757,9787595,9676427,9483636,9511917,9651001,9643667,9545911,9510301,9538581,9679282,9774986,9777034,9669902,9671948,9581521,9574191,9538153,9540197,9564818,9566862]"

def qL (j : Fin 32) : ℕ := qLL.getD j 0
def qU (j : Fin 32) : ℕ := qUL.getD j 0

/-- The narrow box `Q` around the Perron vector (Codex's bounds, `cone6.json`). -/
def InQ6 (w : Wt6) : Prop := ∀ j, (qL j : ℝ) / 10000000 ≤ w j ∧ w j ≤ (qU j : ℝ) / 10000000

/-- The normalised ray `F_d / (F_d)₀`. -/
noncomputable def rayW (d : ℕ) : Wt6 := fun j => (Fv d j : ℝ) / Fv d 0

/-- **The weights of the cone**: a point of `Q` or one of the five normalised transient rays. -/
def InCone6 (w : Wt6) : Prop := InQ6 w ∨ ∃ d, d < 5 ∧ w = rayW d

/-! ### Linear forms on the cone -/

/-- The separable minimum of `10⁷ · Σ cⱼ wⱼ` over `Q`. -/
def qmin (c : Fin 32 → ℤ) : ℤ := ∑ j, min (c j * qL j) (c j * qU j)

/-- The value of a linear form at the ray `F_d`. -/
def rdot (c : Fin 32 → ℤ) (d : ℕ) : ℤ := ∑ j, c j * Fv d j

/-- A linear form is nonnegative on the cone: its separable minimum on `Q` and its five ray
values are nonnegative. -/
def coneOK6 (c : Fin 32 → ℤ) : Bool :=
  decide (0 ≤ qmin c) && (List.range 5).all (fun d => decide (0 ≤ rdot c d))

theorem Fv_pos : ∀ d < 6, 0 < Fv d 0 := by decide +kernel

/-- A linear form on `Q` is at least its separable minimum. -/
theorem lin_Q {w : Wt6} (hw : InQ6 w) (c : Fin 32 → ℤ) :
    (qmin c : ℝ) ≤ 10000000 * ∑ j, (c j : ℝ) * w j := by
  unfold qmin
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  obtain ⟨hl, hu⟩ := hw j
  rcases le_total 0 (c j : ℝ) with hc | hc
  · refine (min_le_left _ _).trans ?_
    have := mul_le_mul_of_nonneg_left hl hc
    have e : (c j : ℝ) * ((qL j : ℝ) / 10000000) * 10000000 = (c j : ℝ) * qL j := by ring
    nlinarith
  · refine (min_le_right _ _).trans ?_
    have := mul_le_mul_of_nonpos_left hu hc
    nlinarith

/-- A linear form at a normalised ray. -/
theorem lin_ray (d : ℕ) (c : Fin 32 → ℤ) :
    ∑ j, (c j : ℝ) * rayW d j = (rdot c d : ℝ) / Fv d 0 := by
  unfold rdot rayW
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **A linear form with a cone certificate is nonnegative on the cone.** -/
theorem lin_cone6 {w : Wt6} (hw : InCone6 w) {c : Fin 32 → ℤ} (h : coneOK6 c = true) :
    0 ≤ ∑ j, (c j : ℝ) * w j := by
  simp only [coneOK6, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
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

theorem qL_zero : qL 0 = 10000000 := by decide +kernel
theorem qU_zero : qU 0 = 10000000 := by decide +kernel

theorem cone_w0 {w : Wt6} (hw : InCone6 w) : w 0 = 1 := by
  rcases hw with hw | ⟨d, hd, rfl⟩
  · obtain ⟨hl, hu⟩ := hw 0
    rw [qL_zero] at hl; rw [qU_zero] at hu
    norm_num at hl hu
    linarith
  · have h2 : (0 : ℝ) < Fv d 0 := by exact_mod_cast Fv_pos d (by omega)
    simp only [rayW]
    exact div_self h2.ne'

theorem cone_nonneg {w : Wt6} (hw : InCone6 w) (j : Fin 32) : 0 ≤ w j := by
  rcases hw with hw | ⟨d, hd, rfl⟩
  · have := (hw j).1
    have : (0 : ℝ) ≤ (qL j : ℝ) / 10000000 := by positivity
    linarith
  · simp only [rayW]; positivity

theorem rowV6_ge {w : Wt6} (hw : InCone6 w) (i : Fin 32) : (Vmat6 i 0 : ℝ) ≤ rowV6 i w := by
  unfold rowV6
  rw [Fin.sum_univ_succ]
  have h0 : (Vmat6 i 0 : ℝ) * w 0 = Vmat6 i 0 := by rw [cone_w0 hw, mul_one]
  have hr : 0 ≤ ∑ j : Fin 31, (Vmat6 i j.succ : ℝ) * w j.succ :=
    Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (cone_nonneg hw _)
  linarith

theorem Vmat6_pos : ∀ i : Fin 32, 0 < Vmat6 i 0 := by decide +kernel

theorem rowV6_pos {w : Wt6} (hw : InCone6 w) (i : Fin 32) : 0 < rowV6 i w := by
  have := rowV6_ge hw i
  have h : (0 : ℝ) < Vmat6 i 0 := by exact_mod_cast Vmat6_pos i
  linarith

/-- The forms `10000 · rowV6 i - 9483 · rowV6 0` and `rowV6 0 - rowV6 i`. -/
def lowR (i : Fin 32) : Fin 32 → ℤ := fun o => 10000 * (Vmat6 i o : ℤ) - 9483 * Vmat6 0 o
def upR (i : Fin 32) : Fin 32 → ℤ := fun o => (Vmat6 0 o : ℤ) - Vmat6 i o

theorem ratio_checks : ∀ i : Fin 32, coneOK6 (lowR i) = true ∧ coneOK6 (upR i) = true := by
  decide +kernel

theorem lin_eq_rowV (a b : ℤ) (i j : Fin 32) (w : Wt6) :
    ∑ o, ((a * (Vmat6 i o : ℤ) - b * Vmat6 j o : ℤ) : ℝ) * w o
      = (a : ℝ) * rowV6 i w - (b : ℝ) * rowV6 j w := by
  unfold rowV6
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun o _ => ?_
  ring

/-- **The uniform ratio on the cone**: any two uniform rows are within the factor
`10000/9483`. -/
theorem rowV6_ratio {w : Wt6} (hw : InCone6 w) (i j : Fin 32) :
    (9483 / 10000 : ℝ) * rowV6 j w ≤ rowV6 i w := by
  have h1 := lin_cone6 hw (ratio_checks i).1
  have h2 := lin_cone6 hw (ratio_checks j).2
  have e1 : ∑ o, ((lowR i o : ℤ) : ℝ) * w o = 10000 * rowV6 i w - 9483 * rowV6 0 w := by
    have := lin_eq_rowV 10000 9483 i 0 w; simp only [lowR]; push_cast at this ⊢; linarith
  have e2 : ∑ o, ((upR j o : ℤ) : ℝ) * w o = rowV6 0 w - rowV6 j w := by
    have := lin_eq_rowV 1 1 0 j w; simp only [upR]; push_cast at this ⊢; simpa using this
  rw [e1] at h1
  rw [e2] at h2
  linarith

/-! ### The invariance of `Q` -/

/-- The coefficients of `10⁷ · rowV6 i - qL i · rowV6 0`. -/
def lowQ (i : Fin 32) : Fin 32 → ℤ := fun j => 10000000 * (Vmat6 i j : ℤ) - qL i * Vmat6 0 j

/-- The coefficients of `qU i · rowV6 0 - 10⁷ · rowV6 i`. -/
def upQ (i : Fin 32) : Fin 32 → ℤ := fun j => (qU i : ℤ) * Vmat6 0 j - 10000000 * Vmat6 i j

/-- **The box checks**: the separable minima over `Q` are nonnegative (Codex, review §1). -/
theorem q_checks : ∀ i : Fin 32, 0 ≤ qmin (lowQ i) ∧ 0 ≤ qmin (upQ i) := by
  decide +kernel

theorem inQ_cone {w : Wt6} (hw : InQ6 w) : InCone6 w := Or.inl hw

/-- **Invariance of `Q`.** -/
theorem nextW6_inQ {w : Wt6} (hw : InQ6 w) : InQ6 (nextW6 w) := by
  have hpos := rowV6_pos (inQ_cone hw) 0
  intro i
  obtain ⟨hl, hu⟩ := q_checks i
  have hl' := lin_Q hw (lowQ i)
  have hu' := lin_Q hw (upQ i)
  have el : ∑ j, ((lowQ i j : ℤ) : ℝ) * w j = 10000000 * rowV6 i w - qL i * rowV6 0 w := by
    unfold lowQ rowV6
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun o _ => ?_
    ring
  have eu : ∑ j, ((upQ i j : ℤ) : ℝ) * w j = qU i * rowV6 0 w - 10000000 * rowV6 i w := by
    unfold upQ rowV6
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun o _ => ?_
    ring
  rw [el] at hl'
  rw [eu] at hu'
  have hl'' : (0 : ℝ) ≤ qmin (lowQ i) := by exact_mod_cast hl
  have hu'' : (0 : ℝ) ≤ qmin (upQ i) := by exact_mod_cast hu
  unfold nextW6
  constructor
  · rw [div_le_div_iff₀ (by norm_num) hpos]; nlinarith
  · rw [div_le_div_iff₀ hpos (by norm_num)]; nlinarith

/-! ### The uniform futures -/

/-- The weighted uniform futures of a column: `Fu k (i+1) s` sums `Fu k i` over the uniform
successors of `s`. -/
noncomputable def Fu (k : ℕ) : ℕ → T6 → ℝ
  | 0 => fun _ => 1
  | i + 1 => fun s => ∑ t ∈ sts ((range k).erase (r1 s)) ((range k).erase (r2 s))
      ((range k).erase (r3 s)) ((range k).erase (r4 s)) ((range k).erase (r5 s))
      ((range k).erase (r6 s)), Fu k i t

/-- The pattern weights of the uniform futures at `k = 6`. -/
noncomputable def wseq6 : ℕ → Wt6
  | 0 => fun _ => 1
  | i + 1 => nextW6 (wseq6 i)

/-- The alternating value of the uniform futures at `k = 6`. -/
noncomputable def fseq6 : ℕ → ℝ
  | 0 => 1
  | i + 1 => fseq6 i * rowV6 0 (wseq6 i)

/-- The rays are the iterates of the transfer. -/
theorem FL_step : ∀ d < 5, ∀ i : Fin 32, Fv (d + 1) i = ∑ j, Vmat6 i j * Fv d j := by
  decide +kernel

theorem rowV6_rayW {d : ℕ} (hd : d < 5) (i : Fin 32) :
    rowV6 i (rayW d) = (Fv (d + 1) i : ℝ) / Fv d 0 := by
  unfold rowV6 rayW
  rw [FL_step d hd i]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem nextW6_rayW {d : ℕ} (hd : d < 5) : nextW6 (rayW d) = rayW (d + 1) := by
  funext i
  unfold nextW6
  rw [rowV6_rayW hd, rowV6_rayW hd]
  have h1 : (0 : ℝ) < Fv d 0 := by exact_mod_cast Fv_pos d (by omega)
  have h2 : (0 : ℝ) < Fv (d + 1) 0 := by exact_mod_cast Fv_pos (d + 1) (by omega)
  simp only [rayW]
  field_simp

theorem Fv_zero : ∀ j : Fin 32, Fv 0 j = 1 := by decide +kernel

theorem rayW_zero : rayW 0 = fun _ => 1 := by
  funext j
  simp only [rayW, Fv_zero]
  norm_num

theorem wseq6_ray : ∀ d, d ≤ 5 → wseq6 d = rayW d
  | 0, _ => rayW_zero.symm
  | d + 1, h => by
      show nextW6 (wseq6 d) = rayW (d + 1)
      rw [wseq6_ray d (by omega), nextW6_rayW (by omega)]

/-- `F₅` lies in `Q`. -/
theorem ray5_checks : ∀ j : Fin 32, qL j * Fv 5 0 ≤ 10000000 * Fv 5 j ∧
    10000000 * Fv 5 j ≤ qU j * Fv 5 0 := by
  decide +kernel

theorem rayW5_inQ : InQ6 (rayW 5) := by
  intro j
  obtain ⟨h1, h2⟩ := ray5_checks j
  have h0 : (0 : ℝ) < Fv 5 0 := by exact_mod_cast Fv_pos 5 (by omega)
  have h1' : (qL j : ℝ) * Fv 5 0 ≤ 10000000 * Fv 5 j := by exact_mod_cast h1
  have h2' : (10000000 : ℝ) * Fv 5 j ≤ qU j * Fv 5 0 := by exact_mod_cast h2
  simp only [rayW]
  constructor
  · rw [div_le_div_iff₀ (by norm_num) h0]; linarith
  · rw [div_le_div_iff₀ h0 (by norm_num)]; linarith

theorem wseq6_inQ : ∀ i, 5 ≤ i → InQ6 (wseq6 i)
  | 0, h => absurd h (by norm_num)
  | i + 1, h => by
      rcases Nat.lt_or_ge i 5 with hi | hi
      · have : i + 1 = 5 := by omega
        rw [this, wseq6_ray 5 le_rfl]; exact rayW5_inQ
      · exact nextW6_inQ (wseq6_inQ i hi)

/-- **Every uniform future lies in the cone.** -/
theorem wseq6_inCone (i : ℕ) : InCone6 (wseq6 i) := by
  rcases Nat.lt_or_ge i 5 with hi | hi
  · exact Or.inr ⟨i, hi, wseq6_ray i (by omega)⟩
  · exact Or.inl (wseq6_inQ i hi)

theorem fseq6_pos : ∀ i, 0 < fseq6 i
  | 0 => one_pos
  | i + 1 => mul_pos (fseq6_pos i) (rowV6_pos (wseq6_inCone i) 0)

/-- **The uniform transfer maps a pattern weight to a pattern weight** at `k = 6`. -/
theorem GU_eq6 (w : Wt6) (hA : rowV6 0 w ≠ 0) {s : T6} (hs : Proper s) :
    GU 6 w s = rowV6 0 w * gw (nextW6 w) s := by
  rw [GU_six w hs, gw, nextW6, mul_div_cancel₀ _ hA]

theorem rowsIn_of_mem_sts_erase {k : ℕ} {s t : T6}
    (ht : t ∈ sts ((range k).erase (r1 s)) ((range k).erase (r2 s)) ((range k).erase (r3 s))
      ((range k).erase (r4 s)) ((range k).erase (r5 s)) ((range k).erase (r6 s))) :
    RowsIn t (range k) := by
  rw [mem_sts] at ht
  exact ⟨Finset.mem_of_mem_erase ht.1, Finset.mem_of_mem_erase ht.2.1,
    Finset.mem_of_mem_erase ht.2.2.1, Finset.mem_of_mem_erase ht.2.2.2.1,
    Finset.mem_of_mem_erase ht.2.2.2.2.1, Finset.mem_of_mem_erase ht.2.2.2.2.2.1⟩

/-- **The uniform futures by pattern** at `k = 6`. -/
theorem Fu_eq6 : ∀ i (s : T6), Proper s → RowsIn s (range 6) →
    Fu 6 i s = fseq6 i * gw (wseq6 i) s
  | 0, s, _, _ => by simp [Fu, fseq6, wseq6, gw]
  | i + 1, s, hs, hP => by
      have hA := (rowV6_pos (wseq6_inCone i) 0).ne'
      have hsum : Fu 6 (i + 1) s = fseq6 i * GU 6 (wseq6 i) s := by
        simp only [Fu]
        rw [Finset.sum_congr rfl (fun t ht => Fu_eq6 i t (proper_of_mem_sts ht)
          (rowsIn_of_mem_sts_erase ht)), ← Finset.mul_sum,
          ← G_erase_eq_GU (wseq6 i) (by norm_num) hs (card_range 6) hP]
        rfl
      rw [hsum, GU_eq6 _ hA hs]
      simp only [fseq6, wseq6]
      ring

/-- One step of the uniform futures at `k = 6`. -/
theorem Fu_succ_eq6 (i : ℕ) {s : T6} (hs : Proper s) (hP : RowsIn s (range 6)) :
    Fu 6 (i + 1) s = fseq6 i * GU 6 (wseq6 i) s := by
  rw [Fu_eq6 (i + 1) s hs hP, GU_eq6 _ (rowV6_pos (wseq6_inCone i) 0).ne' hs]
  simp only [fseq6, wseq6]
  ring

end GridGen.Six
