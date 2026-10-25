/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.State5

/-!
# Height five, `k = 6`: rational bounds for the logarithms

The certificate `F5` of `ai_research_notes/H5_K6_ANALYTIC_2026-10-23.md` §3.1 is a sum of four
row terms `hrow q q' μ = log (1 + μ/21) - zslope μ · (min (qμ) 1 + min (q'μ) 1)` and an averaged
constant built from the eleven orbit constants `Kr i` (`GridGen/Five/State5.lean`). This module
bounds all of them by rationals with denominator `10⁹`, through the alternating series of
`log (1 + y)` with an explicit remainder (`log_lb_series`, `log_ub_series`, `log_lb_series_neg`,
from `Real.abs_log_sub_add_sum_range_le`):

* `KL i / 10⁹ ≤ Kr i` (`KL_le`; six terms of the series of `log (1 - x)`, error below `10⁻⁷`);
* `HE μ / 10⁹ ≤ hrow qₑ qₘ μ` and `HM μ / 10⁹ ≤ hrow qₘ qₘ μ` for `μ = 0, …, 6` (`HE_le`,
  `HM_le`; ten terms for the main logarithm, six for the chord slope). The shares are
  `qₑ = 1/(1 + 3ρ) = 1000/3877` (end rows) and `qₘ = 1/(1 + 2ρ) = 500/1459` (middle rows),
  `ρ = 959/1000`.
-/

namespace GridGen.Five

open Finset Real

/-! ### The series with remainder -/

theorem log_lb_series {y : ℝ} (h0 : 0 ≤ y) (h1 : y < 1) (n : ℕ) :
    -(∑ i ∈ range n, (-y) ^ (i + 1) / ((i : ℝ) + 1)) - y ^ (n + 1) / (1 - y) ≤ log (1 + y) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -y)
    (by rw [abs_neg, abs_of_nonneg h0]; exact h1) n
  rw [sub_neg_eq_add, abs_neg, abs_of_nonneg h0] at h
  have := (abs_le.mp h).1
  linarith

theorem log_ub_series {y : ℝ} (h0 : 0 ≤ y) (h1 : y < 1) (n : ℕ) :
    log (1 + y) ≤ -(∑ i ∈ range n, (-y) ^ (i + 1) / ((i : ℝ) + 1)) + y ^ (n + 1) / (1 - y) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -y)
    (by rw [abs_neg, abs_of_nonneg h0]; exact h1) n
  rw [sub_neg_eq_add, abs_neg, abs_of_nonneg h0] at h
  have := (abs_le.mp h).2
  linarith

theorem log_lb_series_neg {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    -(∑ i ∈ range n, x ^ (i + 1) / ((i : ℝ) + 1)) - x ^ (n + 1) / (1 - x) ≤ log (1 - x) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := x) (by rw [abs_of_nonneg h0]; exact h1) n
  rw [abs_of_nonneg h0] at h
  have := (abs_le.mp h).1
  linarith

/-! ### The orbit constants -/

/-- Lower bounds for `Kr i`, times `10⁹`. -/
def KLL : List ℤ := [-94466637, -83764589, -84397301, -71025550, -73586372, -57472578,
  -60068297, -73586372, -72946781, -63303500, -62657296]

theorem Kr_eq (i : Fin 11) : Kr i = log (971038 / 1000000 * (123125 / 128018) * (194481 / 125)
    / ∑ j, (Vmat i j : ℝ)) := by
  have hR : 0 < ∑ j, (Vmat i j : ℝ) := by
    fin_cases i <;> simp [Vmat, Fin.sum_univ_succ] <;> norm_num
  unfold Kr
  rw [Real.log_div (by positivity) hR.ne', Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)]


theorem KL_le_0 : ((KLL.getD 0 0 : ℤ) : ℝ) / 10 ^ 9 ≤ Kr 0 := by
  rw [Kr_eq]
  have eR : ∑ j, (Vmat 0 j : ℝ) = 1597 := by
    simp only [Vmat, Fin.sum_univ_succ, Fin.sum_univ_zero]; norm_num
  have ex : 971038 / 1000000 * (123125 / 128018) * (194481 / 125) / (1597 : ℝ)
      = 1 - 1842903134117 / 20444474600000 := by norm_num
  rw [eR, ex]
  refine le_trans ?_ (log_lb_series_neg (by norm_num) (by norm_num) 6)
  simp only [KLL, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

theorem KL_le_1 : ((KLL.getD 1 0 : ℤ) : ℝ) / 10 ^ 9 ≤ Kr 1 := by
  rw [Kr_eq]
  have eR : ∑ j, (Vmat 1 j : ℝ) = 1580 := by
    simp only [Vmat, Fin.sum_univ_succ, Fin.sum_univ_zero]; norm_num
  have ex : 971038 / 1000000 * (123125 / 128018) * (194481 / 125) / (1580 : ℝ)
      = 1 - 1625272534117 / 20226844000000 := by norm_num
  rw [eR, ex]
  refine le_trans ?_ (log_lb_series_neg (by norm_num) (by norm_num) 6)
  simp only [KLL, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

theorem KL_le_2 : ((KLL.getD 2 0 : ℤ) : ℝ) / 10 ^ 9 ≤ Kr 2 := by
  rw [Kr_eq]
  have eR : ∑ j, (Vmat 2 j : ℝ) = 1581 := by
    simp only [Vmat, Fin.sum_univ_succ, Fin.sum_univ_zero]; norm_num
  have ex : 971038 / 1000000 * (123125 / 128018) * (194481 / 125) / (1581 : ℝ)
      = 1 - 546024778039 / 6746548600000 := by norm_num
  rw [eR, ex]
  refine le_trans ?_ (log_lb_series_neg (by norm_num) (by norm_num) 6)
  simp only [KLL, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

theorem KL_le_3 : ((KLL.getD 3 0 : ℤ) : ℝ) / 10 ^ 9 ≤ Kr 3 := by
  rw [Kr_eq]
  have eR : ∑ j, (Vmat 3 j : ℝ) = 1560 := by
    simp only [Vmat, Fin.sum_univ_succ, Fin.sum_univ_zero]; norm_num
  have ex : 971038 / 1000000 * (123125 / 128018) * (194481 / 125) / (1560 : ℝ)
      = 1 - 456412178039 / 6656936000000 := by norm_num
  rw [eR, ex]
  refine le_trans ?_ (log_lb_series_neg (by norm_num) (by norm_num) 6)
  simp only [KLL, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

theorem KL_le_4 : ((KLL.getD 4 0 : ℤ) : ℝ) / 10 ^ 9 ≤ Kr 4 := by
  rw [Kr_eq]
  have eR : ∑ j, (Vmat 4 j : ℝ) = 1564 := by
    simp only [Vmat, Fin.sum_univ_succ, Fin.sum_univ_zero]; norm_num
  have ex : 971038 / 1000000 * (123125 / 128018) * (194481 / 125) / (1564 : ℝ)
      = 1 - 1420443734117 / 20022015200000 := by norm_num
  rw [eR, ex]
  refine le_trans ?_ (log_lb_series_neg (by norm_num) (by norm_num) 6)
  simp only [KLL, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

theorem KL_le_5 : ((KLL.getD 5 0 : ℤ) : ℝ) / 10 ^ 9 ≤ Kr 5 := by
  rw [Kr_eq]
  have eR : ∑ j, (Vmat 5 j : ℝ) = 1539 := by
    simp only [Vmat, Fin.sum_univ_succ, Fin.sum_univ_zero]; norm_num
  have ex : 971038 / 1000000 * (123125 / 128018) * (194481 / 125) / (1539 : ℝ)
      = 1 - 13585169557 / 243234200000 := by norm_num
  rw [eR, ex]
  refine le_trans ?_ (log_lb_series_neg (by norm_num) (by norm_num) 6)
  simp only [KLL, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

theorem KL_le_6 : ((KLL.getD 6 0 : ℤ) : ℝ) / 10 ^ 9 ≤ Kr 6 := by
  rw [Kr_eq]
  have eR : ∑ j, (Vmat 6 j : ℝ) = 1543 := by
    simp only [Vmat, Fin.sum_univ_succ, Fin.sum_univ_zero]; norm_num
  have ex : 971038 / 1000000 * (123125 / 128018) * (194481 / 125) / (1543 : ℝ)
      = 1 - 1151605934117 / 19753177400000 := by norm_num
  rw [eR, ex]
  refine le_trans ?_ (log_lb_series_neg (by norm_num) (by norm_num) 6)
  simp only [KLL, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

theorem KL_le_7 : ((KLL.getD 7 0 : ℤ) : ℝ) / 10 ^ 9 ≤ Kr 7 := by
  rw [Kr_eq]
  have eR : ∑ j, (Vmat 7 j : ℝ) = 1564 := by
    simp only [Vmat, Fin.sum_univ_succ, Fin.sum_univ_zero]; norm_num
  have ex : 971038 / 1000000 * (123125 / 128018) * (194481 / 125) / (1564 : ℝ)
      = 1 - 1420443734117 / 20022015200000 := by norm_num
  rw [eR, ex]
  refine le_trans ?_ (log_lb_series_neg (by norm_num) (by norm_num) 6)
  simp only [KLL, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

theorem KL_le_8 : ((KLL.getD 8 0 : ℤ) : ℝ) / 10 ^ 9 ≤ Kr 8 := by
  rw [Kr_eq]
  have eR : ∑ j, (Vmat 8 j : ℝ) = 1563 := by
    simp only [Vmat, Fin.sum_univ_succ, Fin.sum_univ_zero]; norm_num
  have ex : 971038 / 1000000 * (123125 / 128018) * (194481 / 125) / (1563 : ℝ)
      = 1 - 469213978039 / 6669737800000 := by norm_num
  rw [eR, ex]
  refine le_trans ?_ (log_lb_series_neg (by norm_num) (by norm_num) 6)
  simp only [KLL, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

theorem KL_le_9 : ((KLL.getD 9 0 : ℤ) : ℝ) / 10 ^ 9 ≤ Kr 9 := by
  rw [Kr_eq]
  have eR : ∑ j, (Vmat 9 j : ℝ) = 1548 := by
    simp only [Vmat, Fin.sum_univ_succ, Fin.sum_univ_zero]; norm_num
  have ex : 971038 / 1000000 * (123125 / 128018) * (194481 / 125) / (1548 : ℝ)
      = 1 - 135068326013 / 2201909600000 := by norm_num
  rw [eR, ex]
  refine le_trans ?_ (log_lb_series_neg (by norm_num) (by norm_num) 6)
  simp only [KLL, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

theorem KL_le_10 : ((KLL.getD 10 0 : ℤ) : ℝ) / 10 ^ 9 ≤ Kr 10 := by
  rw [Kr_eq]
  have eR : ∑ j, (Vmat 10 j : ℝ) = 1547 := by
    simp only [Vmat, Fin.sum_univ_succ, Fin.sum_univ_zero]; norm_num
  have ex : 971038 / 1000000 * (123125 / 128018) * (194481 / 125) / (1547 : ℝ)
      = 1 - 171830447731 / 2829197800000 := by norm_num
  rw [eR, ex]
  refine le_trans ?_ (log_lb_series_neg (by norm_num) (by norm_num) 6)
  simp only [KLL, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

theorem KL_le (i : Fin 11) : ((KLL.getD i 0 : ℤ) : ℝ) / 10 ^ 9 ≤ Kr i := by
  fin_cases i
  · exact KL_le_0
  · exact KL_le_1
  · exact KL_le_2
  · exact KL_le_3
  · exact KL_le_4
  · exact KL_le_5
  · exact KL_le_6
  · exact KL_le_7
  · exact KL_le_8
  · exact KL_le_9
  · exact KL_le_10

/-! ### The row terms -/

/-- The fibre shares: end rows and middle rows. -/
noncomputable def qe5 : ℝ := 1000 / 3877
noncomputable def qm5 : ℝ := 500 / 1459

/-- One row of `F5`. -/
noncomputable def hrow (qa qb μ : ℝ) : ℝ :=
  log (1 + μ / 21) - Lookback.zslope 5 μ * (min (qa * μ) 1 + min (qb * μ) 1)

theorem zslope_le_series {m : ℝ} (hm : 0 ≤ m) :
    Lookback.zslope 5 m ≤ (-(∑ i ∈ range 6, (-(2 / (19 + m))) ^ (i + 1) / ((i : ℝ) + 1))
      + (2 / (19 + m)) ^ (6 + 1) / (1 - 2 / (19 + m))) / 2 := by
  unfold Lookback.zslope
  refine (min_le_right _ _).trans ?_
  have h19 : (19 + m) ≠ 0 := by linarith
  have e : ((5 : ℝ) ^ 2 - 5 + 1 + m) / ((5 : ℝ) ^ 2 - 5 + 1 + m - 2) = 1 + 2 / (19 + m) := by
    rw [show ((5 : ℝ) ^ 2 - 5 + 1 + m - 2) = 19 + m by ring,
      show ((5 : ℝ) ^ 2 - 5 + 1 + m) = (19 + m) + 2 by ring, add_div, div_self h19]
  rw [e]
  have h1 : 2 / (19 + m) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have := log_ub_series (y := 2 / (19 + m)) (by positivity) h1 6
  linarith

/-- The row bound from the series, for `μ = m`. -/
theorem hrow_ge {qa qb m : ℝ} (hqa : 0 ≤ qa) (hqb : 0 ≤ qb) (hm : 0 ≤ m) (hm21 : m < 21) :
    -(∑ i ∈ range 10, (-(m / 21)) ^ (i + 1) / ((i : ℝ) + 1)) - (m / 21) ^ (10 + 1) / (1 - m / 21)
      - (-(∑ i ∈ range 6, (-(2 / (19 + m))) ^ (i + 1) / ((i : ℝ) + 1))
        + (2 / (19 + m)) ^ (6 + 1) / (1 - 2 / (19 + m))) / 2 * (min (qa * m) 1 + min (qb * m) 1)
      ≤ hrow qa qb m := by
  unfold hrow
  have hl := log_lb_series (y := m / 21) (by positivity)
    (by rw [div_lt_one (by norm_num)]; exact hm21) 10
  have hz := zslope_le_series hm
  have hp : 0 ≤ min (qa * m) 1 + min (qb * m) 1 :=
    add_nonneg (le_min (mul_nonneg hqa hm) zero_le_one) (le_min (mul_nonneg hqb hm) zero_le_one)
  have := mul_le_mul_of_nonneg_right hz hp
  linarith

/-- Lower bounds for the end-row terms `hrow qₑ qₘ μ`, times `10⁹`. -/
def HEL : List ℤ := [0, 17896820, 36331187, 56361211, 90971726, 133531172, 174351842]

/-- Lower bounds for the middle-row terms `hrow qₘ qₘ μ`, times `10⁹`. -/
def HML : List ℤ := [0, 13857137, 28619586, 46519965, 90971726, 133531172, 174351842]

theorem HE_le_0 : ((HEL.getD 0 0 : ℤ) : ℝ) / 10 ^ 9 ≤ hrow qe5 qm5 0 := by
  refine le_trans ?_ (hrow_ge (by norm_num [qe5]) (by norm_num [qm5]) (by norm_num) (by norm_num))
  simp only [HEL, Finset.sum_range_succ, Finset.sum_range_zero, qe5, qm5]
  norm_num [min_def]

theorem HE_le_1 : ((HEL.getD 1 0 : ℤ) : ℝ) / 10 ^ 9 ≤ hrow qe5 qm5 1 := by
  refine le_trans ?_ (hrow_ge (by norm_num [qe5]) (by norm_num [qm5]) (by norm_num) (by norm_num))
  simp only [HEL, Finset.sum_range_succ, Finset.sum_range_zero, qe5, qm5]
  norm_num [min_def]

theorem HE_le_2 : ((HEL.getD 2 0 : ℤ) : ℝ) / 10 ^ 9 ≤ hrow qe5 qm5 2 := by
  refine le_trans ?_ (hrow_ge (by norm_num [qe5]) (by norm_num [qm5]) (by norm_num) (by norm_num))
  simp only [HEL, Finset.sum_range_succ, Finset.sum_range_zero, qe5, qm5]
  norm_num [min_def]

theorem HE_le_3 : ((HEL.getD 3 0 : ℤ) : ℝ) / 10 ^ 9 ≤ hrow qe5 qm5 3 := by
  refine le_trans ?_ (hrow_ge (by norm_num [qe5]) (by norm_num [qm5]) (by norm_num) (by norm_num))
  simp only [HEL, Finset.sum_range_succ, Finset.sum_range_zero, qe5, qm5]
  norm_num [min_def]

theorem HE_le_4 : ((HEL.getD 4 0 : ℤ) : ℝ) / 10 ^ 9 ≤ hrow qe5 qm5 4 := by
  refine le_trans ?_ (hrow_ge (by norm_num [qe5]) (by norm_num [qm5]) (by norm_num) (by norm_num))
  simp only [HEL, Finset.sum_range_succ, Finset.sum_range_zero, qe5, qm5]
  norm_num [min_def]

theorem HE_le_5 : ((HEL.getD 5 0 : ℤ) : ℝ) / 10 ^ 9 ≤ hrow qe5 qm5 5 := by
  refine le_trans ?_ (hrow_ge (by norm_num [qe5]) (by norm_num [qm5]) (by norm_num) (by norm_num))
  simp only [HEL, Finset.sum_range_succ, Finset.sum_range_zero, qe5, qm5]
  norm_num [min_def]

theorem HE_le_6 : ((HEL.getD 6 0 : ℤ) : ℝ) / 10 ^ 9 ≤ hrow qe5 qm5 6 := by
  refine le_trans ?_ (hrow_ge (by norm_num [qe5]) (by norm_num [qm5]) (by norm_num) (by norm_num))
  simp only [HEL, Finset.sum_range_succ, Finset.sum_range_zero, qe5, qm5]
  norm_num [min_def]

theorem HM_le_0 : ((HML.getD 0 0 : ℤ) : ℝ) / 10 ^ 9 ≤ hrow qm5 qm5 0 := by
  refine le_trans ?_ (hrow_ge (by norm_num [qm5]) (by norm_num [qm5]) (by norm_num) (by norm_num))
  simp only [HML, Finset.sum_range_succ, Finset.sum_range_zero, qm5, qm5]
  norm_num [min_def]

theorem HM_le_1 : ((HML.getD 1 0 : ℤ) : ℝ) / 10 ^ 9 ≤ hrow qm5 qm5 1 := by
  refine le_trans ?_ (hrow_ge (by norm_num [qm5]) (by norm_num [qm5]) (by norm_num) (by norm_num))
  simp only [HML, Finset.sum_range_succ, Finset.sum_range_zero, qm5, qm5]
  norm_num [min_def]

theorem HM_le_2 : ((HML.getD 2 0 : ℤ) : ℝ) / 10 ^ 9 ≤ hrow qm5 qm5 2 := by
  refine le_trans ?_ (hrow_ge (by norm_num [qm5]) (by norm_num [qm5]) (by norm_num) (by norm_num))
  simp only [HML, Finset.sum_range_succ, Finset.sum_range_zero, qm5, qm5]
  norm_num [min_def]

theorem HM_le_3 : ((HML.getD 3 0 : ℤ) : ℝ) / 10 ^ 9 ≤ hrow qm5 qm5 3 := by
  refine le_trans ?_ (hrow_ge (by norm_num [qm5]) (by norm_num [qm5]) (by norm_num) (by norm_num))
  simp only [HML, Finset.sum_range_succ, Finset.sum_range_zero, qm5, qm5]
  norm_num [min_def]

theorem HM_le_4 : ((HML.getD 4 0 : ℤ) : ℝ) / 10 ^ 9 ≤ hrow qm5 qm5 4 := by
  refine le_trans ?_ (hrow_ge (by norm_num [qm5]) (by norm_num [qm5]) (by norm_num) (by norm_num))
  simp only [HML, Finset.sum_range_succ, Finset.sum_range_zero, qm5, qm5]
  norm_num [min_def]

theorem HM_le_5 : ((HML.getD 5 0 : ℤ) : ℝ) / 10 ^ 9 ≤ hrow qm5 qm5 5 := by
  refine le_trans ?_ (hrow_ge (by norm_num [qm5]) (by norm_num [qm5]) (by norm_num) (by norm_num))
  simp only [HML, Finset.sum_range_succ, Finset.sum_range_zero, qm5, qm5]
  norm_num [min_def]

theorem HM_le_6 : ((HML.getD 6 0 : ℤ) : ℝ) / 10 ^ 9 ≤ hrow qm5 qm5 6 := by
  refine le_trans ?_ (hrow_ge (by norm_num [qm5]) (by norm_num [qm5]) (by norm_num) (by norm_num))
  simp only [HML, Finset.sum_range_succ, Finset.sum_range_zero, qm5, qm5]
  norm_num [min_def]

theorem HE_le {m : ℕ} (hm : m ≤ 6) : ((HEL.getD m 0 : ℤ) : ℝ) / 10 ^ 9 ≤ hrow qe5 qm5 m := by
  interval_cases m
  · exact_mod_cast HE_le_0
  · exact_mod_cast HE_le_1
  · exact_mod_cast HE_le_2
  · exact_mod_cast HE_le_3
  · exact_mod_cast HE_le_4
  · exact_mod_cast HE_le_5
  · exact_mod_cast HE_le_6

theorem HM_le {m : ℕ} (hm : m ≤ 6) : ((HML.getD m 0 : ℤ) : ℝ) / 10 ^ 9 ≤ hrow qm5 qm5 m := by
  interval_cases m
  · exact_mod_cast HM_le_0
  · exact_mod_cast HM_le_1
  · exact_mod_cast HM_le_2
  · exact_mod_cast HM_le_3
  · exact_mod_cast HM_le_4
  · exact_mod_cast HM_le_5
  · exact_mod_cast HM_le_6

end GridGen.Five
