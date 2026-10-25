/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.CountBound

/-!
# Height four: sharper row bounds for `k = 6`

Two refinements of `LogBounds.lean`, needed at `k = 6`:

* **The chord in `z`** (in `GridGen/Lookback/Common.lean`, as height five uses it too). The
  bonus-free rate of a row is `t + (μ - z)/n`, so its log against `t` is `log (1 + (μ - z)/A)`.
  This is concave in `z`, and on `z ∈ [0, 2]` it lies above the chord between `z = 0` and `z = 2`.
  The state colours in the difference sets therefore cost
  `zslope n μ = min (1/(n(n-1)), log ((A+μ)/(A+μ-2))/2)` each (`rate_main_chord`), which is less
  than `1/(n(n-1))` once `μ ≥ 1`.
* **The error with a minimum.** The third-row deviation numerator is
  `n₂t₁₂₃ - e₁₂e₂₃ ≥ -(n₂-e₁₂)·min (n₂-e₂₃, e₁₂)`, because `t₁₂₃ ≥ max (0, e₁₂ + e₂₃ - n₂)`
  (`rate3_err_emin`). The fourth row is the same, with `t₂₃₄` (`rate4_err_emin`). Both matter only
  for large mismatches.
-/

namespace GridGen.Four

open Real GridGen.Lookback

/-! ### The errors with a minimum -/

/-- `n t - a b ≥ -(n-a)·min (n-b, a)` when `t ≥ max (0, a + b - n)` and `a, b ≤ n`. -/
theorem tri_min {n a b t : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (han : a ≤ n) (hbn : b ≤ n) (ht0 : 0 ≤ t)
    (ht : a + b - n ≤ t) : -((n - a) * min (n - b) a) ≤ n * t - a * b := by
  rcases le_total n (a + b) with h | h
  · rw [min_eq_left (by linarith)]
    have : 0 ≤ n := by linarith
    nlinarith
  · rw [min_eq_right (by linarith)]
    have : 0 ≤ n := by linarith
    nlinarith

/-- `n t - a b ≥ -min ((n-a)(n-b), a b)` under the same conditions. -/
theorem tri_min' {n a b t : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (han : a ≤ n) (hbn : b ≤ n)
    (ht0 : 0 ≤ t) (ht : a + b - n ≤ t) : -min ((n - a) * (n - b)) (a * b) ≤ n * t - a * b := by
  rcases le_total n (a + b) with h | h
  · rw [min_eq_left (by nlinarith)]
    nlinarith
  · rw [min_eq_right (by nlinarith)]
    have : 0 ≤ n := by linarith
    nlinarith

/-- **Row three, actual side, with the minimum.** -/
theorem rate3_err_emin {n n1 n2 n3 e12 e23 t123 μ2 μ3 : ℝ} (hn : 5 ≤ n)
    (hn1 : n ≤ n1) (hn1' : n1 ≤ n + 1) (hn2 : n ≤ n2) (hn2' : n2 ≤ n + 1)
    (hn3 : n ≤ n3) (hn3' : n3 ≤ n + 1)
    (he12 : 0 ≤ e12) (he12n : e12 ≤ n1) (he12m : e12 ≤ n2) (he23 : 0 ≤ e23) (he23n : e23 ≤ n2)
    (ht : e12 + e23 - n2 ≤ t123) (ht0 : 0 ≤ t123) (hM0 : 0 ≤ n1 * e23 - t123)
    (hMN : n1 * e23 - t123 ≤ n1 * n2 - e12)
    (hd2 : n2 - e12 ≤ μ2 + 1) (hd3 : n2 - e23 ≤ μ3 + 1) (he12μ : e12 ≤ n + 3 - μ2)
    (hμ2 : 0 ≤ μ2) (hμ3 : 0 ≤ μ3) (hμ2k : μ2 ≤ n + 1) :
    -((μ2 + 1) * min (μ3 + 1) (n + 3 - μ2) / (n ^ 2 * (n - 1) ^ 2))
      ≤ log (((n3 * (n1 * n2 - e12) - (n1 * e23 - t123)) / (n1 * n2 - e12)) / (n3 - e23 / n2)) := by
  have hn0 : 0 < n := by linarith
  have hl0 : 0 < n - 1 := by linarith
  have hn2p : 0 < n2 := by linarith
  have hN2 : n * (n - 1) ≤ n1 * n2 - e12 := by nlinarith
  have hN2p : 0 < n1 * n2 - e12 := by nlinarith
  have hr3hi : (n3 * (n1 * n2 - e12) - (n1 * e23 - t123)) / (n1 * n2 - e12) ≤ n + 1 := by
    rw [div_le_iff₀ hN2p]; nlinarith
  have hrt0 : 0 < n3 - e23 / n2 := by
    have : e23 / n2 ≤ 1 := by rw [div_le_one hn2p]; exact he23n
    linarith
  have hid : (n3 * (n1 * n2 - e12) - (n1 * e23 - t123)) / (n1 * n2 - e12) - (n3 - e23 / n2)
      = (n2 * t123 - e12 * e23) / (n2 * (n1 * n2 - e12)) := by
    field_simp; ring
  have hden : 0 < n2 * (n1 * n2 - e12) := by positivity
  have hnum := tri_min he12 he23 he12m he23n ht0 ht
  have h1 : 0 ≤ n2 - e12 := by linarith
  have hm0 : 0 ≤ min (n2 - e23) e12 := le_min (by linarith) he12
  have hmle : min (n2 - e23) e12 ≤ min (μ3 + 1) (n + 3 - μ2) :=
    min_le_min hd3 he12μ
  have hprod : (n2 - e12) * min (n2 - e23) e12 ≤ (μ2 + 1) * min (μ3 + 1) (n + 3 - μ2) :=
    mul_le_mul hd2 hmle hm0 (by linarith)
  have hbig : n ^ 2 * (n - 1) ≤ n2 * (n1 * n2 - e12) := by
    have : n * n * (n - 1) ≤ n2 * (n1 * n2 - e12) :=
      mul_le_mul hn2 hN2 (by positivity) (by linarith) |>.trans_eq' (by ring)
    nlinarith
  have hQ0 : 0 ≤ (μ2 + 1) * min (μ3 + 1) (n + 3 - μ2) :=
    mul_nonneg (by linarith) (le_min (by linarith) (by linarith))
  have hfrac : (n2 - e12) * min (n2 - e23) e12 / (n2 * (n1 * n2 - e12))
      ≤ (μ2 + 1) * min (μ3 + 1) (n + 3 - μ2) / (n ^ 2 * (n - 1)) :=
    div_le_div₀ hQ0 hprod (by positivity) hbig
  have hdiff : 0 - (μ2 + 1) * min (μ3 + 1) (n + 3 - μ2) / (n ^ 2 * (n - 1))
      ≤ (n3 * (n1 * n2 - e12) - (n1 * e23 - t123)) / (n1 * n2 - e12) - (n3 - e23 / n2) := by
    rw [hid]
    have : -((n2 - e12) * min (n2 - e23) e12) / (n2 * (n1 * n2 - e12))
        ≤ (n2 * t123 - e12 * e23) / (n2 * (n1 * n2 - e12)) :=
      div_le_div_of_nonneg_right hnum hden.le
    rw [neg_div] at this
    linarith
  have hQ : 0 ≤ (μ2 + 1) * min (μ3 + 1) (n + 3 - μ2) / (n ^ 2 * (n - 1)) := by positivity
  have hlog := log_ratio_ge hl0 (by
    rw [le_div_iff₀ hN2p]; nlinarith) hr3hi hrt0 le_rfl hQ hdiff
  have e1 : (0 : ℝ) / (n + 1) - (μ2 + 1) * min (μ3 + 1) (n + 3 - μ2) / (n ^ 2 * (n - 1)) / (n - 1)
      = -((μ2 + 1) * min (μ3 + 1) (n + 3 - μ2) / (n ^ 2 * (n - 1) ^ 2)) := by
    field_simp; ring
  linarith

/-- **Row four, actual side, with the minimum.** -/
theorem rate4_err_emin {n n1 n2 n3 n4 e12 e23 e34 t123 t234 q μ3 μ4 : ℝ} (hn : 5 ≤ n)
    (hn1 : n ≤ n1) (hn1' : n1 ≤ n + 1) (hn2 : n ≤ n2) (hn2' : n2 ≤ n + 1)
    (hn3 : n ≤ n3) (hn3' : n3 ≤ n + 1) (hn4 : n ≤ n4) (hn4' : n4 ≤ n + 1)
    (he12 : 0 ≤ e12) (he12n : e12 ≤ n1) (he23a : 0 ≤ e23) (he23n : e23 ≤ n3) (he34 : 0 ≤ e34)
    (he34n : e34 ≤ n3)
    (ht234 : e23 + e34 - n3 ≤ t234) (ht234' : 0 ≤ t234) (hq : q ≤ t123) (ht0 : 0 ≤ t123)
    (ht1 : t123 ≤ n1)
    (hM30 : 0 ≤ n1 * e23 - t123) (hM3N : n1 * e23 - t123 ≤ n1 * n2 - e12)
    (hM40 : 0 ≤ n1 * (n2 * e34 - t234) - e12 * e34 + q)
    (hM4N : n1 * (n2 * e34 - t234) - e12 * e34 + q
      ≤ n3 * (n1 * n2 - e12) - (n1 * e23 - t123))
    (hd3 : n3 - e23 ≤ μ3 + 1) (hd4 : n3 - e34 ≤ μ4 + 1) (he23μ : e23 ≤ n + 3 - μ3)
    (he34μ : e34 ≤ n + 3 - μ4) (hμ3 : 0 ≤ μ3) (hμ4 : 0 ≤ μ4) (hμ3k : μ3 ≤ n + 1)
    (hμ4k : μ4 ≤ n + 1) :
    -((min ((μ3 + 1) * (μ4 + 1)) ((n + 3 - μ3) * (n + 3 - μ4)) + (μ4 + 1)) / (n * (n - 1) ^ 3))
      ≤ log (((n4 * (n3 * (n1 * n2 - e12) - (n1 * e23 - t123))
              - (n1 * (n2 * e34 - t234) - e12 * e34 + q))
            / (n3 * (n1 * n2 - e12) - (n1 * e23 - t123))) / (n4 - e34 / n3)) := by
  have hn0 : 0 < n := by linarith
  have hl0 : 0 < n - 1 := by linarith
  have hn3p : 0 < n3 := by linarith
  have hn1p : 0 < n1 := by linarith
  have hN2 : n1 * (n2 - 1) ≤ n1 * n2 - e12 := by nlinarith
  have hN3 : (n3 - 1) * (n1 * n2 - e12) ≤ n3 * (n1 * n2 - e12) - (n1 * e23 - t123) := by
    nlinarith
  have hN3big : (n - 1) * (n1 * (n - 1)) ≤ n3 * (n1 * n2 - e12) - (n1 * e23 - t123) := by
    have h1 : n1 * (n - 1) ≤ n1 * (n2 - 1) := mul_le_mul_of_nonneg_left (by linarith) hn1p.le
    have h2 : (n - 1) * (n1 * (n - 1)) ≤ (n3 - 1) * (n1 * n2 - e12) :=
      mul_le_mul (by linarith) (h1.trans hN2) (by positivity) (by linarith)
    linarith
  have hid := rate4_id n1 n2 n3 n4 e12 e23 e34 t123 t234 q hn3p.ne'
    (lt_of_lt_of_le (by positivity) hN3big).ne'
  generalize hN3d : n3 * (n1 * n2 - e12) - (n1 * e23 - t123) = N3 at *
  generalize hM4d : n1 * (n2 * e34 - t234) - e12 * e34 + q = M4 at *
  have hN3p : 0 < N3 := lt_of_lt_of_le (by positivity) hN3big
  have hr4hi : (n4 * N3 - M4) / N3 ≤ n + 1 := by
    rw [div_le_iff₀ hN3p]
    have := mul_le_mul_of_nonneg_right hn4' hN3p.le
    linarith
  have hrt0 : 0 < n4 - e34 / n3 := by
    have : e34 / n3 ≤ 1 := by rw [div_le_one hn3p]; exact he34n
    linarith
  -- the numerator, with the minimum
  have hmin := tri_min' he23a he34 he23n he34n ht234' ht234
  have hnum : -(n1 * min ((n3 - e23) * (n3 - e34)) (e23 * e34) + t123 * (n3 - e34))
      ≤ n1 * (n3 * t234 - e23 * e34) + (e34 * t123 - n3 * q) := by
    have a1 : -(n1 * min ((n3 - e23) * (n3 - e34)) (e23 * e34)) ≤ n1 * (n3 * t234 - e23 * e34) := by
      have := mul_le_mul_of_nonneg_left hmin hn1p.le
      linarith
    have a2 : -(t123 * (n3 - e34)) ≤ e34 * t123 - n3 * q := by nlinarith
    linarith
  have hm0 : 0 ≤ min ((n3 - e23) * (n3 - e34)) (e23 * e34) :=
    le_min (mul_nonneg (by linarith) (by linarith)) (mul_nonneg he23a he34)
  have hmle : min ((n3 - e23) * (n3 - e34)) (e23 * e34)
      ≤ min ((μ3 + 1) * (μ4 + 1)) ((n + 3 - μ3) * (n + 3 - μ4)) :=
    min_le_min (mul_le_mul hd3 hd4 (by linarith) (by linarith))
      (mul_le_mul he23μ he34μ he34 (by linarith))
  have hX0 : 0 ≤ n1 * min ((n3 - e23) * (n3 - e34)) (e23 * e34) + t123 * (n3 - e34) :=
    add_nonneg (mul_nonneg hn1p.le hm0) (mul_nonneg ht0 (by linarith))
  have hX : n1 * min ((n3 - e23) * (n3 - e34)) (e23 * e34) + t123 * (n3 - e34)
      ≤ n1 * (min ((μ3 + 1) * (μ4 + 1)) ((n + 3 - μ3) * (n + 3 - μ4)) + (μ4 + 1)) := by
    have b1 := mul_le_mul_of_nonneg_left hmle hn1p.le
    have b2 : t123 * (n3 - e34) ≤ n1 * (μ4 + 1) :=
      mul_le_mul ht1 hd4 (by linarith) hn1p.le
    nlinarith
  have hden : n * (n - 1) ^ 2 * n1 ≤ n3 * N3 := by
    have := mul_le_mul hn3 hN3big (by positivity) hn3p.le
    have e : n * (n - 1) ^ 2 * n1 = n * ((n - 1) * (n1 * (n - 1))) := by ring
    linarith
  have hfrac : (n1 * min ((n3 - e23) * (n3 - e34)) (e23 * e34) + t123 * (n3 - e34)) / (n3 * N3)
      ≤ n1 * (min ((μ3 + 1) * (μ4 + 1)) ((n + 3 - μ3) * (n + 3 - μ4)) + (μ4 + 1))
        / (n * (n - 1) ^ 2 * n1) :=
    div_le_div₀ (le_trans hX0 hX) hX (by positivity) hden
  have hsimp : n1 * (min ((μ3 + 1) * (μ4 + 1)) ((n + 3 - μ3) * (n + 3 - μ4)) + (μ4 + 1))
        / (n * (n - 1) ^ 2 * n1)
      = (min ((μ3 + 1) * (μ4 + 1)) ((n + 3 - μ3) * (n + 3 - μ4)) + (μ4 + 1)) / (n * (n - 1) ^ 2) := by
    have : n1 ≠ 0 := hn1p.ne'
    field_simp
  have hdiff : 0 - (min ((μ3 + 1) * (μ4 + 1)) ((n + 3 - μ3) * (n + 3 - μ4)) + (μ4 + 1))
        / (n * (n - 1) ^ 2) ≤ (n4 * N3 - M4) / N3 - (n4 - e34 / n3) := by
    rw [hid]
    have : -(n1 * min ((n3 - e23) * (n3 - e34)) (e23 * e34) + t123 * (n3 - e34)) / (n3 * N3)
        ≤ (n1 * (n3 * t234 - e23 * e34) + (e34 * t123 - n3 * q)) / (n3 * N3) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    rw [neg_div] at this
    linarith
  have hmin0 : 0 ≤ min ((μ3 + 1) * (μ4 + 1)) ((n + 3 - μ3) * (n + 3 - μ4)) :=
    le_min (mul_nonneg (by linarith) (by linarith)) (mul_nonneg (by linarith) (by linarith))
  have hQ : 0 ≤ (min ((μ3 + 1) * (μ4 + 1)) ((n + 3 - μ3) * (n + 3 - μ4)) + (μ4 + 1))
      / (n * (n - 1) ^ 2) := div_nonneg (by linarith) (by positivity)
  have hr4lo : n4 - 1 ≤ (n4 * N3 - M4) / N3 := by
    rw [le_div_iff₀ hN3p]; linarith
  have hlog := log_ratio_ge hl0 (le_trans (by linarith) hr4lo) hr4hi hrt0 le_rfl hQ hdiff
  have e1 : (0 : ℝ) / (n + 1) - (min ((μ3 + 1) * (μ4 + 1)) ((n + 3 - μ3) * (n + 3 - μ4)) + (μ4 + 1))
        / (n * (n - 1) ^ 2) / (n - 1)
      = -((min ((μ3 + 1) * (μ4 + 1)) ((n + 3 - μ3) * (n + 3 - μ4)) + (μ4 + 1))
          / (n * (n - 1) ^ 3)) := by
    field_simp; ring
  linarith

/-! ### The rows and the column at `k = 6` -/

/-- **Row three, the error, with the minimum** (`rate3_err_emin`). -/
theorem row3_charge6 {n n1 n2 n3 e12 e23 t123 μ2 μ3 h1 h2 h3 h4 z2 z3 c13 : ℝ} (hn : 5 ≤ n)
    (hh1 : h1 = 0 ∨ h1 = 1) (hh2 : h2 = 0 ∨ h2 = 1) (hh3 : h3 = 0 ∨ h3 = 1) (hh4 : 0 ≤ h4)
    (hn1 : n1 = n + h1) (hn2 : n2 = n + h2) (hn3 : n3 = n + h3)
    (hμ2 : 0 ≤ μ2) (hμ3 : 0 ≤ μ3) (hz2 : 0 ≤ z2) (hz3 : 0 ≤ z3)
    (he12 : e12 = (n - 1 - μ2) + h1 + h2 + z2) (he23 : e23 = (n - 1 - μ3) + h2 + h3 + z3)
    (he12a : 0 ≤ e12) (he12b : e12 ≤ n1) (he12c : e12 ≤ n2)
    (he23a : 0 ≤ e23) (he23b : e23 ≤ n2)
    (ht123 : e12 + e23 - n2 ≤ t123)
    (hM30 : 0 ≤ n1 * e23 - t123) (hM3N : n1 * e23 - t123 ≤ n1 * n2 - e12)
    (hc13 : c13 = 0 ∨ c13 = 1)
    (hZ3 : μ2 = 0 → μ3 = 0 → h1 = 0 → h2 = 0 → h3 = 0 →
      z2 = 0 ∧ z3 = 0 ∧ t123 = n - 2 + c13) (hz2' : z2 ≤ 2) (ht0 : 0 ≤ t123) (hμ2k : μ2 ≤ n + 1) :
    -(J3 μ2 μ3 * ((μ2 + 1) * min (μ3 + 1) (n + 3 - μ2) / (n ^ 2 * (n - 1) ^ 2) + ku3 n * c13))
        - kb3 n * (h1 + h2 + h3 + h4)
      ≤ log (((n3 * (n1 * n2 - e12) - (n1 * e23 - t123)) / (n1 * n2 - e12)) / (n3 - e23 / n2))
        - log (((n * (n ^ 2 - n + 1) - (n * (n - 1) - (n - 2 + c13))) / (n ^ 2 - n + 1))
          / ((n ^ 2 - n + 1) / n)) := by
  by_cases hJ : μ2 + μ3 = 0
  · have h := row3_charge hn hh1 hh2 hh3 hh4 hn1 hn2 hn3 hμ2 hμ3 hz2 hz3 he12 he23 he12a he12b
      he12c he23a he23b ht123 hM30 hM3N hc13 hZ3
    simp only [J3, hJ, ite_true, zero_mul, neg_zero, zero_sub] at h ⊢
    exact h
  have hn0 : 0 < n := by linarith
  have hb1 : 0 ≤ h1 ∧ h1 ≤ 1 := by rcases hh1 with rfl | rfl <;> norm_num
  have hb2 : 0 ≤ h2 ∧ h2 ≤ 1 := by rcases hh2 with rfl | rfl <;> norm_num
  have hb3 : 0 ≤ h3 ∧ h3 ≤ 1 := by rcases hh3 with rfl | rfl <;> norm_num
  have herr := rate3_err_emin (n1 := n1) (n2 := n2) (n3 := n3) (e12 := e12) (e23 := e23)
    (t123 := t123) hn (by rw [hn1]; linarith) (by rw [hn1]; linarith)
    (by rw [hn2]; linarith) (by rw [hn2]; linarith) (by rw [hn3]; linarith)
    (by rw [hn3]; linarith) he12a he12b he12c he23a he23b ht123 ht0 hM30 hM3N
    (μ2 := μ2) (μ3 := μ3) (by rw [hn2, he12]; linarith) (by rw [hn2, he23]; linarith)
    (by rw [he12]; linarith) hμ2 hμ3 hμ2k
  have hunif := rate3_unif hn hc13
  have eku : (n - 1) / (n ^ 2 * ((n ^ 2 - n + 1) / n) ^ 2) * c13 = ku3 n * c13 := by
    unfold ku3 kt kA; ring
  rw [eku] at hunif
  have hkb3 : kb3 n = 1 / (n ^ 2 * (n - 1) ^ 2) + ku3 n := rfl
  have hku : 0 ≤ ku3 n := by
    unfold ku3 kt kA; have : 0 < n ^ 2 - n + 1 := by nlinarith
    exact div_nonneg (by linarith) (by positivity)
  simp only [J3, hJ, ite_false, one_mul]
  have hkb0 : 0 ≤ kb3 n := by
    rw [hkb3]; have : 0 ≤ 1 / (n ^ 2 * (n - 1) ^ 2) := by positivity
    linarith
  have : 0 ≤ kb3 n * (h1 + h2 + h3 + h4) := mul_nonneg hkb0 (by linarith)
  linarith

set_option maxHeartbeats 2000000 in
/-- **Row four, the error, with the minimum** (`rate4_err_emin`). -/
theorem row4_charge6 {k : ℕ} (hk6 : 6 ≤ k) (hkle : k ≤ 7) {n : ℝ} (hnk : n = (k : ℝ) - 1)
    {n1 n2 n3 n4 e12 e23 e34 t123 t234 q h1 h2 h3 h4 μ2 μ3 μ4 z2 z3 z4 c13 c24 c14 : ℝ}
    (hh1 : h1 = 0 ∨ h1 = 1) (hh2 : h2 = 0 ∨ h2 = 1) (hh3 : h3 = 0 ∨ h3 = 1) (hh4 : h4 = 0 ∨ h4 = 1)
    (hn1 : n1 = n + h1) (hn2 : n2 = n + h2) (hn3 : n3 = n + h3) (hn4 : n4 = n + h4)
    (hμ2 : 0 ≤ μ2) (hμ3 : 0 ≤ μ3) (hμ4 : 0 ≤ μ4) (hz3 : 0 ≤ z3) (hz4 : 0 ≤ z4)
    (he12 : e12 = (n - 1 - μ2) + h1 + h2 + z2) (he23 : e23 = (n - 1 - μ3) + h2 + h3 + z3)
    (he34 : e34 = (n - 1 - μ4) + h3 + h4 + z4)
    (he12a : 0 ≤ e12) (he12b : e12 ≤ n1) (he23c : e23 ≤ n3)
    (he34a : 0 ≤ e34) (he34b : e34 ≤ n3)
    (ht0 : 0 ≤ t123) (ht1 : t123 ≤ n1) (ht234 : e23 + e34 - n3 ≤ t234) (hq : q ≤ t123)
    (hM30 : 0 ≤ n1 * e23 - t123) (hM3N : n1 * e23 - t123 ≤ n1 * n2 - e12)
    (hM40 : 0 ≤ n1 * (n2 * e34 - t234) - e12 * e34 + q)
    (hM4N : n1 * (n2 * e34 - t234) - e12 * e34 + q ≤ n3 * (n1 * n2 - e12) - (n1 * e23 - t123))
    (hc13 : c13 = 0 ∨ c13 = 1) (hc24 : c24 = 0 ∨ c24 = 1) (hc14 : c14 = 0 ∨ c14 = 1)
    (h1314 : c13 * c14 = 0) (h2414 : c24 * c14 = 0)
    (hZ4 : μ2 = 0 → μ3 = 0 → μ4 = 0 → h2 = 0 → h3 = 0 → h4 = 0 →
      z2 = 0 ∧ z3 = 0 ∧ z4 = 0 ∧ t234 = n - 2 + c24 ∧
      (h1 = 0 → t123 = n - 2 + c13 ∧ q = n - 3 + c13 + c24 + c14) ∧
      (h1 = 1 → t123 = n - 1 ∧ q = t234 ∧ c13 = 0 ∧ c14 = 0))
    (hz3' : z3 ≤ 2) (hz4' : z4 ≤ 2) (ht234' : 0 ≤ t234) (hμ3k : μ3 ≤ n + 1) (hμ4k : μ4 ≤ n + 1)
    (he23a : 0 ≤ e23) :
    -(J4 μ2 μ3 μ4 * ((min ((μ3 + 1) * (μ4 + 1)) ((n + 3 - μ3) * (n + 3 - μ4)) + (μ4 + 1))
        / (n * (n - 1) ^ 3) + ku4e n * c24 + ku4b n))
        - kb4 n * (h1 + h2 + h3 + h4)
      ≤ log (rate4 n1 n2 n3 n4 e12 e23 e34 t123 t234 q / (n4 - e34 / n3))
        - log (r4U n c13 c24 c14 / ((n ^ 2 - n + 1) / n)) := by
  by_cases hJ : μ2 + μ3 + μ4 = 0
  · have h := row4_charge hk6 hkle hnk hh1 hh2 hh3 hh4 hn1 hn2 hn3 hn4 hμ2 hμ3 hμ4 hz3 hz4
      he12 he23 he34 he12a he12b he23c he34a he34b ht0 ht1 ht234 hq hM30 hM3N hM40 hM4N
      hc13 hc24 hc14 h1314 h2414 hZ4
    simp only [J4, hJ, ite_true, zero_mul, neg_zero, zero_sub] at h ⊢
    exact h
  have hk6' : (6 : ℝ) ≤ k := by exact_mod_cast hk6
  have hn : 5 ≤ n := by rw [hnk]; linarith
  have hn0 : 0 < n := by linarith
  have hl0 : 0 < n - 1 := by linarith
  have hb1 : 0 ≤ h1 ∧ h1 ≤ 1 := by rcases hh1 with rfl | rfl <;> norm_num
  have hb2 : 0 ≤ h2 ∧ h2 ≤ 1 := by rcases hh2 with rfl | rfl <;> norm_num
  have hb3 : 0 ≤ h3 ∧ h3 ≤ 1 := by rcases hh3 with rfl | rfl <;> norm_num
  have hb4 : 0 ≤ h4 ∧ h4 ≤ 1 := by rcases hh4 with rfl | rfl <;> norm_num
  have herr := rate4_err_emin (n1 := n1) (n2 := n2) (n3 := n3) (n4 := n4) (e12 := e12)
    (e23 := e23) (e34 := e34) (t123 := t123) (t234 := t234) (q := q) (μ3 := μ3) (μ4 := μ4) hn
    (by rw [hn1]; linarith) (by rw [hn1]; linarith) (by rw [hn2]; linarith) (by rw [hn2]; linarith)
    (by rw [hn3]; linarith) (by rw [hn3]; linarith) (by rw [hn4]; linarith) (by rw [hn4]; linarith)
    he12a he12b he23a he23c he34a he34b ht234 ht234' hq ht0 ht1 hM30 hM3N
    hM40 hM4N (by rw [hn3, he23]; linarith) (by rw [hn3, he34]; linarith)
    (by rw [he23]; linarith) (by rw [he34]; linarith) hμ3 hμ4 hμ3k hμ4k
  have herr' : -((min ((μ3 + 1) * (μ4 + 1)) ((n + 3 - μ3) * (n + 3 - μ4)) + (μ4 + 1))
        / (n * (n - 1) ^ 3))
      ≤ log (rate4 n1 n2 n3 n4 e12 e23 e34 t123 t234 q / (n4 - e34 / n3)) := herr
  clear herr
  have e1 : (k : ℝ) - 1 = n := by rw [hnk]
  have e2 : (k : ℝ) - 2 = n - 1 := by rw [hnk]; ring
  have hunif := rate4_unif hk6 hkle hc13 hc24 hc14 h1314 h2414
  rw [e1, e2] at hunif
  have eku : c24 / ((n - 1) ^ 2 * ((n ^ 2 - n + 1) / n))
      + 1 / (n * ((n ^ 2 - n + 1) / n) ^ 2 * (n - 1)) = ku4e n * c24 + ku4b n := by
    unfold ku4e ku4b kt kA; ring
  rw [eku] at hunif
  have ht : 0 < (n ^ 2 - n + 1) / n := div_pos (by clear * - hn; nlinarith) hn0
  have hku4e : 0 ≤ ku4e n := by
    unfold ku4e kt kA; exact (one_div_pos.mpr (mul_pos (by positivity) ht)).le
  have hku4b : 0 ≤ ku4b n := by
    unfold ku4b kt kA; exact (one_div_pos.mpr (mul_pos (mul_pos hn0 (pow_pos ht 2)) hl0)).le
  have hkb4 : kb4 n = 2 / (n * (n - 1) ^ 3) + ku4e n + ku4b n := rfl
  have h2p : 0 ≤ 2 / (n * (n - 1) ^ 3) :=
    div_nonneg zero_le_two (mul_pos hn0 (pow_pos hl0 3)).le
  have hkb4p : 0 ≤ kb4 n := by rw [hkb4]; exact add_nonneg (add_nonneg h2p hku4e) hku4b
  simp only [J4, hJ, ite_false, one_mul]
  have : 0 ≤ kb4 n * (h1 + h2 + h3 + h4) := mul_nonneg hkb4p (by linarith)
  linarith

/-- **The count bound at `k = 6`**: `countBound` with the chord costs `zslope` and the
minimum errors. -/
noncomputable def countBound6 (n μ2 μ3 μ4 z2 z3 z4 h1 h2 h3 h4 c13 c24 : ℝ) : ℝ :=
  log (1 + μ2 / kA n) + log (1 + μ3 / kA n) + log (1 + μ4 / kA n)
    - (z2 * zslope n μ2 + z3 * zslope n μ3 + z4 * zslope n μ4)
    - J3 μ2 μ3 * ((μ2 + 1) * min (μ3 + 1) (n + 3 - μ2) / (n ^ 2 * (n - 1) ^ 2) + ku3 n * c13)
    - J4 μ2 μ3 μ4 * ((min ((μ3 + 1) * (μ4 + 1)) ((n + 3 - μ3) * (n + 3 - μ4)) + (μ4 + 1))
        / (n * (n - 1) ^ 3) + ku4e n * c24 + ku4b n)
    + (kβ0 n - kb3 n - kb4 n) * (h1 + h2 + h3 + h4)

/-- **The log count ratio of one column, at `k = 6` precision.** -/
theorem count_log_bound6 {k : ℕ} (hk6 : 6 ≤ k) (hkle : k ≤ 7) {n : ℝ} (hnk : n = (k : ℝ) - 1)
    {n1 n2 n3 n4 e12 e23 e34 t123 t234 q h1 h2 h3 h4 μ2 μ3 μ4 z2 z3 z4 c13 c24 c14 : ℝ}
    (hh1 : h1 = 0 ∨ h1 = 1) (hh2 : h2 = 0 ∨ h2 = 1) (hh3 : h3 = 0 ∨ h3 = 1) (hh4 : h4 = 0 ∨ h4 = 1)
    (hn1 : n1 = n + h1) (hn2 : n2 = n + h2) (hn3 : n3 = n + h3) (hn4 : n4 = n + h4)
    (hμ2 : 0 ≤ μ2) (hμ3 : 0 ≤ μ3) (hμ4 : 0 ≤ μ4)
    (hμ2k : μ2 ≤ n + 1) (hμ3k : μ3 ≤ n + 1) (hμ4k : μ4 ≤ n + 1)
    (hz2 : 0 ≤ z2) (hz3 : 0 ≤ z3) (hz4 : 0 ≤ z4)
    (he12 : e12 = (n - 1 - μ2) + h1 + h2 + z2) (he23 : e23 = (n - 1 - μ3) + h2 + h3 + z3)
    (he34 : e34 = (n - 1 - μ4) + h3 + h4 + z4)
    (he12a : 0 ≤ e12) (he12b : e12 ≤ n1) (he12c : e12 ≤ n2)
    (he23a : 0 ≤ e23) (he23b : e23 ≤ n2) (he23c : e23 ≤ n3)
    (he34a : 0 ≤ e34) (he34b : e34 ≤ n3)
    (ht123 : e12 + e23 - n2 ≤ t123) (ht0 : 0 ≤ t123) (ht1 : t123 ≤ n1)
    (ht234 : e23 + e34 - n3 ≤ t234) (hq : q ≤ t123)
    (hM30 : 0 ≤ n1 * e23 - t123) (hM3N : n1 * e23 - t123 ≤ n1 * n2 - e12)
    (hM40 : 0 ≤ n1 * (n2 * e34 - t234) - e12 * e34 + q)
    (hM4N : n1 * (n2 * e34 - t234) - e12 * e34 + q ≤ n3 * (n1 * n2 - e12) - (n1 * e23 - t123))
    (hc13 : c13 = 0 ∨ c13 = 1) (hc24 : c24 = 0 ∨ c24 = 1) (hc14 : c14 = 0 ∨ c14 = 1)
    (h1314 : c13 * c14 = 0) (h2414 : c24 * c14 = 0)
    (hZ3 : μ2 = 0 → μ3 = 0 → h1 = 0 → h2 = 0 → h3 = 0 →
      z2 = 0 ∧ z3 = 0 ∧ t123 = n - 2 + c13)
    (hZ4 : μ2 = 0 → μ3 = 0 → μ4 = 0 → h2 = 0 → h3 = 0 → h4 = 0 →
      z2 = 0 ∧ z3 = 0 ∧ z4 = 0 ∧ t234 = n - 2 + c24 ∧
      (h1 = 0 → t123 = n - 2 + c13 ∧ q = n - 3 + c13 + c24 + c14) ∧
      (h1 = 1 → t123 = n - 1 ∧ q = t234 ∧ c13 = 0 ∧ c14 = 0))
    (hz2' : z2 ≤ 2) (hz3' : z3 ≤ 2) (hz4' : z4 ≤ 2) (ht234' : 0 ≤ t234) :
    countBound6 n μ2 μ3 μ4 z2 z3 z4 h1 h2 h3 h4 c13 c24
      ≤ log (N4 n1 n2 n3 n4 e12 e23 e34 t123 t234 q / N4U n c13 c24 c14) := by
  have hk6' : (6 : ℝ) ≤ k := by exact_mod_cast hk6
  have hn : 5 ≤ n := by rw [hnk]; linarith
  have hn0 : 0 < n := by linarith
  have hh1' : 0 ≤ h1 ∧ h1 ≤ 1 := by rcases hh1 with rfl | rfl <;> norm_num
  have hh2' : 0 ≤ h2 ∧ h2 ≤ 1 := by rcases hh2 with rfl | rfl <;> norm_num
  have hh3' : 0 ≤ h3 ∧ h3 ≤ 1 := by rcases hh3 with rfl | rfl <;> norm_num
  have hh4' : 0 ≤ h4 ∧ h4 ≤ 1 := by rcases hh4 with rfl | rfl <;> norm_num
  have hn1p : 0 < n1 := by rw [hn1]; linarith
  have hn2p : 0 < n2 := by rw [hn2]; linarith
  have hn3p : 0 < n3 := by rw [hn3]; linarith
  have hn4p : 5 ≤ n4 := by rw [hn4]; linarith
  -- positivity of all counts
  obtain ⟨hN2, hN3, hN4⟩ := counts_pos (n1 := n1) (n2 := n2) (n3 := n3) (n4 := n4) hn
    (by rw [hn1]; linarith) (by rw [hn2]; linarith) (by rw [hn3]; linarith)
    (by rw [hn4]; linarith) he12b hM3N hM4N
  have hN2U : 0 < n ^ 2 - n + 1 := by nlinarith
  have hN3U := N3U_pos hn hc13
  have hN4U := N4U_pos hn hc13 hc24 hc14 h1314 h2414
  have ht : 0 < (n ^ 2 - n + 1) / n := div_pos hN2U hn0
  -- the four row logs
  have hsplit := log_count_split (n := n) (n1 := n1) (N2 := n1 * n2 - e12)
    (N3 := n3 * (n1 * n2 - e12) - (n1 * e23 - t123))
    (N4 := N4 n1 n2 n3 n4 e12 e23 e34 t123 t234 q) (N2U := n ^ 2 - n + 1)
    (N3U := n * (n ^ 2 - n + 1) - (n * (n - 1) - (n - 2 + c13))) (N4U := N4U n c13 c24 c14)
    hn0 hn1p hN2 hN3 hN4 hN2U hN3U hN4U
  -- row one
  have hL1 := rate_first hn hh1
  rw [← hn1] at hL1
  -- row two
  have hL2 := rate_main_chord hn hh1 hh2 hz2 hz2' hμ2 hμ2k he12 he12a (by rw [← hn1]; exact he12b)
  have eR2 : (n1 * n2 - e12) / n1 / ((n ^ 2 - n + 1) / n)
      = ((n + h2) - e12 / (n + h1)) / ((n ^ 2 - n + 1) / n) := by
    rw [← hn1, ← hn2]
    congr 1; field_simp
  rw [← eR2] at hL2
  -- row three
  have hR3 : 0 < n3 - e23 / n2 := by
    have : e23 / n2 ≤ 1 := by rw [div_le_one hn2p]; exact he23b
    linarith
  have hs3 := log_split (a := (n3 * (n1 * n2 - e12) - (n1 * e23 - t123)) / (n1 * n2 - e12))
    (b := (n * (n ^ 2 - n + 1) - (n * (n - 1) - (n - 2 + c13))) / (n ^ 2 - n + 1))
    (div_pos hN3 hN2) (div_pos hN3U hN2U) hR3 ht
  have hm3 := rate_main_chord hn hh2 hh3 hz3 hz3' hμ3 hμ3k he23 he23a (by rw [← hn2]; exact he23b)
  rw [← hn2, ← hn3] at hm3
  have hE3 := row3_charge6 hn hh1 hh2 hh3 hh4'.1 hn1 hn2 hn3 hμ2 hμ3 hz2 hz3 he12 he23 he12a he12b
    he12c he23a he23b ht123 hM30 hM3N hc13 hZ3 hz2' ht0 hμ2k
  -- row four
  have hR4 : 0 < n4 - e34 / n3 := by
    have : e34 / n3 ≤ 1 := by rw [div_le_one hn3p]; exact he34b
    linarith
  have hr4 : 0 < rate4 n1 n2 n3 n4 e12 e23 e34 t123 t234 q := by
    unfold rate4; exact div_pos hN4 hN3
  have hr4U : 0 < r4U n c13 c24 c14 := by
    have : r4U n c13 c24 c14 = N4U n c13 c24 c14 / (n * (n ^ 2 - n + 1) - (n * (n - 1) - (n - 2 + c13))) := by
      unfold r4U rate4 N4U N4; ring
    rw [this]; exact div_pos hN4U hN3U
  have hs4 := log_split hr4 hr4U hR4 ht
  have e4 : N4 n1 n2 n3 n4 e12 e23 e34 t123 t234 q / (n3 * (n1 * n2 - e12) - (n1 * e23 - t123))
      = rate4 n1 n2 n3 n4 e12 e23 e34 t123 t234 q := by unfold rate4 N4; rfl
  have e4U : N4U n c13 c24 c14 / (n * (n ^ 2 - n + 1) - (n * (n - 1) - (n - 2 + c13)))
      = r4U n c13 c24 c14 := by unfold r4U rate4 N4U N4; ring
  rw [e4, e4U] at hsplit
  have hm4 := rate_main_chord hn hh3 hh4 hz4 hz4' hμ4 hμ4k he34 he34a (by rw [← hn3]; exact he34b)
  rw [← hn3, ← hn4] at hm4
  have hE4 := row4_charge6 hk6 hkle hnk hh1 hh2 hh3 hh4 hn1 hn2 hn3 hn4 hμ2 hμ3 hμ4 hz3 hz4
    he12 he23 he34 he12a he12b he23c he34a he34b ht0 ht1 ht234 hq hM30 hM3N hM40 hM4N
    hc13 hc24 hc14 h1314 h2414 hZ4 hz3' hz4' ht234' hμ3k hμ4k he23a
  have hbon := bonus_sum hn hh1'.1 hh2'.1 hh3'.1 hh4'.1 hμ2k hμ3k hμ4k
  unfold countBound6 kA
  linarith

end GridGen.Four
