/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Height four: the logarithmic rate bounds, as real inequalities

The successor count of a column factors into four row rates (`GridGen/Four/Rates.lean`). This file
proves the per-row lower bounds on the logarithms of those rates against their uniform values,
as statements about real numbers satisfying the counting constraints; no colourings appear here.

Notation: `n = k - 1`, `ℓ = k - 2`, `A = ℓ² + ℓ + 1 = n² - ℓ`, `t = A / n` (the uniform rate of rows
2 to 4 when the previous row is ignored). For a row, `h` is the bonus indicator (its state colour is
missing from its list), `μ` the number of colours its list does not share with the previous list,
and `z ∈ {0, 1, 2}` counts state colours lying in the two difference sets.
-/

namespace GridGen.Four

open Real

/-- **The log comparison.** If `x - y ≥ P - Q` with `x, y` in `[ℓ, K]`, then
`log (x / y) ≥ P / K - Q / ℓ`. -/
theorem log_ratio_ge {x y l K P Q : ℝ} (hl : 0 < l) (hlx : l ≤ x) (hxK : x ≤ K) (hy : 0 < y)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (h : P - Q ≤ x - y) : P / K - Q / l ≤ log (x / y) := by
  have hx : 0 < x := lt_of_lt_of_le hl hlx
  have hK : 0 < K := lt_of_lt_of_le hx hxK
  have hlog : 1 - y / x ≤ log (x / y) := by
    have := Real.one_sub_inv_le_log_of_pos (div_pos hx hy)
    rwa [inv_div] at this
  refine le_trans ?_ hlog
  have hyx : 1 - y / x = (x - y) / x := by field_simp
  rw [hyx]
  rcases le_or_gt y x with hxy | hxy
  · -- nonnegative difference: divide by the larger `K`
    have h1 : (x - y) / K ≤ (x - y) / x :=
      div_le_div_of_nonneg_left (by linarith) hx hxK
    have h2 : P / K - Q / l ≤ (P - Q) / K := by
      rw [sub_div]
      have : Q / K ≤ Q / l := div_le_div_of_nonneg_left hQ hl (by linarith)
      linarith
    have h3 : (P - Q) / K ≤ (x - y) / K := div_le_div_of_nonneg_right h hK.le
    linarith
  · -- negative difference: divide by the smaller `ℓ`
    have h1 : (x - y) / l ≤ (x - y) / x := by
      rw [div_le_div_iff₀ hl hx]
      nlinarith
    have h2 : P / K - Q / l ≤ (P - Q) / l := by
      rw [sub_div]
      have : P / K ≤ P / l := div_le_div_of_nonneg_left hP hl (by linarith)
      linarith
    have h3 : (P - Q) / l ≤ (x - y) / l := div_le_div_of_nonneg_right h hl.le
    linarith

/-- `log (1 + x) ≥ x - x²/2` for `x ≥ 0` (from Mathlib's `2x/(x+2) ≤ log (1 + x)`). -/
theorem log_one_add_ge {x : ℝ} (hx : 0 ≤ x) : x - x ^ 2 / 2 ≤ log (1 + x) := by
  refine le_trans ?_ (Real.le_log_one_add_of_nonneg hx)
  rw [le_div_iff₀ (by linarith)]
  nlinarith [pow_nonneg hx 3]

/-! ### The main term of one row

From here on the base variable is `n = k - 1` (so `ℓ = n - 1`, `k = n + 1`), with
`A = n² - n + 1 = ℓ² + ℓ + 1` and `t = A / n`. -/

/-- **One row, main term.** If the previous row has bonus `h₀`, this row bonus `h₁`, list
mismatch `μ` and `z` state colours in the difference sets, the punctured intersection has
`e = (n - 1 - μ) + h₀ + h₁ + z` colours, and the uniform-on-list rate
`r̃ = (n + h₁) - e/(n + h₀)` satisfies
`log (r̃ / t) ≥ log (1 + μ/A) + ((n-1)/n) h₁/(n+1) - z/(n(n-1)) - (μ+1) h₀/(n(n+1)(n-1))`. -/
theorem rate_main {n h0 h1 z μ e : ℝ} (hn : 6 ≤ n) (hh0 : h0 = 0 ∨ h0 = 1)
    (hh1 : h1 = 0 ∨ h1 = 1) (hz : 0 ≤ z) (hμ : 0 ≤ μ) (hμk : μ ≤ n + 1)
    (he : e = (n - 1 - μ) + h0 + h1 + z) (he0 : 0 ≤ e) (heN : e ≤ n + h0) :
    log (1 + μ / (n ^ 2 - n + 1)) + ((n - 1) / n) * h1 / (n + 1)
        - z / (n * (n - 1)) - (μ + 1) * h0 / (n * (n + 1) * (n - 1))
      ≤ log (((n + h1) - e / (n + h0)) / ((n ^ 2 - n + 1) / n)) := by
  have hn0 : 0 < n := by linarith
  have hl0 : 0 < n - 1 := by linarith
  have hA0 : 0 < n ^ 2 - n + 1 := by nlinarith
  have hnne : n ≠ 0 := hn0.ne'
  have hn1ne : n + 1 ≠ 0 := by linarith
  have hlne : n - 1 ≠ 0 := hl0.ne'
  have hden : 0 < n + h0 := by rcases hh0 with rfl | rfl <;> linarith
  have ht0 : 0 < (n ^ 2 - n + 1) / n := div_pos hA0 hn0
  have hr0 : 0 < (n ^ 2 - n + 1) / n + μ / n := by positivity
  -- the rate lies in `[n - 1, n + 1]`
  have hq : e / (n + h0) ≤ 1 := by rw [div_le_one hden]; exact heN
  have hq0 : 0 ≤ e / (n + h0) := div_nonneg he0 hden.le
  have hlo : n - 1 ≤ (n + h1) - e / (n + h0) := by
    rcases hh1 with rfl | rfl <;> linarith
  have hhi : (n + h1) - e / (n + h0) ≤ n + 1 := by
    rcases hh1 with rfl | rfl <;> linarith
  -- the comparison with `r₀ = t + μ/n`
  have hdiff : ((n - 1) / n) * h1 - (z / n + (μ + 1) * h0 / (n * (n + 1)))
      ≤ ((n + h1) - e / (n + h0)) - ((n ^ 2 - n + 1) / n + μ / n) := by
    rw [he]
    rcases hh0 with rfl | rfl
    · have key : (n + h1) - (n - 1 - μ + 0 + h1 + z) / (n + 0) - ((n ^ 2 - n + 1) / n + μ / n)
          = ((n - 1) / n) * h1 - z / n := by
        field_simp; ring
      rw [key]; simp
    · have key : (n + h1) - (n - 1 - μ + 1 + h1 + z) / (n + 1) - ((n ^ 2 - n + 1) / n + μ / n)
          = h1 * (n / (n + 1)) - z / (n + 1) - (1 + μ) / (n * (n + 1)) := by
        field_simp; ring
      rw [key]
      have c1 : ((n - 1) / n) * h1 ≤ h1 * (n / (n + 1)) := by
        rcases hh1 with rfl | rfl
        · simp
        · rw [mul_one, one_mul, div_le_div_iff₀ hn0 (by linarith)]; nlinarith
      have c2 : z / (n + 1) ≤ z / n := div_le_div_of_nonneg_left hz hn0 (by linarith)
      have c3 : (μ + 1) * 1 / (n * (n + 1)) = (1 + μ) / (n * (n + 1)) := by ring
      linarith
  have hP : 0 ≤ ((n - 1) / n) * h1 := by rcases hh1 with rfl | rfl <;> positivity
  have hh0nn : 0 ≤ h0 := by rcases hh0 with rfl | rfl <;> norm_num
  have hQ : 0 ≤ z / n + (μ + 1) * h0 / (n * (n + 1)) := by positivity
  have hlog := log_ratio_ge hl0 hlo hhi hr0 hP hQ hdiff
  -- split `log (r̃ / t) = log (r₀ / t) + log (r̃ / r₀)`
  have hrpos : 0 < (n + h1) - e / (n + h0) := by linarith
  have hsplit : log (((n + h1) - e / (n + h0)) / ((n ^ 2 - n + 1) / n))
      = log (((n ^ 2 - n + 1) / n + μ / n) / ((n ^ 2 - n + 1) / n))
        + log (((n + h1) - e / (n + h0)) / ((n ^ 2 - n + 1) / n + μ / n)) := by
    rw [← Real.log_mul (div_pos hr0 ht0).ne' (div_pos hrpos hr0).ne']
    congr 1; field_simp
  have hr0t : ((n ^ 2 - n + 1) / n + μ / n) / ((n ^ 2 - n + 1) / n) = 1 + μ / (n ^ 2 - n + 1) := by
    field_simp
  rw [hsplit, hr0t]
  have e1 : ((n - 1) / n) * h1 / (n + 1) - (z / n + (μ + 1) * h0 / (n * (n + 1))) / (n - 1)
      = ((n - 1) / n) * h1 / (n + 1) - z / (n * (n - 1)) - (μ + 1) * h0 / (n * (n + 1) * (n - 1)) := by
    field_simp; ring
  rw [e1] at hlog
  linarith

/-- **Row one.** `log ((n + h₁)/n) ≥ ((n-1)/n) h₁ / (n+1)`. -/
theorem rate_first {n h1 : ℝ} (hn : 6 ≤ n) (hh1 : h1 = 0 ∨ h1 = 1) :
    ((n - 1) / n) * h1 / (n + 1) ≤ log ((n + h1) / n) := by
  have hn0 : 0 < n := by linarith
  rcases hh1 with rfl | rfl
  · simp
  · have hpos : 0 < (n + 1) / n := by positivity
    refine le_trans ?_ (Real.one_sub_inv_le_log_of_pos hpos)
    rw [inv_div, mul_one]
    rw [show 1 - n / (n + 1) = 1 / (n + 1) by field_simp; ring]
    apply div_le_div_of_nonneg_right _ (by linarith)
    rw [div_le_one hn0]; linarith

/-! ### The third row: the deviation of the actual rate -/

/-- **Row three, actual side.** With `N₂ = n₁n₂ - e₁₂` and `M₃ = n₁e₂₃ - t₁₂₃ ∈ [0, N₂]`, the rate
`r₃ = (n₃N₂ - M₃)/N₂` is within `(μ₂+1)(μ₃+1)/(n²(n-1)²)` (in log) below
`r̃₃ = n₃ - e₂₃/n₂`. -/
theorem rate3_err {n n1 n2 n3 e12 e23 t123 μ2 μ3 : ℝ} (hn : 6 ≤ n)
    (hn1 : n ≤ n1) (hn1' : n1 ≤ n + 1) (hn2 : n ≤ n2) (hn2' : n2 ≤ n + 1)
    (hn3 : n ≤ n3) (hn3' : n3 ≤ n + 1)
    (he12 : 0 ≤ e12) (he12n : e12 ≤ n1) (he12m : e12 ≤ n2) (he23 : 0 ≤ e23) (he23n : e23 ≤ n2)
    (ht : e12 + e23 - n2 ≤ t123) (hM0 : 0 ≤ n1 * e23 - t123)
    (hMN : n1 * e23 - t123 ≤ n1 * n2 - e12)
    (hd2 : n2 - e12 ≤ μ2 + 1) (hd3 : n2 - e23 ≤ μ3 + 1) (hμ2 : 0 ≤ μ2) (hμ3 : 0 ≤ μ3) :
    -((μ2 + 1) * (μ3 + 1) / (n ^ 2 * (n - 1) ^ 2))
      ≤ log (((n3 * (n1 * n2 - e12) - (n1 * e23 - t123)) / (n1 * n2 - e12)) / (n3 - e23 / n2)) := by
  have hn0 : 0 < n := by linarith
  have hl0 : 0 < n - 1 := by linarith
  have hn2p : 0 < n2 := by linarith
  have hn2ne : n2 ≠ 0 := hn2p.ne'
  have hN2 : n * (n - 1) ≤ n1 * n2 - e12 := by nlinarith
  have hN2p : 0 < n1 * n2 - e12 := by nlinarith
  have hN2ne : n1 * n2 - e12 ≠ 0 := hN2p.ne'
  have hr3lo : n3 - 1 ≤ (n3 * (n1 * n2 - e12) - (n1 * e23 - t123)) / (n1 * n2 - e12) := by
    rw [le_div_iff₀ hN2p]; nlinarith
  have hr3hi : (n3 * (n1 * n2 - e12) - (n1 * e23 - t123)) / (n1 * n2 - e12) ≤ n + 1 := by
    rw [div_le_iff₀ hN2p]; nlinarith
  have hrt0 : 0 < n3 - e23 / n2 := by
    have : e23 / n2 ≤ 1 := by rw [div_le_one hn2p]; exact he23n
    linarith
  -- the exact deviation and its lower bound
  have hid : (n3 * (n1 * n2 - e12) - (n1 * e23 - t123)) / (n1 * n2 - e12) - (n3 - e23 / n2)
      = (n2 * t123 - e12 * e23) / (n2 * (n1 * n2 - e12)) := by
    field_simp; ring
  have hden : 0 < n2 * (n1 * n2 - e12) := by positivity
  have hnum : -((n2 - e12) * (n2 - e23)) ≤ n2 * t123 - e12 * e23 := by nlinarith
  have h1 : 0 ≤ n2 - e12 := by linarith
  have h2 : 0 ≤ n2 - e23 := by linarith
  have hprod : (n2 - e12) * (n2 - e23) ≤ (μ2 + 1) * (μ3 + 1) :=
    mul_le_mul hd2 hd3 h2 (by linarith)
  have hbig : n ^ 2 * (n - 1) ≤ n2 * (n1 * n2 - e12) := by
    have : n * n * (n - 1) ≤ n2 * (n1 * n2 - e12) :=
      mul_le_mul hn2 hN2 (by positivity) (by linarith) |>.trans_eq' (by ring)
    nlinarith
  have hfrac : (n2 - e12) * (n2 - e23) / (n2 * (n1 * n2 - e12))
      ≤ (μ2 + 1) * (μ3 + 1) / (n ^ 2 * (n - 1)) :=
    div_le_div₀ (by positivity) hprod (by positivity) hbig
  have hdiff : 0 - (μ2 + 1) * (μ3 + 1) / (n ^ 2 * (n - 1))
      ≤ (n3 * (n1 * n2 - e12) - (n1 * e23 - t123)) / (n1 * n2 - e12) - (n3 - e23 / n2) := by
    rw [hid]
    have : -((n2 - e12) * (n2 - e23)) / (n2 * (n1 * n2 - e12))
        ≤ (n2 * t123 - e12 * e23) / (n2 * (n1 * n2 - e12)) :=
      div_le_div_of_nonneg_right hnum hden.le
    rw [neg_div] at this
    linarith
  have hQ : 0 ≤ (μ2 + 1) * (μ3 + 1) / (n ^ 2 * (n - 1)) := by positivity
  have hlog := log_ratio_ge hl0 (by linarith) hr3hi hrt0 le_rfl hQ hdiff
  have e1 : (0 : ℝ) / (n + 1) - (μ2 + 1) * (μ3 + 1) / (n ^ 2 * (n - 1)) / (n - 1)
      = -((μ2 + 1) * (μ3 + 1) / (n ^ 2 * (n - 1) ^ 2)) := by
    field_simp; ring
  linarith

/-- **Row three, uniform side.** For the uniform column the deviation is `-1/(nA)` or, when rows 1
and 3 share a colour (`c = 1`), `(n-1)/(nA)`; in log against `t` it is at most
`(n-1)/(n²t²)·c`. -/
theorem rate3_unif {n c : ℝ} (hn : 6 ≤ n) (hc : c = 0 ∨ c = 1) :
    log (((n * (n ^ 2 - n + 1) - (n * (n - 1) - (n - 2 + c))) / (n ^ 2 - n + 1))
        / ((n ^ 2 - n + 1) / n))
      ≤ (n - 1) / (n ^ 2 * ((n ^ 2 - n + 1) / n) ^ 2) * c := by
  have hn0 : 0 < n := by linarith
  have hA0 : 0 < n ^ 2 - n + 1 := by nlinarith
  have hnne : n ≠ 0 := hn0.ne'
  have hAne : n ^ 2 - n + 1 ≠ 0 := hA0.ne'
  have hnum : 0 < n * (n ^ 2 - n + 1) - (n * (n - 1) - (n - 2 + c)) := by
    rcases hc with rfl | rfl <;> nlinarith
  have hx : 0 < ((n * (n ^ 2 - n + 1) - (n * (n - 1) - (n - 2 + c))) / (n ^ 2 - n + 1))
        / ((n ^ 2 - n + 1) / n) := by positivity
  refine le_trans (Real.log_le_sub_one_of_pos hx) ?_
  -- in fact `x - 1 = ((n-1)c - (1-c)) / A²`, and the `c = 0` value is negative
  generalize hAdef : n ^ 2 - n + 1 = A at *
  rcases hc with rfl | rfl
  · rw [mul_zero, sub_nonpos, div_div_eq_mul_div, div_le_one (by positivity)]
    rw [div_mul_eq_mul_div, div_le_iff₀ hA0]
    have : A = n ^ 2 - n + 1 := hAdef.symm
    subst this
    nlinarith
  · apply le_of_eq
    field_simp
    have : A = n ^ 2 - n + 1 := hAdef.symm
    subst this
    ring

/-! ### The fourth row -/

/-- The exact deviation of the fourth rate, as an identity. -/
theorem rate4_id (n1 n2 n3 n4 e12 e23 e34 t123 t234 q : ℝ) (hn3 : n3 ≠ 0)
    (hN3 : n3 * (n1 * n2 - e12) - (n1 * e23 - t123) ≠ 0) :
    (n4 * (n3 * (n1 * n2 - e12) - (n1 * e23 - t123)) - (n1 * (n2 * e34 - t234) - e12 * e34 + q))
        / (n3 * (n1 * n2 - e12) - (n1 * e23 - t123)) - (n4 - e34 / n3)
      = (n1 * (n3 * t234 - e23 * e34) + (e34 * t123 - n3 * q))
        / (n3 * (n3 * (n1 * n2 - e12) - (n1 * e23 - t123))) := by
  field_simp
  ring

/-- **Row four, actual side.** With `N₃ = n₃N₂ - M₃` and `M₄ = n₁(n₂e₃₄ - t₂₃₄) - e₁₂e₃₄ + q ∈ [0, N₃]`,
the rate `r₄ = (n₄N₃ - M₄)/N₃` is within `(μ₃+2)(μ₄+1)/(n(n-1)³)` (in log) below
`r̃₄ = n₄ - e₃₄/n₃`. -/
theorem rate4_err {n n1 n2 n3 n4 e12 e23 e34 t123 t234 q μ3 μ4 : ℝ} (hn : 6 ≤ n)
    (hn1 : n ≤ n1) (hn1' : n1 ≤ n + 1) (hn2 : n ≤ n2) (hn2' : n2 ≤ n + 1)
    (hn3 : n ≤ n3) (hn3' : n3 ≤ n + 1) (hn4 : n ≤ n4) (hn4' : n4 ≤ n + 1)
    (he12 : 0 ≤ e12) (he12n : e12 ≤ n1) (he23n : e23 ≤ n3) (he34 : 0 ≤ e34) (he34n : e34 ≤ n3)
    (ht234 : e23 + e34 - n3 ≤ t234) (hq : q ≤ t123) (ht0 : 0 ≤ t123) (ht1 : t123 ≤ n1)
    (hM30 : 0 ≤ n1 * e23 - t123) (hM3N : n1 * e23 - t123 ≤ n1 * n2 - e12)
    (hM40 : 0 ≤ n1 * (n2 * e34 - t234) - e12 * e34 + q)
    (hM4N : n1 * (n2 * e34 - t234) - e12 * e34 + q
      ≤ n3 * (n1 * n2 - e12) - (n1 * e23 - t123))
    (hd3 : n3 - e23 ≤ μ3 + 1) (hd4 : n3 - e34 ≤ μ4 + 1) (hμ3 : 0 ≤ μ3) (hμ4 : 0 ≤ μ4) :
    -((μ3 + 2) * (μ4 + 1) / (n * (n - 1) ^ 3))
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
  -- name the long expressions
  generalize hN3d : n3 * (n1 * n2 - e12) - (n1 * e23 - t123) = N3 at *
  generalize hM4d : n1 * (n2 * e34 - t234) - e12 * e34 + q = M4 at *
  have hN3p : 0 < N3 := lt_of_lt_of_le (by positivity) hN3big
  have hr4lo : n4 - 1 ≤ (n4 * N3 - M4) / N3 := by
    rw [le_div_iff₀ hN3p]; linarith
  have hr4hi : (n4 * N3 - M4) / N3 ≤ n + 1 := by
    rw [div_le_iff₀ hN3p]
    have := mul_le_mul_of_nonneg_right hn4' hN3p.le
    linarith
  have hrt0 : 0 < n4 - e34 / n3 := by
    have : e34 / n3 ≤ 1 := by rw [div_le_one hn3p]; exact he34n
    linarith
  have hnum : -((n3 - e34) * (n1 * (n3 - e23) + t123))
      ≤ n1 * (n3 * t234 - e23 * e34) + (e34 * t123 - n3 * q) := by
    have hw : n1 * (n3 * t234 - e23 * e34) + (e34 * t123 - n3 * q)
        - -((n3 - e34) * (n1 * (n3 - e23) + t123))
        = n1 * n3 * (t234 - (e23 + e34 - n3)) + n3 * (t123 - q) := by ring
    have h1 : 0 ≤ n1 * n3 * (t234 - (e23 + e34 - n3)) :=
      mul_nonneg (mul_nonneg hn1p.le hn3p.le) (by linarith)
    have h2 : 0 ≤ n3 * (t123 - q) := mul_nonneg hn3p.le (by linarith)
    linarith
  have hX0 : 0 ≤ n1 * (n3 - e23) + t123 := by
    have : 0 ≤ n1 * (n3 - e23) := mul_nonneg hn1p.le (by linarith)
    linarith
  have hX : n1 * (n3 - e23) + t123 ≤ n1 * (μ3 + 2) := by
    have := mul_le_mul_of_nonneg_left hd3 hn1p.le
    have e : n1 * (μ3 + 2) = n1 * (μ3 + 1) + n1 := by ring
    linarith
  have hprod : (n3 - e34) * (n1 * (n3 - e23) + t123) ≤ (μ4 + 1) * (n1 * (μ3 + 2)) :=
    mul_le_mul hd4 hX hX0 (by linarith)
  have hden : n * (n - 1) ^ 2 * n1 ≤ n3 * N3 := by
    have := mul_le_mul hn3 hN3big (by positivity) hn3p.le
    have e : n * (n - 1) ^ 2 * n1 = n * ((n - 1) * (n1 * (n - 1))) := by ring
    linarith
  have hfrac : (n3 - e34) * (n1 * (n3 - e23) + t123) / (n3 * N3)
      ≤ (μ4 + 1) * (n1 * (μ3 + 2)) / (n * (n - 1) ^ 2 * n1) :=
    div_le_div₀ (by positivity) hprod (by positivity) hden
  have hsimp : (μ4 + 1) * (n1 * (μ3 + 2)) / (n * (n - 1) ^ 2 * n1)
      = (μ3 + 2) * (μ4 + 1) / (n * (n - 1) ^ 2) := by
    have : n1 ≠ 0 := hn1p.ne'
    have : n ≠ 0 := hn0.ne'
    have : n - 1 ≠ 0 := hl0.ne'
    field_simp
  have hdiff : 0 - (μ3 + 2) * (μ4 + 1) / (n * (n - 1) ^ 2) ≤ (n4 * N3 - M4) / N3 - (n4 - e34 / n3) := by
    rw [hid]
    have : -((n3 - e34) * (n1 * (n3 - e23) + t123)) / (n3 * N3)
        ≤ (n1 * (n3 * t234 - e23 * e34) + (e34 * t123 - n3 * q)) / (n3 * N3) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    rw [neg_div] at this
    linarith
  have hQ : 0 ≤ (μ3 + 2) * (μ4 + 1) / (n * (n - 1) ^ 2) := by positivity
  have hlog := log_ratio_ge hl0 (by linarith) hr4hi hrt0 le_rfl hQ hdiff
  have e1 : (0 : ℝ) / (n + 1) - (μ3 + 2) * (μ4 + 1) / (n * (n - 1) ^ 2) / (n - 1)
      = -((μ3 + 2) * (μ4 + 1) / (n * (n - 1) ^ 3)) := by
    have : n ≠ 0 := hn0.ne'
    have : n - 1 ≠ 0 := hl0.ne'
    field_simp; ring
  linarith

/-! ### The fourth row: uniform side and the defect-free tail (numerical, `7 ≤ k ≤ 7`) -/

/-- The fourth rate from the counting data `(n₁, …, q)`. -/
noncomputable def rate4 (n1 n2 n3 n4 e12 e23 e34 t123 t234 q : ℝ) : ℝ :=
  (n4 * (n3 * (n1 * n2 - e12) - (n1 * e23 - t123)) - (n1 * (n2 * e34 - t234) - e12 * e34 + q))
    / (n3 * (n1 * n2 - e12) - (n1 * e23 - t123))

/-- The uniform fourth rate for the pattern bits `c₁₃, c₂₄, c₁₄`. -/
noncomputable def r4U (n c13 c24 c14 : ℝ) : ℝ :=
  rate4 n n n n (n - 1) (n - 1) (n - 1) (n - 2 + c13) (n - 2 + c24) (n - 3 + c13 + c24 + c14)

/-- `log x ≤ y` from `x - 1 ≤ y`. -/
theorem log_le_of_sub_one_le {x y : ℝ} (hx : 0 < x) (h : x - 1 ≤ y) : log x ≤ y :=
  (Real.log_le_sub_one_of_pos hx).trans h

/-- **Row four, uniform side.** In log against `t`, the uniform fourth rate is at most
`c₂₄/((n-1)²t) + 1/(nt²(n-1))`. Checked for each `k = 7`, `n = k - 1`. -/
theorem rate4_unif {k : ℕ} (hk : 7 ≤ k) (hk' : k ≤ 7) {c13 c24 c14 : ℝ}
    (h13 : c13 = 0 ∨ c13 = 1) (h24 : c24 = 0 ∨ c24 = 1) (h14 : c14 = 0 ∨ c14 = 1)
    (h1314 : c13 * c14 = 0) (h2414 : c24 * c14 = 0) :
    log (r4U ((k : ℝ) - 1) c13 c24 c14 / ((((k : ℝ) - 1) ^ 2 - ((k : ℝ) - 1) + 1) / ((k : ℝ) - 1)))
      ≤ c24 / (((k : ℝ) - 2) ^ 2 * ((((k : ℝ) - 1) ^ 2 - ((k : ℝ) - 1) + 1) / ((k : ℝ) - 1)))
        + 1 / (((k : ℝ) - 1) * ((((k : ℝ) - 1) ^ 2 - ((k : ℝ) - 1) + 1) / ((k : ℝ) - 1)) ^ 2
          * ((k : ℝ) - 2)) := by
  rcases h14 with rfl | rfl
  · rcases h13 with rfl | rfl <;> rcases h24 with rfl | rfl <;>
      (apply log_le_of_sub_one_le (by interval_cases k <;> norm_num [r4U, rate4]);
       interval_cases k <;> norm_num [r4U, rate4])
  · have e13 : c13 = 0 := by simpa using h1314
    have e24 : c24 = 0 := by simpa using h2414
    subst e13 e24
    apply log_le_of_sub_one_le (by interval_cases k <;> norm_num [r4U, rate4])
    interval_cases k <;> norm_num [r4U, rate4]

/-- **Row four, the defect-free tail.** When all lists agree and only row one has a bonus, the
data are explicit and the fourth-row error is at least `-1/(nt(n-1)³)`. -/
theorem rate4_tail {k : ℕ} (hk : 7 ≤ k) (hk' : k ≤ 7) {c24 : ℝ} (h24 : c24 = 0 ∨ c24 = 1) :
    -(1 / (((k : ℝ) - 1) * ((((k : ℝ) - 1) ^ 2 - ((k : ℝ) - 1) + 1) / ((k : ℝ) - 1))
          * ((k : ℝ) - 2) ^ 3))
      ≤ log (rate4 ((k : ℝ)) ((k : ℝ) - 1) ((k : ℝ) - 1) ((k : ℝ) - 1) ((k : ℝ) - 1)
              ((k : ℝ) - 2) ((k : ℝ) - 2) ((k : ℝ) - 2) ((k : ℝ) - 3 + c24) ((k : ℝ) - 3 + c24)
            / (((k : ℝ) - 1) - ((k : ℝ) - 2) / ((k : ℝ) - 1)))
        - log (r4U ((k : ℝ) - 1) 0 c24 0
            / ((((k : ℝ) - 1) ^ 2 - ((k : ℝ) - 1) + 1) / ((k : ℝ) - 1))) := by
  have key : ∀ x y z : ℝ, 0 < x → 0 < y → 0 < z → ∀ b : ℝ, b ≤ 1 - y / x →
      b ≤ log (x / z) - log (y / z) := by
    intro x y z hx hy hz b h
    rw [← Real.log_div (div_pos hx hz).ne' (div_pos hy hz).ne',
      show x / z / (y / z) = x / y by field_simp]
    refine h.trans ?_
    have := Real.one_sub_inv_le_log_of_pos (div_pos hx hy)
    rwa [inv_div] at this
  have hz : ∀ k : ℕ, 7 ≤ k → 0 < (((k : ℝ) - 1) ^ 2 - ((k : ℝ) - 1) + 1) / ((k : ℝ) - 1) := by
    intro k hk
    have : (7 : ℝ) ≤ k := by exact_mod_cast hk
    apply div_pos <;> nlinarith
  have heq : ∀ k : ℕ, 7 ≤ k → ((k : ℝ) - 1) - ((k : ℝ) - 2) / ((k : ℝ) - 1)
      = (((k : ℝ) - 1) ^ 2 - ((k : ℝ) - 1) + 1) / ((k : ℝ) - 1) := by
    intro k hk
    have : (7 : ℝ) ≤ k := by exact_mod_cast hk
    have : (k : ℝ) - 1 ≠ 0 := by linarith
    field_simp; ring
  rw [heq k hk]
  rcases h24 with rfl | rfl <;>
  (apply key _ _ _ (by interval_cases k <;> norm_num [rate4]) (by interval_cases k <;> norm_num [r4U, rate4])
      (hz k hk);
   interval_cases k <;> norm_num [rate4, r4U])

end GridGen.Four
