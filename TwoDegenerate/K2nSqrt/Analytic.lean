/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The analytic inequality behind `τ(K₂,ₙ) = O(√n)`

`TwoDegenerate/K2nSqrt/Classes.lean` bounds the number of colourings of a pushed `k`-list
assignment on `K₂,ₙ` with hub overlap `r` from below by `(k - 1)ⁿ · lowerG k r x η λ w`, where
`x = n log (k / (k - 1))`, `η = n log ((k - 1)² / (k (k - 2)))`, `λ = η / x` and `w ≥ 0` records how
many shared hub colours the right lists omit. The constant assignment has `(k - 1)ⁿ · target k x η`
colourings. This file proves `target ≤ lowerG` for `k ≥ 300`, `1 ≤ r ≤ k - 2` and `n ≤ k²`
(`target_le_lowerG`), and the `r = 0` case (`target_le_lowerG_zero`).

The four terms of `lowerG` are the AM–GM bounds on the four classes of hub-colour pairs: equal
shared colours `D`, distinct shared colours `O`, one shared and one private colour `M`, and two
private colours `PQ`. Write `s = k - r`, `E = e^{-x/2}`, `q = e^{-η}`, `Q = e^{-η/4}`. The proof has
four regimes, each closed by tangent lines `e^y ≥ e^{y₀}(1 + y - y₀)` alone:

* `A`, `e^{-x} ≥ 3/10`: the tangent line at `w = 0`, whose slope is nonnegative;
* `Ψ`, `r ≥ s` and `e^{-x} ≤ 3/10`: linearise `D` and `O` in `u = (r/s) w` and bound the two
  remaining exponentials in `u` by their Legendre transforms;
* `Φ`, `r < s` and `1/(k + r - 1) ≤ e^{-x} ≤ 3/10`: split at the `w₁` where `M` alone reaches
  its share of the target; below `w₁` the `PQ` term is still large;
* `V`, `r < s` and `e^{-x} ≤ 1/(k + r - 1)`: the target is at most `2k`; split at the `w₂` where
  `D` alone reaches `2k`.
-/

namespace SimpleGraph.TwoDegenerate.K2nSqrt

open Real

/-- The normalised lower bound: the four class terms `D`, `PQ`, `O`, `M`. -/
noncomputable def lowerG (k r x η lam w : ℝ) : ℝ :=
  r * exp w + (k - r) ^ 2 * exp (-(η / 4) - r / (k - r) * (1 + 3 * lam / 4) * w) +
    r * (r - 1) * exp (-x - η + (2 + lam) * w) +
    2 * r * (k - r) * exp (-(x / 2) - η + (1 - r / (2 * (k - r))) * w)

/-- The normalised constant count `k + k (k - 1) ((k - 2)/(k - 1))ⁿ`. -/
noncomputable def target (k x η : ℝ) : ℝ := k + k * (k - 1) * exp (-x - η)

/-- The standing hypotheses on the parameters. -/
structure Hyp (k x η lam : ℝ) : Prop where
  hk : 300 ≤ k
  hx : 0 ≤ x
  hη : 0 ≤ η
  hηx : η * (k - 2) ≤ x
  hη1 : η ≤ 11 / 10
  hl0 : 0 ≤ lam
  hl1 : lam * (k - 2) ≤ 1

/-! ### Exponential toolkit -/

/-- The tangent line of `exp` at `y₀`. -/
theorem exp_ge_tangent (y y₀ : ℝ) : exp y₀ * (1 + (y - y₀)) ≤ exp y := by
  have h1 := add_one_le_exp (y - y₀)
  have h2 : exp y = exp y₀ * exp (y - y₀) := by rw [← exp_add]; ring_nf
  rw [h2]
  exact mul_le_mul_of_nonneg_left (by linarith) (exp_pos y₀).le

/-- `c e^{a + d w} ≥ c e^a (1 + d w)`. -/
theorem mul_exp_ge_tangent {c : ℝ} (hc : 0 ≤ c) (a d w : ℝ) :
    c * exp a * (1 + d * w) ≤ c * exp (a + d * w) := by
  have := exp_ge_tangent (a + d * w) a
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (by linarith) hc

/-- Legendre bound: `c u + B e^{-a u} ≥ (c / a)(1 + log (a B / c))`. -/
theorem linear_add_exp_ge {a c B : ℝ} (ha : 0 < a) (hc : 0 < c) (hB : 0 < B) (u : ℝ) :
    c / a * (1 + log (a * B / c)) ≤ c * u + B * exp (-(a * u)) := by
  have hpos : 0 < a * B / c := by positivity
  have h := exp_ge_tangent (-(a * u)) (-log (a * B / c))
  rw [exp_neg, exp_log hpos] at h
  have h' : c / a * (1 + log (a * B / c)) - c * u = B * ((a * B / c)⁻¹ * (1 + (-(a * u) -
      -log (a * B / c)))) := by
    field_simp
    ring
  nlinarith

theorem exp_neg_le_inv_one_add {x : ℝ} (hx : 0 ≤ x) : exp (-x) ≤ 1 / (1 + x) := by
  rw [exp_neg, one_div]
  exact inv_anti₀ (by linarith) (by linarith [add_one_le_exp x])

theorem one_sub_le_exp_neg (x : ℝ) : 1 - x ≤ exp (-x) := by
  linarith [add_one_le_exp (-x)]

/-- `e^{0.1} ≤ 10/9`. -/
theorem exp_tenth_le : exp (1 / 10) ≤ 10 / 9 := by
  have h := one_sub_le_exp_neg (1 / 10)
  have hm : exp (1 / 10) * exp (-(1 / 10)) = 1 := by rw [← exp_add]; simp
  nlinarith [exp_pos (1 / 10), exp_pos (-(1 / 10))]

/-- `e^{-11/10} ≥ 3/10`. -/
theorem exp_neg_eleven_tenths : 3 / 10 ≤ exp (-(11 / 10)) := by
  have h1 : exp (11 / 10) = exp 1 * exp (1 / 10) := by rw [← exp_add]; norm_num
  have he := exp_one_lt_d9
  have ht := exp_tenth_le
  have hle : exp (11 / 10) ≤ 10 / 3 := by
    rw [h1]; nlinarith [exp_pos 1, exp_pos (1 / 10)]
  rw [exp_neg]
  rw [le_inv_comm₀ (by norm_num) (exp_pos _)]
  linarith

/-- If `e^{-x} ≥ 3/10` then `x ≤ 13/10`. -/
theorem le_of_exp_neg_ge {x : ℝ} (h : 3 / 10 ≤ exp (-x)) : x ≤ 13 / 10 := by
  by_contra hx
  push Not at hx
  have h1 : exp (13 / 10) = exp 1 * exp (3 / 10) := by rw [← exp_add]; norm_num
  have h2 := add_one_le_exp (3 / 10)
  have he := exp_one_gt_d9
  have h3 : 7 / 2 ≤ exp (13 / 10) := by rw [h1]; nlinarith [exp_pos 1]
  have h4 : exp (-x) < exp (-(13 / 10)) := exp_lt_exp.mpr (by linarith)
  rw [exp_neg (13 / 10)] at h4
  have h5 : (exp (13 / 10))⁻¹ ≤ 2 / 7 := by
    rw [inv_le_comm₀ (exp_pos _) (by norm_num)]; linarith
  linarith

/-! ### Shorthand -/

section Shorthand

variable (x η : ℝ)

theorem exp_split_O (c : ℝ) :
    exp (-x - η + c) = exp (-η) * exp (-(x / 2)) ^ 2 * exp c := by
  rw [sq, ← exp_add, ← exp_add, ← exp_add]; ring_nf

theorem exp_split_M (c : ℝ) :
    exp (-(x / 2) - η + c) = exp (-η) * exp (-(x / 2)) * exp c := by
  rw [← exp_add, ← exp_add]; ring_nf

theorem exp_split_PQ (c : ℝ) : exp (-(η / 4) - c) = exp (-(η / 4)) * exp (-c) := by
  rw [← exp_add]; ring_nf

theorem exp_split_target : exp (-x - η) = exp (-η) * exp (-(x / 2)) ^ 2 := by
  rw [sq, ← exp_add, ← exp_add]; ring_nf

theorem exp_q_eq : exp (-η) = exp (-(η / 4)) ^ 4 := by
  rw [← exp_nat_mul]; ring_nf

theorem exp_E_sq : exp (-(x / 2)) ^ 2 = exp (-x) := by
  rw [← exp_nat_mul]; ring_nf

end Shorthand

/-! ### Common facts -/

section Facts

variable {k x η lam : ℝ}

theorem Hyp.E_pos : 0 < exp (-(x / 2)) := exp_pos _

theorem Hyp.E_le_one (H : Hyp k x η lam) : exp (-(x / 2)) ≤ 1 :=
  exp_le_one_iff.mpr (by linarith [H.hx])

theorem Hyp.Q_le_one (H : Hyp k x η lam) : exp (-(η / 4)) ≤ 1 :=
  exp_le_one_iff.mpr (by linarith [H.hη])

theorem Hyp.q_le_Q (H : Hyp k x η lam) : exp (-η) ≤ exp (-(η / 4)) :=
  exp_le_exp.mpr (by linarith [H.hη])

theorem Hyp.q_ge (_ : Hyp k x η lam) : 1 - η ≤ exp (-η) := one_sub_le_exp_neg η

theorem Hyp.Q_ge (_ : Hyp k x η lam) : 1 - η / 4 ≤ exp (-(η / 4)) := one_sub_le_exp_neg _

theorem Hyp.q_ge_three_tenths (H : Hyp k x η lam) : 3 / 10 ≤ exp (-η) :=
  exp_neg_eleven_tenths.trans (exp_le_exp.mpr (by linarith [H.hη1]))

/-- `(1 - e^{-x})(1 + x) ≥ x`. -/
theorem Hyp.one_sub_a (H : Hyp k x η lam) : x ≤ (1 - exp (-x)) * (1 + x) := by
  have h := exp_neg_le_inv_one_add H.hx
  have h1 : 0 < 1 + x := by linarith [H.hx]
  rw [le_div_iff₀ h1] at h
  nlinarith

end Facts

/-! ### Regime `A`: the tangent line at `w = 0` -/

section RegimeA

theorem regimeA_f2 {k q E ε : ℝ} (hk : 300 ≤ k) (hq : 99 / 100 ≤ q) (hE : 547 / 1000 ≤ E)
    (hε0 : 0 ≤ ε) (hε : ε * (k - 2) ≤ 3 / 4) :
    0 ≤ 1 - 2 * (1 + ε) + 2 * (k - 2 - 1) * (q * E ^ 2) + q * E * (3 * 2 - k) := by
  have hid : 1 - 2 * (1 + ε) + 2 * (k - 2 - 1) * (q * E ^ 2) + q * E * (3 * 2 - k) =
      -1 - 2 * ε + (q * E) * (2 * (k - 3) * E - (k - 6)) := by ring
  rw [hid]
  have h1 : (k - 3) * (547 / 1000) ≤ (k - 3) * E := mul_le_mul_of_nonneg_left hE (by linarith)
  have h2 : 30 ≤ 2 * (k - 3) * E - (k - 6) := by linarith
  have h3 : (99 / 100) * (547 / 1000) ≤ q * E := mul_le_mul hq hE (by norm_num) (by linarith)
  have h4 : (99 / 100) * (547 / 1000) * 30 ≤ (q * E) * (2 * (k - 3) * E - (k - 6)) :=
    mul_le_mul h3 h2 (by norm_num) (by linarith)
  have h5 : ε * 298 ≤ ε * (k - 2) := mul_le_mul_of_nonneg_left (by linarith) hε0
  linarith

theorem regimeA_fk {k q E ε : ℝ} (hk : 300 ≤ k) (hq : 99 / 100 ≤ q) (hE : 547 / 1000 ≤ E)
    (hε0 : 0 ≤ ε) (hε : ε * (k - 2) ≤ 3 / 4) :
    0 ≤ 1 - (k - 1) * (1 + ε) + 2 * (k - (k - 1) - 1) * (q * E ^ 2) +
      q * E * (3 * (k - 1) - k) := by
  have hid : 1 - (k - 1) * (1 + ε) + 2 * (k - (k - 1) - 1) * (q * E ^ 2) +
      q * E * (3 * (k - 1) - k) = 2 - k - (k - 1) * ε + (q * E) * (2 * k - 3) := by ring
  rw [hid]
  have h0 : (k - 1) * ε ≤ 1 := by
    have h5 : ε * 298 ≤ ε * (k - 2) := mul_le_mul_of_nonneg_left (by linarith) hε0
    linarith
  have h3 : (99 / 100) * (547 / 1000) ≤ q * E := mul_le_mul hq hE (by norm_num) (by linarith)
  have h4 : (99 / 100) * (547 / 1000) * (2 * k - 3) ≤ (q * E) * (2 * k - 3) :=
    mul_le_mul_of_nonneg_right h3 (by linarith)
  nlinarith

/-- The slope of the tangent line at `w = 0`, up to the factor `r`, is nonnegative. -/
theorem regimeA_slope {k r q E ε lam Q : ℝ} (hk : 300 ≤ k) (hr : 1 ≤ r) (hrk : r ≤ k - 2)
    (hq : 99 / 100 ≤ q) (hE : 547 / 1000 ≤ E) (hε0 : 0 ≤ ε)
    (hε : ε * (k - 2) ≤ 3 / 4) (hl : 0 ≤ lam) (hQ1 : Q ≤ 1) :
    0 ≤ 1 - (k - r) * Q * (1 + ε) + (r - 1) * (q * E ^ 2) * (2 + lam) +
      q * E * (2 * (k - r) - r) := by
  set f : ℝ → ℝ := fun t => 1 - t * (1 + ε) + 2 * (k - t - 1) * (q * E ^ 2) +
    q * E * (3 * t - k) with hf
  have hf2 : 0 ≤ f 2 := regimeA_f2 hk hq hE hε0 hε
  have hfk : 0 ≤ f (k - 1) := regimeA_fk hk hq hE hε0 hε
  have hid : (k - 3) * f (k - r) = (k - 1 - (k - r)) * f 2 + ((k - r) - 2) * f (k - 1) := by
    simp only [hf]; ring
  have h1 : 0 ≤ (k - 1 - (k - r)) * f 2 := mul_nonneg (by linarith) hf2
  have h2 : 0 ≤ ((k - r) - 2) * f (k - 1) := mul_nonneg (by linarith) hfk
  have hfs : 0 ≤ f (k - r) := by
    have h3 : 0 ≤ (k - 3) * f (k - r) := by linarith
    exact (mul_nonneg_iff_of_pos_left (by linarith : (0 : ℝ) < k - 3)).mp h3
  have hqE2 : 0 ≤ q * E ^ 2 := mul_nonneg (by linarith) (sq_nonneg E)
  have h4 : (k - r) * Q * (1 + ε) ≤ (k - r) * (1 + ε) := by
    have := mul_le_mul_of_nonneg_left hQ1
      (mul_nonneg (by linarith) (by linarith) : (0 : ℝ) ≤ (k - r) * (1 + ε))
    linarith
  have h5 : (r - 1) * (q * E ^ 2) * 2 ≤ (r - 1) * (q * E ^ 2) * (2 + lam) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (by linarith) hqE2)
  have h6 : f (k - r) = 1 - (k - r) * (1 + ε) + (r - 1) * (q * E ^ 2) * 2 +
      q * E * (2 * (k - r) - r) := by simp only [hf]; ring
  linarith

/-- The value at `w = 0`: `s Q - 1 - (s - 1) q E² ≥ 0`. -/
theorem regimeA_value {k s x η q Q E : ℝ} (hk : 300 ≤ k) (hs : 2 ≤ s)
    (hx13 : x ≤ 13 / 10) (hη : 0 ≤ η) (hηx : η * (k - 2) ≤ x) (hqQ : q ≤ Q)
    (hQge : 1 - η / 4 ≤ Q) (hE : x ≤ (1 - E ^ 2) * (1 + x)) (hE1 : E ^ 2 ≤ 1) :
    0 ≤ s * Q - 1 - (s - 1) * (q * E ^ 2) := by
  have hE0 : 0 ≤ E ^ 2 := sq_nonneg E
  have h1 : (s - 1) * (q * E ^ 2) ≤ (s - 1) * (Q * E ^ 2) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hqQ hE0) (by linarith)
  set D := 1 - E ^ 2 with hD
  have hD0 : 0 ≤ D := by linarith
  have h4 : x ≤ D * (23 / 10) := by
    have : D * (1 + x) ≤ D * (23 / 10) := mul_le_mul_of_nonneg_left (by linarith) hD0
    linarith
  have hη298 : η * 298 ≤ x := by nlinarith
  have hηs : η ≤ 1 / 100 := by nlinarith
  have h5 : η * 4 ≤ D := by nlinarith
  have h6 : (s - 1) * Q * D ≥ D * (1 - η / 4) := by
    have : 1 * (1 - η / 4) ≤ (s - 1) * Q :=
      mul_le_mul (by linarith) hQge (by linarith) (by linarith)
    nlinarith
  have h7 : s * Q - 1 - (s - 1) * (Q * E ^ 2) = (Q - 1) + (s - 1) * Q * D := by
    rw [hD]; ring
  nlinarith

theorem regimeA {k r x η lam w : ℝ} (H : Hyp k x η lam) (hr : 1 ≤ r) (hrk : r ≤ k - 2)
    (ha : 3 / 10 ≤ exp (-x)) (hw : 0 ≤ w) : target k x η ≤ lowerG k r x η lam w := by
  have hk := H.hk
  set s := k - r with hs
  have hs2 : 2 ≤ s := by linarith
  have hspos : 0 < s := by linarith
  set E := exp (-(x / 2)) with hEdef
  set q := exp (-η) with hqdef
  set Q := exp (-(η / 4)) with hQdef
  set ε := 3 * lam / 4 with hεdef
  have hE0 : 0 < E := exp_pos _
  have hE1 : E ≤ 1 := H.E_le_one
  have hE2 : E ^ 2 = exp (-x) := exp_E_sq x
  have hEa : 547 / 1000 ≤ E := by nlinarith
  have hx13 := le_of_exp_neg_ge ha
  have hq0 : 0 < q := exp_pos _
  have hQ0 : 0 < Q := exp_pos _
  have hqQ : q ≤ Q := H.q_le_Q
  have hQ1 : Q ≤ 1 := H.Q_le_one
  have hqge : 1 - η ≤ q := H.q_ge
  have hQge : 1 - η / 4 ≤ Q := H.Q_ge
  have hηsmall : η * 298 ≤ 13 / 10 := by nlinarith [H.hηx, H.hη]
  have hq995 : 99 / 100 ≤ q := by linarith
  have hε : ε * (k - 2) ≤ 3 / 4 := by rw [hεdef]; nlinarith [H.hl1, H.hl0]
  have hε0 : 0 ≤ ε := by have := H.hl0; positivity
  -- Tangent lines at `w = 0`.
  have tD : r * (1 + w) ≤ r * exp w := by
    have := mul_exp_ge_tangent (c := r) (by linarith) 0 1 w
    simpa using this
  have tPQ : s ^ 2 * Q * (1 + -(r / s * (1 + ε)) * w) ≤
      s ^ 2 * exp (-(η / 4) - r / s * (1 + ε) * w) := by
    have := mul_exp_ge_tangent (c := s ^ 2) (by positivity) (-(η / 4)) (-(r / s * (1 + ε))) w
    convert this using 2; ring_nf
  have tO : r * (r - 1) * (q * E ^ 2) * (1 + (2 + lam) * w) ≤
      r * (r - 1) * exp (-x - η + (2 + lam) * w) := by
    have := mul_exp_ge_tangent (c := r * (r - 1)) (by nlinarith) (-x - η) (2 + lam) w
    rwa [exp_split_target] at this
  have tM : 2 * r * s * (q * E) * (1 + (1 - r / (2 * s)) * w) ≤
      2 * r * s * exp (-(x / 2) - η + (1 - r / (2 * s)) * w) := by
    have := mul_exp_ge_tangent (c := 2 * r * s) (by positivity) (-(x / 2) - η)
      (1 - r / (2 * s)) w
    convert this using 2; rw [← exp_add]; ring_nf
  have hslope := regimeA_slope hk hr hrk hq995 hEa hε0 hε H.hl0 hQ1
  have hval := regimeA_value hk hs2 hx13 H.hη H.hηx hqQ hQge (hE2 ▸ H.one_sub_a)
    (by nlinarith)
  have hG : target k x η ≤ r + s ^ 2 * Q + r * (r - 1) * (q * E ^ 2) + 2 * r * s * (q * E) := by
    have hid : r + s ^ 2 * Q + r * (r - 1) * (q * E ^ 2) + 2 * r * s * (q * E) - target k x η =
        s * (s * Q - 1 - (s - 1) * (q * E ^ 2)) + 2 * r * s * (q * E) * (1 - E) := by
      simp only [target, exp_split_target, hs]; ring
    have := mul_nonneg hspos.le hval
    have := mul_nonneg (by positivity : 0 ≤ 2 * r * s * (q * E)) (by linarith : 0 ≤ 1 - E)
    linarith
  have hsl : 0 ≤ r * (1 - s * Q * (1 + ε) + (r - 1) * (q * E ^ 2) * (2 + lam) +
      q * E * (2 * s - r)) * w := mul_nonneg (mul_nonneg (by linarith) hslope) hw
  have hexpand : r * (1 + w) + s ^ 2 * Q * (1 + -(r / s * (1 + ε)) * w) +
      r * (r - 1) * (q * E ^ 2) * (1 + (2 + lam) * w) +
      2 * r * s * (q * E) * (1 + (1 - r / (2 * s)) * w) =
      (r + s ^ 2 * Q + r * (r - 1) * (q * E ^ 2) + 2 * r * s * (q * E)) +
      r * (1 - s * Q * (1 + ε) + (r - 1) * (q * E ^ 2) * (2 + lam) + q * E * (2 * s - r)) * w := by
    field_simp
    ring
  have hlow : lowerG k r x η lam w = r * exp w +
      s ^ 2 * exp (-(η / 4) - r / s * (1 + ε) * w) +
      r * (r - 1) * exp (-x - η + (2 + lam) * w) +
      2 * r * s * exp (-(x / 2) - η + (1 - r / (2 * s)) * w) := by
    simp only [lowerG, hs, hεdef]
  rw [hlow]
  linarith

end RegimeA

/-! ### Regime `Ψ`: `r ≥ s`, Legendre bounds in `u = (r/s) w` -/

section RegimePsi

/-- `log (r / (2 (r - 1) E)) ≥ -1/10` when `E² ≤ 3/10`. -/
theorem psi_log_ge {r E : ℝ} (hr : 2 ≤ r) (hE0 : 0 < E) (hE : E ^ 2 ≤ 3 / 10) :
    -(1 / 10) ≤ log (r / (2 * (r - 1) * E)) := by
  have hE55 : E ≤ 55 / 100 := by nlinarith
  have hr1 : (0 : ℝ) < r - 1 := by linarith
  have hden : 0 < 2 * (r - 1) * E := by positivity
  have h1 : 10 / 11 ≤ r / (2 * (r - 1) * E) := by
    rw [le_div_iff₀ hden]
    nlinarith
  have hpos : 0 < r / (2 * (r - 1) * E) := div_pos (by linarith) hden
  have h2 := one_sub_inv_le_log_of_pos hpos
  have h3 : (r / (2 * (r - 1) * E))⁻¹ ≤ 11 / 10 := by
    rw [inv_le_comm₀ hpos (by norm_num)]; linarith
  linarith

/-- The final inequality of regime `Ψ`. -/
theorem psi_final {k r η ε qE2 : ℝ} (hk : 300 ≤ k) (hsr : k - r ≤ r)
    (hη : η ≤ 11 / 10) (hε0 : 0 ≤ ε) (hε : ε * (k - 2) ≤ 3 / 4) (hq : 0 ≤ qE2) :
    0 ≤ (1 + log 2 - η / 4) / (1 + ε) + 2 * (2 * (r - 1) * qE2) * (1 - 1 / 10) - 1 -
      (2 * r + (k - r) - 1) * qE2 := by
  have hl2 := log_two_gt_d9
  have hε1 : ε ≤ 1 / 100 := by
    have : ε * 298 ≤ ε * (k - 2) := mul_le_mul_of_nonneg_left (by linarith) hε0
    linarith
  have h1 : 1 ≤ (1 + log 2 - η / 4) / (1 + ε) := by
    rw [le_div_iff₀ (by linarith)]; norm_num at hl2; linarith
  have h2 : 0 ≤ (2 * (2 * (r - 1)) * (1 - 1 / 10) - (2 * r + (k - r) - 1)) * qE2 :=
    mul_nonneg (by linarith) hq
  nlinarith

theorem regimePsi {k r x η lam w : ℝ} (H : Hyp k x η lam) (hsr : k ≤ 2 * r) (hrk : r ≤ k - 2)
    (ha : exp (-x) ≤ 3 / 10) (hw : 0 ≤ w) : target k x η ≤ lowerG k r x η lam w := by
  have hk := H.hk
  set s := k - r with hs
  have hs2 : 2 ≤ s := by linarith
  have hspos : 0 < s := by linarith
  have hr2 : 2 ≤ r := by linarith
  set E := exp (-(x / 2)) with hEdef
  set q := exp (-η) with hqdef
  set Q := exp (-(η / 4)) with hQdef
  set ε := 3 * lam / 4 with hεdef
  have hE0 : 0 < E := exp_pos _
  have hE2 : E ^ 2 = exp (-x) := exp_E_sq x
  have hq0 : 0 < q := exp_pos _
  have hQ0 : 0 < Q := exp_pos _
  have hε : ε * (k - 2) ≤ 3 / 4 := by rw [hεdef]; nlinarith [H.hl1, H.hl0]
  have hε0 : 0 ≤ ε := by have := H.hl0; positivity
  set u := r / s * w with hudef
  have hu : 0 ≤ u := by positivity
  have hsu : s * u = r * w := by rw [hudef]; field_simp
  -- Linearise `D` and `O`, drop the growth of `M`.
  have tD : r + s * u ≤ r * exp w := by
    rw [hsu]; nlinarith [add_one_le_exp w]
  have tO : r * (r - 1) * (q * E ^ 2) + 2 * (r - 1) * s * (q * E ^ 2) * u ≤
      r * (r - 1) * exp (-x - η + (2 + lam) * w) := by
    rw [exp_split_O]
    have h1 : 1 + 2 * w ≤ exp ((2 + lam) * w) := by
      have := add_one_le_exp ((2 + lam) * w); nlinarith [H.hl0]
    have h2 : 2 * (r - 1) * s * (q * E ^ 2) * u = r * (r - 1) * (q * E ^ 2) * (2 * w) := by
      rw [hudef]; field_simp
    rw [h2]
    have h3 : 0 ≤ r * (r - 1) * (q * E ^ 2) := by
      have : 0 ≤ r * (r - 1) := by nlinarith
      positivity
    nlinarith
  have tM : 2 * r * s * (q * E) * exp (-(u / 2)) ≤
      2 * r * s * exp (-(x / 2) - η + (1 - r / (2 * s)) * w) := by
    rw [exp_split_M]
    have h1 : -(u / 2) ≤ (1 - r / (2 * s)) * w := by
      have : (1 - r / (2 * s)) * w = w - u / 2 := by rw [hudef]; field_simp
      rw [this]; linarith
    have h2 := exp_le_exp.mpr h1
    have h3 : 0 ≤ 2 * r * s * (q * E) := by positivity
    calc 2 * r * s * (q * E) * exp (-(u / 2)) ≤ 2 * r * s * (q * E) * exp ((1 - r / (2 * s)) * w) :=
          mul_le_mul_of_nonneg_left h2 h3
      _ = _ := by ring
  have hPQ : s ^ 2 * exp (-(η / 4) - r / s * (1 + ε) * w) = s ^ 2 * (Q * exp (-((1 + ε) * u))) := by
    rw [exp_split_PQ]; congr 3; rw [hudef]; ring
  -- Two Legendre bounds.
  have La := linear_add_exp_ge (a := 1 + ε) (c := 1) (B := s * Q) (by linarith) one_pos
    (by positivity) u
  set c := 2 * (r - 1) * (q * E ^ 2) with hcdef
  have hc : 0 < c := by
    have : (0 : ℝ) < r - 1 := by linarith
    positivity
  have Lb := linear_add_exp_ge (a := 1 / 2) (c := c) (B := 2 * r * (q * E)) (by norm_num) hc
    (by positivity) u
  have hlogB : (1 / 2) * (2 * r * (q * E)) / c = r / (2 * (r - 1) * E) := by
    rw [hcdef]; field_simp
  rw [hlogB] at Lb
  have hlog1 := psi_log_ge hr2 hE0 (hE2 ▸ ha)
  have hLb : 2 * c * (1 - 1 / 10) ≤ c * u + 2 * r * (q * E) * exp (-(1 / 2 * u)) := by
    have : c / (1 / 2) = 2 * c := by ring
    rw [this] at Lb
    have := mul_le_mul_of_nonneg_left (by linarith : 1 - 1 / 10 ≤ 1 + log (r / (2 * (r - 1) * E)))
      (by positivity : (0 : ℝ) ≤ 2 * c)
    linarith
  have hlogA : log 2 - η / 4 ≤ log ((1 + ε) * (s * Q) / 1) := by
    rw [div_one, log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity),
      hQdef, log_exp]
    have : log 2 ≤ log (1 + ε) + log s := by
      rw [← log_mul (by positivity) (by positivity)]
      have : 0 ≤ ε * s := mul_nonneg hε0 hspos.le
      exact log_le_log (by norm_num) (by linarith)
    linarith
  have hLa : (1 + log 2 - η / 4) / (1 + ε) ≤ 1 * u + s * Q * exp (-((1 + ε) * u)) := by
    refine le_trans ?_ La
    have h1 : (1 + log 2 - η / 4) / (1 + ε) = 1 / (1 + ε) * (1 + log 2 - η / 4) := by ring
    rw [h1]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hfin := psi_final (r := r) hk (by linarith) H.hη1 hε0 hε (by positivity : 0 ≤ q * E ^ 2)
  -- Assemble: `lowerG - target ≥ s · ψ(u)`.
  have hlow : lowerG k r x η lam w = r * exp w +
      s ^ 2 * exp (-(η / 4) - r / s * (1 + ε) * w) +
      r * (r - 1) * exp (-x - η + (2 + lam) * w) +
      2 * r * s * exp (-(x / 2) - η + (1 - r / (2 * s)) * w) := by
    simp only [lowerG, hs, hεdef]
  have htarget : target k x η = r + s + (r * (r - 1) + s * (2 * r + s - 1)) * (q * E ^ 2) := by
    simp only [target, exp_split_target, hs]; ring
  have hhalf : exp (-(1 / 2 * u)) = exp (-(u / 2)) := by ring_nf
  rw [hhalf] at hLb
  rw [hlow, htarget, hPQ]
  have key : 0 ≤ s * ((1 * u + s * Q * exp (-((1 + ε) * u))) +
      (c * u + 2 * r * (q * E) * exp (-(u / 2))) - 1 - (2 * r + s - 1) * (q * E ^ 2)) := by
    apply mul_nonneg hspos.le
    have : (2 * r + (k - r) - 1) = (2 * r + s - 1) := by rw [hs]
    rw [this] at hfin
    linarith
  have hexp : s * ((1 * u + s * Q * exp (-((1 + ε) * u))) +
      (c * u + 2 * r * (q * E) * exp (-(u / 2))) - 1 - (2 * r + s - 1) * (q * E ^ 2)) =
      (r + s * u) + s ^ 2 * (Q * exp (-((1 + ε) * u))) +
      (r * (r - 1) * (q * E ^ 2) + 2 * (r - 1) * s * (q * E ^ 2) * u) +
      2 * r * s * (q * E) * exp (-(u / 2)) -
      (r + s + (r * (r - 1) + s * (2 * r + s - 1)) * (q * E ^ 2)) := by
    rw [hcdef]; ring
  linarith

end RegimePsi

/-! ### Regime `Φ`: `r < s`, split between `M` and `PQ` -/

section RegimePhi

/-- `1 + P q E² - 2 r q E ≤ (8/25) q E (2 s - r) / (1 + ε)`, cleared of denominators. -/
theorem phi_gamma {s r P q E ε : ℝ} (hs : 150 ≤ s) (hrs : r < s) (hr : 1 ≤ r)
    (hP : P = s + 2 * r - 1) (hq : 3 / 10 ≤ q) (hE0 : 0 < E) (hE : E ≤ 548 / 1000)
    (hPE : 17 ≤ P * E) (hε0 : 0 ≤ ε) (hε : ε ≤ 3 / 1000) :
    (1 + ε) * (1 + P * q * E ^ 2 - 2 * r * q * E) ≤ 8 / 25 * (q * E) * (2 * s - r) := by
  have hqE : 0 < q * E := by positivity
  -- `1 + P q E² ≤ q E (31/5 + (137/250) P)`.
  have h1 : 1 + P * q * E ^ 2 ≤ q * E * (31 / 5 + 137 / 250 * P) := by
    have e1 : q * E * (31 / 5) ≥ 3 / 10 * E * (31 / 5) := by nlinarith
    have e2 : q * (P * E) * (548 / 1000 - E) ≥ 3 / 10 * 17 * (548 / 1000 - E) := by
      have : 3 / 10 * 17 ≤ q * (P * E) := mul_le_mul hq hPE (by norm_num) (by linarith)
      exact mul_le_mul_of_nonneg_right this (by linarith)
    nlinarith
  have h2 : 137 / 250 * P - 2 * r ≤ 137 / 500 * (2 * s - r) := by rw [hP]; linarith
  have h3 : 1 + P * q * E ^ 2 - 2 * r * q * E ≤ q * E * (31 / 5 + 137 / 500 * (2 * s - r)) := by
    have := mul_le_mul_of_nonneg_left h2 hqE.le
    nlinarith
  have h4 : (1 + ε) * (31 / 5 + 137 / 500 * (2 * s - r)) ≤ 8 / 25 * (2 * s - r) := by nlinarith
  by_cases hA : 1 + P * q * E ^ 2 - 2 * r * q * E ≤ 0
  · have : 0 ≤ 8 / 25 * (q * E) * (2 * s - r) := by
      have : 0 ≤ 2 * s - r := by linarith
      positivity
    nlinarith
  · push Not at hA
    have h5 := mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ 1 + ε)
    have h6 := mul_le_mul_of_nonneg_left h4 hqE.le
    nlinarith

/-- `P E² - 2 r E ≤ (301/1000) s` for `E ≤ 548/1000`. -/
theorem phi_rest {s r P E : ℝ} (hrs : r < s) (hr : 1 ≤ r) (hP : P = s + 2 * r - 1)
    (hE0 : 0 < E) (hE : E ≤ 548 / 1000) : P * E ^ 2 - 2 * r * E ≤ 301 / 1000 * s := by
  by_cases h : P * E - 2 * r ≤ 0
  · have : E * (P * E - 2 * r) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hE0.le h
    nlinarith
  · push Not at h
    have h1 : E * (P * E - 2 * r) ≤ 548 / 1000 * (P * E - 2 * r) :=
      mul_le_mul_of_nonneg_right hE h.le
    have h2 : P * E ≤ P * (548 / 1000) := mul_le_mul_of_nonneg_left hE (by rw [hP]; linarith)
    nlinarith

/-- The core of regime `Φ`: `PQ(w) + M(w) ≥ s + s P q E²` for every `w ≥ 0`. -/
theorem phi_key {s r P q E Q ε w μ β M0 T : ℝ} (hs150 : 150 ≤ s) (hsr : r < s) (hr : 1 ≤ r)
    (hPs : P = s + 2 * r - 1) (hq3 : 3 / 10 ≤ q) (hq1 : q ≤ 1) (hE0 : 0 < E)
    (hE : E ≤ 548 / 1000) (hPE : 17 ≤ P * E) (hε0 : 0 ≤ ε) (hε : ε ≤ 3 / 1000)
    (hQ : 29 / 40 ≤ Q) (hw : 0 ≤ w) (hμ : μ = r / s * (1 + ε)) (hβ : β = 1 - r / (2 * s))
    (hM0 : M0 = 2 * r * s * (q * E)) (hT : T = s + s * P * (q * E ^ 2)) :
    T ≤ s ^ 2 * Q * exp (-(μ * w)) + M0 * exp (β * w) := by
  have hspos : 0 < s := by linarith
  have hq0 : 0 < q := by linarith
  have hβ0 : 0 < β := by
    rw [hβ, sub_pos, div_lt_one (by positivity)]; linarith
  have hM0pos : 0 < M0 := by rw [hM0]; positivity
  have hMM0 : M0 ≤ M0 * exp (β * w) :=
    le_mul_of_one_le_right hM0pos.le (one_le_exp (mul_nonneg hβ0.le hw))
  have hPQ0 : 0 ≤ s ^ 2 * Q * exp (-(μ * w)) := by
    have : 0 ≤ Q := by linarith
    positivity
  by_cases hTM : T ≤ M0
  · linarith
  push Not at hTM
  have hZ : 0 < T / M0 := div_pos (by linarith) hM0pos
  by_cases hw1 : log (T / M0) ≤ β * w
  · -- `M` alone reaches `T`.
    have h1 : T / M0 ≤ exp (β * w) := by
      rw [← exp_log hZ]; exact exp_le_exp.mpr hw1
    have h2 := mul_le_mul_of_nonneg_left h1 hM0pos.le
    rw [mul_div_cancel₀ _ hM0pos.ne'] at h2
    linarith
  -- Otherwise `PQ` is still large.
  push Not at hw1
  have hlog := log_le_sub_one_of_pos hZ
  have hμ0 : 0 ≤ μ := by rw [hμ]; positivity
  have hμw : μ * w * β ≤ μ * (T / M0 - 1) := by
    have h1 := mul_le_mul_of_nonneg_left hw1.le hμ0
    have h2 := mul_le_mul_of_nonneg_left hlog hμ0
    calc μ * w * β = μ * (β * w) := by ring
      _ ≤ _ := h1.trans h2
  have hγ := phi_gamma hs150 hsr hr hPs hq3 hE0 hE hPE hε0 hε
  have hqE : 0 < q * E := by positivity
  have hcl : μ * (T / M0 - 1) ≤ 8 / 25 * β := by
    have e1 : μ * (T / M0 - 1) =
        (1 + ε) * (1 + P * q * E ^ 2 - 2 * r * q * E) / (2 * s * (q * E)) := by
      rw [hμ, hT, hM0]; field_simp
    have e3 : 8 / 25 * β = 8 / 25 * (q * E) * (2 * s - r) / (2 * s * (q * E)) := by
      rw [hβ]; field_simp
    rw [e1, e3]
    exact div_le_div_of_nonneg_right hγ (by positivity)
  have hμw' : μ * w ≤ 8 / 25 := by
    have : μ * w * β ≤ 8 / 25 * β := by linarith
    exact le_of_mul_le_mul_right this hβ0
  have hexp : 17 / 25 ≤ exp (-(μ * w)) := by
    have := one_sub_le_exp_neg (μ * w); linarith
  have hrest := phi_rest hsr hr hPs hE0 hE
  have hTM0 : T - M0 ≤ s * (1 + 301 / 1000 * s) := by
    have e : T - M0 = s * (1 + q * (P * E ^ 2 - 2 * r * E)) := by rw [hT, hM0]; ring
    rw [e]
    have h1 : q * (P * E ^ 2 - 2 * r * E) ≤ 301 / 1000 * s := by
      by_cases h : P * E ^ 2 - 2 * r * E ≤ 0
      · have : q * (P * E ^ 2 - 2 * r * E) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hq0.le h
        linarith
      · push Not at h
        have := mul_le_mul_of_nonneg_right hq1 h.le
        linarith
    exact mul_le_mul_of_nonneg_left (by linarith) hspos.le
  have h1 : s ^ 2 * Q * (17 / 25) ≤ s ^ 2 * Q * exp (-(μ * w)) :=
    mul_le_mul_of_nonneg_left hexp (by have : 0 ≤ Q := by linarith
                                       positivity)
  have h2 : s * (1 + 301 / 1000 * s) ≤ s * (s * (29 / 40) * (17 / 25)) :=
    mul_le_mul_of_nonneg_left (by linarith) hspos.le
  have h3 : s ^ 2 * (17 / 25) * (29 / 40) ≤ s ^ 2 * (17 / 25) * Q :=
    mul_le_mul_of_nonneg_left hQ (by positivity)
  have e4 : s * (s * (29 / 40) * (17 / 25)) = s ^ 2 * (17 / 25) * (29 / 40) := by ring
  have e5 : s ^ 2 * Q * (17 / 25) = s ^ 2 * (17 / 25) * Q := by ring
  linarith

theorem regimePhi {k r x η lam w : ℝ} (H : Hyp k x η lam) (hr : 1 ≤ r) (hrs : 2 * r < k)
    (ha : exp (-x) ≤ 3 / 10) (hb : 1 ≤ (k + r - 1) * exp (-x)) (hw : 0 ≤ w) :
    target k x η ≤ lowerG k r x η lam w := by
  have hk := H.hk
  have hE0 : 0 < exp (-(x / 2)) := exp_pos _
  have hE2 : exp (-(x / 2)) ^ 2 = exp (-x) := exp_E_sq x
  have hE : exp (-(x / 2)) ≤ 548 / 1000 := by nlinarith
  have hq0 : 0 < exp (-η) := exp_pos _
  have hq1 : exp (-η) ≤ 1 := exp_le_one_iff.mpr (by linarith [H.hη])
  have hQ : 29 / 40 ≤ exp (-(η / 4)) := by linarith [H.hη1, H.Q_ge]
  have hε0 : 0 ≤ 3 * lam / 4 := by have := H.hl0; positivity
  have hε : 3 * lam / 4 ≤ 3 / 1000 := by
    have h1 : lam * 298 ≤ lam * (k - 2) := mul_le_mul_of_nonneg_left (by linarith) H.hl0
    linarith [H.hl1]
  have hPE : 17 ≤ (k + r - 1) * exp (-(x / 2)) := by
    have h1 : 300 ≤ ((k + r - 1) * exp (-(x / 2))) ^ 2 := by
      have : ((k + r - 1) * exp (-(x / 2))) ^ 2 = (k + r - 1) * ((k + r - 1) * exp (-x)) := by
        rw [← hE2]; ring
      rw [this]; nlinarith
    nlinarith [mul_pos (by linarith : (0 : ℝ) < k + r - 1) hE0]
  have key := phi_key (s := k - r) (r := r) (P := k + r - 1) (w := w) (by linarith) (by linarith) hr
    (by ring) H.q_ge_three_tenths hq1 hE0 hE hPE hε0 hε hQ hw rfl rfl rfl rfl
  -- `D ≥ r` and `O ≥ r (r - 1) q E²`.
  have tD : r ≤ r * exp w := le_mul_of_one_le_right (by linarith) (one_le_exp hw)
  have tO : r * (r - 1) * (exp (-η) * exp (-(x / 2)) ^ 2) ≤
      r * (r - 1) * exp (-x - η + (2 + lam) * w) := by
    rw [exp_split_O]
    have h1 : 1 ≤ exp ((2 + lam) * w) := one_le_exp (mul_nonneg (by linarith [H.hl0]) hw)
    have h3 : 0 ≤ r * (r - 1) * (exp (-η) * exp (-(x / 2)) ^ 2) := by
      have : 0 ≤ r * (r - 1) := mul_nonneg (by linarith) (by linarith)
      positivity
    calc r * (r - 1) * (exp (-η) * exp (-(x / 2)) ^ 2)
        ≤ r * (r - 1) * (exp (-η) * exp (-(x / 2)) ^ 2) * exp ((2 + lam) * w) :=
          le_mul_of_one_le_right h3 h1
      _ = _ := by ring
  have hlow : lowerG k r x η lam w = r * exp w +
      (k - r) ^ 2 * exp (-(η / 4)) * exp (-(r / (k - r) * (1 + 3 * lam / 4) * w)) +
      r * (r - 1) * exp (-x - η + (2 + lam) * w) +
      2 * r * (k - r) * (exp (-η) * exp (-(x / 2))) *
        exp ((1 - r / (2 * (k - r))) * w) := by
    have e1 := exp_split_PQ η (r / (k - r) * (1 + 3 * lam / 4) * w)
    have e2 := exp_split_M x η ((1 - r / (2 * (k - r))) * w)
    simp only [lowerG]
    rw [e1, e2]
    ring
  have htarget : target k x η = r + r * (r - 1) * (exp (-η) * exp (-(x / 2)) ^ 2) +
      ((k - r) + (k - r) * (k + r - 1) * (exp (-η) * exp (-(x / 2)) ^ 2)) := by
    simp only [target, exp_split_target]; ring
  rw [hlow, htarget]
  linarith

end RegimePhi

/-! ### Regime `V`: `r < s`, `e^{-x} ≤ 1/(k + r - 1)`, split between `D` and `PQ` -/

section RegimeV

/-- `e^{-301/100} ≥ 1/21`. -/
theorem exp_neg_three_le : 1 / 21 ≤ exp (-(301 / 100)) := by
  have h1 : exp (301 / 100) = exp 1 ^ 3 * exp (1 / 100) := by
    rw [← exp_nat_mul, ← exp_add]; norm_num
  have he := exp_one_lt_d9
  have ht : exp (1 / 100) ≤ 100 / 99 := by
    have h := one_sub_le_exp_neg (1 / 100)
    have hm : exp (1 / 100) * exp (-(1 / 100)) = 1 := by rw [← exp_add]; simp
    nlinarith [exp_pos (1 / 100), exp_pos (-(1 / 100))]
  have he3 : exp 1 ^ 3 ≤ 2.7182818286 ^ 3 := by
    exact pow_le_pow_left₀ (exp_pos 1).le he.le 3
  have hle : exp (301 / 100) ≤ 21 := by
    rw [h1]
    calc exp 1 ^ 3 * exp (1 / 100) ≤ 2.7182818286 ^ 3 * (100 / 99) :=
          mul_le_mul he3 ht (exp_pos _).le (by norm_num)
      _ ≤ 21 := by norm_num
  rw [exp_neg, one_div]
  exact inv_anti₀ (exp_pos _) hle

/-- Regime `V` needs no sign condition on `w`. -/
theorem regimeV {k r x η lam w : ℝ} (H : Hyp k x η lam) (hr : 1 ≤ r) (hrs : 2 * r < k)
    (hb : (k + r - 1) * exp (-x) ≤ 1) : target k x η ≤ lowerG k r x η lam w := by
  have hk := H.hk
  set s := k - r with hs
  have hsr : r < s := by linarith
  have hspos : 0 < s := by linarith
  set E := exp (-(x / 2)) with hEdef
  set q := exp (-η) with hqdef
  set Q := exp (-(η / 4)) with hQdef
  set ε := 3 * lam / 4 with hεdef
  have hE0 : 0 < E := exp_pos _
  have hq0 : 0 < q := exp_pos _
  have hq1 : q ≤ 1 := exp_le_one_iff.mpr (by linarith [H.hη])
  have hQge : 1 - η / 4 ≤ Q := H.Q_ge
  have hQ : 29 / 40 ≤ Q := by linarith [H.hη1]
  have hε0 : 0 ≤ ε := by have := H.hl0; positivity
  have hε : ε ≤ 3 / 1000 := by
    have h1 : lam * 298 ≤ lam * (k - 2) := mul_le_mul_of_nonneg_left (by linarith) H.hl0
    rw [hεdef]; linarith [H.hl1]
  have ha0 : 0 < exp (-x) := exp_pos _
  -- The target is at most `2k`.
  have htarget : target k x η ≤ 2 * k := by
    have h1 : exp (-x - η) ≤ exp (-x) := exp_le_exp.mpr (by linarith [H.hη])
    have h2 : (k - 1) * exp (-x) ≤ 1 := by nlinarith
    have h3 : k * (k - 1) * exp (-x - η) ≤ k * (k - 1) * exp (-x) :=
      mul_le_mul_of_nonneg_left h1 (by nlinarith)
    simp only [target]; nlinarith
  set μ := r / s * (1 + ε) with hμdef
  have hlow : r * exp w + s ^ 2 * Q * exp (-(μ * w)) ≤ lowerG k r x η lam w := by
    have hO : 0 ≤ r * (r - 1) * exp (-x - η + (2 + lam) * w) := by
      have : 0 ≤ r * (r - 1) := by nlinarith
      positivity
    have hM : 0 ≤ 2 * r * s * exp (-(x / 2) - η + (1 - r / (2 * s)) * w) := by positivity
    have e : lowerG k r x η lam w = r * exp w + s ^ 2 * Q * exp (-(μ * w)) +
        r * (r - 1) * exp (-x - η + (2 + lam) * w) +
        2 * r * s * exp (-(x / 2) - η + (1 - r / (2 * s)) * w) := by
      simp only [lowerG, hs, hεdef, hμdef, hQdef]
      rw [exp_split_PQ]; ring_nf
    linarith
  refine htarget.trans (le_trans ?_ hlow)
  have hPQ0 : 0 ≤ s ^ 2 * Q * exp (-(μ * w)) := by positivity
  by_cases hw2 : log (2 * k / r) ≤ w
  · have : 2 * k / r ≤ exp w := by
      rw [← exp_log (by positivity : 0 < 2 * k / r)]; exact exp_le_exp.mpr hw2
    have := mul_le_mul_of_nonneg_left this (by linarith : (0 : ℝ) ≤ r)
    rw [mul_div_cancel₀ _ (by linarith : (r : ℝ) ≠ 0)] at this
    have : 0 ≤ r * exp w := by positivity
    linarith
  · push Not at hw2
    have hlog := log_le_sub_one_of_pos (by positivity : 0 < 2 * k / r)
    have hμ0 : 0 ≤ μ := by positivity
    have hμw : μ * w ≤ 301 / 100 := by
      have h1 : μ * w ≤ μ * (2 * k / r - 1) := by
        have := mul_le_mul_of_nonneg_left hw2.le hμ0
        nlinarith
      have h2 : μ * (2 * k / r - 1) = (1 + ε) * ((2 * k - r) / s) := by
        rw [hμdef]; field_simp
      have h3 : (2 * k - r) / s ≤ 3 := by
        rw [div_le_iff₀ hspos]; linarith
      have h4 : (1 + ε) * ((2 * k - r) / s) ≤ (1 + 3 / 1000) * 3 :=
        mul_le_mul (by linarith) h3 (div_nonneg (by linarith) hspos.le) (by norm_num)
      linarith
    have hexp : 1 / 21 ≤ exp (-(μ * w)) :=
      exp_neg_three_le.trans (exp_le_exp.mpr (by linarith))
    have h1 : s ^ 2 * Q * (1 / 21) ≤ s ^ 2 * Q * exp (-(μ * w)) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    have h2 : 2 * k ≤ s ^ 2 * Q * (1 / 21) := by
      have hs2 : k / 2 ≤ s := by linarith
      have h3 : (k / 2) ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (by linarith) hs2 2
      have h4 : (k / 2) ^ 2 * (29 / 40) ≤ s ^ 2 * Q := mul_le_mul h3 hQ (by norm_num) (by positivity)
      nlinarith
    have : 0 ≤ r * exp w := by positivity
    linarith

end RegimeV

/-! ### The case `r = 0` -/

theorem target_le_zero {k x η lam : ℝ} (H : Hyp k x η lam) :
    target k x η ≤ k ^ 2 * exp (-(η / 4)) := by
  have hk := H.hk
  set E := exp (-(x / 2)) with hEdef
  set q := exp (-η) with hqdef
  set Q := exp (-(η / 4)) with hQdef
  have hE2 : E ^ 2 = exp (-x) := exp_E_sq x
  have hqQ : q ≤ Q := H.q_le_Q
  have hQge : 1 - η / 4 ≤ Q := H.Q_ge
  have hQ : 29 / 40 ≤ Q := by linarith [H.hη1]
  have hone := H.one_sub_a
  rw [← hE2] at hone
  set D := 1 - E ^ 2 with hD
  have hD1 : D ≤ 1 := by rw [hD]; nlinarith [sq_nonneg E]
  have hD0 : 0 ≤ D := by nlinarith [H.hx]
  -- `(k - 1) D (1 - η/4) ≥ η / 4`.
  have hmain : η / 4 ≤ (k - 1) * D * (1 - η / 4) := by
    have hη298 : η * 298 ≤ x := by nlinarith [H.hηx, H.hη]
    by_cases hx1 : x ≤ 1
    · have h1 : x / 2 ≤ D := by nlinarith
      have h2 : (k - 1) * (x / 2) * (29 / 40) ≤ (k - 1) * D * (1 - η / 4) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left h1 (by linarith)) (by linarith [H.hη1])
          (by norm_num) (mul_nonneg (by linarith) hD0)
      nlinarith [H.hx]
    · push Not at hx1
      have h1 : 1 / 2 ≤ D := by nlinarith
      have h2 : (k - 1) * (1 / 2) * (29 / 40) ≤ (k - 1) * D * (1 - η / 4) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left h1 (by linarith)) (by linarith [H.hη1])
          (by norm_num) (mul_nonneg (by linarith) hD0)
      nlinarith [H.hη1]
  have e : k ^ 2 * Q - target k x η ≥ k * (Q * (1 + (k - 1) * D) - 1) := by
    simp only [target, exp_split_target, hD]
    have : k * (k - 1) * (q * E ^ 2) ≤ k * (k - 1) * (Q * E ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hqQ (sq_nonneg E)) (by nlinarith)
    nlinarith
  have h2 : 0 ≤ Q * (1 + (k - 1) * D) - 1 := by
    have : (1 - η / 4) * (1 + (k - 1) * D) ≤ Q * (1 + (k - 1) * D) :=
      mul_le_mul_of_nonneg_right hQge (by nlinarith)
    nlinarith
  have := mul_nonneg (by linarith : (0 : ℝ) ≤ k) h2
  linarith

/-! ### The inequality -/

/-- **The analytic inequality**: for `k ≥ 300`, `1 ≤ r ≤ k - 2` and every `w ≥ 0`, the class lower
bound dominates the constant count. -/
theorem target_le_lowerG {k r x η lam w : ℝ} (H : Hyp k x η lam) (hr : 1 ≤ r) (hrk : r ≤ k - 2)
    (hw : 0 ≤ w) : target k x η ≤ lowerG k r x η lam w := by
  by_cases hA : 3 / 10 ≤ exp (-x)
  · exact regimeA H hr hrk hA hw
  push Not at hA
  by_cases hsr : k ≤ 2 * r
  · exact regimePsi H hsr hrk hA.le hw
  push Not at hsr
  by_cases hb : 1 ≤ (k + r - 1) * exp (-x)
  · exact regimePhi H hr hsr hA.le hb hw
  · push Not at hb
    exact regimeV H hr hsr hb.le

end SimpleGraph.TwoDegenerate.K2nSqrt
