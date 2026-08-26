/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Tactic

/-!
# The arithmetic of the `(C1_r)` pair lemma

Pure integer inequalities, with no lists in sight. `k ≥ 5`, list sizes `x, z ∈ [k-2, k]` for two
colours differing by at most one, `t = |M \ T|`, `b = |M \ B|`, indicators `M, p, q ∈ {0, 1}`
of `y ∈ M`, `y ∈ M \ T`, `y ∈ M \ B`. `pairC_arith` is the inequality
`cc·(Λ y₁ + Λ y₂) + RL y₁ + RL y₂ ≥ 0` of `Grid3.PairC`; it is linear in `t` and `b`, and the
coefficient lemmas are the sub-claims.
-/

namespace Grid3

-- sub-claim: coefficient of t' (the part of t beyond p₁+p₂) is nonnegative
theorem Ft_nonneg (k x₁ z₁ x₂ z₂ μ₁ μ₂ : ℤ) (hk : 5 ≤ k) (hx1 : k - 2 ≤ x₁) (hx1' : x₁ ≤ k)
    (hz1 : k - 2 ≤ z₁) (hz1' : z₁ ≤ k) (hx2 : k - 2 ≤ x₂) (hx2' : x₂ ≤ k) (hz2 : k - 2 ≤ z₂) (hz2' : z₂ ≤ k)
    (hμ1 : μ₁ ≤ k) (hμ2 : μ₂ ≤ k) :
    0 ≤ (k - 2) * ((k - 1) * (k - 2) + 1) * (((k - 2) * z₁ * (x₁ - 1) - 1) + ((k - 2) * z₂ * (x₂ - 1) - 1))
        - x₁ * z₁ * μ₁ - x₂ * z₂ * μ₂ - z₁ - z₂ := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 5 := ⟨k - 5, by omega⟩
  have hm : 0 ≤ m := by omega
  have h1 : 0 ≤ x₁ - 1 := by omega
  have h2 : 0 ≤ x₂ - 1 := by omega
  have hz10 : 0 ≤ z₁ := by omega
  have hz20 : 0 ≤ z₂ := by omega
  have hx10 : 0 ≤ x₁ := by omega
  have hx20 : 0 ≤ x₂ := by omega
  have e1 : x₁ * z₁ * μ₁ ≤ x₁ * z₁ * (m + 5) := by
    apply mul_le_mul_of_nonneg_left hμ1 (mul_nonneg hx10 hz10)
  have e2 : x₂ * z₂ * μ₂ ≤ x₂ * z₂ * (m + 5) := by
    apply mul_le_mul_of_nonneg_left hμ2 (mul_nonneg hx20 hz20)
  nlinarith [mul_nonneg hm hz10, mul_nonneg hm hx10, mul_nonneg (mul_nonneg hm hm) hz10,
    mul_nonneg (mul_nonneg hz10 h1) hm, mul_nonneg (mul_nonneg hz20 h2) hm,
    mul_nonneg (mul_nonneg (mul_nonneg hz10 h1) hm) hm, mul_nonneg (mul_nonneg (mul_nonneg hz20 h2) hm) hm,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hz10 h1) hm) hm) hm,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hz20 h2) hm) hm) hm,
    mul_nonneg hz10 h1, mul_nonneg hz20 h2]

-- sub-claim: the p₁-coefficient is nonnegative (CT₁ ≥ 0), including the μ-deficits
theorem CT_nonneg (k x₁ z₁ x₂ z₂ μ₁ μ₂ : ℤ) (hk : 5 ≤ k) (hx1 : k - 2 ≤ x₁) (hx1' : x₁ ≤ k)
    (hz1 : k - 2 ≤ z₁) (hz1' : z₁ ≤ k) (hx2 : k - 2 ≤ x₂) (hx2' : x₂ ≤ k) (hz2 : k - 2 ≤ z₂) (hz2' : z₂ ≤ k)
    (c1 : x₁ ≤ x₂ + 1) (c2 : z₁ ≤ z₂ + 1) (hμ1 : μ₁ ≤ k) (hμ2 : μ₂ ≤ k) :
    0 ≤ (k - 2) * ((k - 1) * (k - 2) + 1) * (((k - 2) * z₂ * (x₂ - 1) - 1) - ((k - 2) * z₁ + 1))
        - x₁ * z₁ * μ₁ - x₂ * z₂ * μ₂ - z₁ - z₂ := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 5 := ⟨k - 5, by omega⟩
  obtain ⟨ξ, rfl⟩ : ∃ ξ, x₂ = m + 3 + ξ := ⟨x₂ - m - 3, by omega⟩
  obtain ⟨ζ, rfl⟩ : ∃ ζ, z₂ = m + 3 + ζ := ⟨z₂ - m - 3, by omega⟩
  have hm : 0 ≤ m := by omega
  have hξ : 0 ≤ ξ := by omega
  have hζ : 0 ≤ ζ := by omega
  have hx1'' : x₁ ≤ m + 4 + ξ := by omega
  have hz1'' : z₁ ≤ m + 4 + ζ := by omega
  have hx10 : 0 ≤ x₁ := by omega
  have hz10 : 0 ≤ z₁ := by omega
  have e1 : x₁ * z₁ * μ₁ ≤ (m + 4 + ξ) * (m + 4 + ζ) * (m + 5) := by
    calc x₁ * z₁ * μ₁ ≤ x₁ * z₁ * (m + 5) := mul_le_mul_of_nonneg_left hμ1 (mul_nonneg hx10 hz10)
      _ ≤ (m + 4 + ξ) * (m + 4 + ζ) * (m + 5) :=
          mul_le_mul_of_nonneg_right (mul_le_mul hx1'' hz1'' hz10 (by omega)) (by omega)
  have e2 : (m + 3 + ξ) * (m + 3 + ζ) * μ₂ ≤ (m + 3 + ξ) * (m + 3 + ζ) * (m + 5) :=
    mul_le_mul_of_nonneg_left hμ2 (mul_nonneg (by omega) (by omega))
  nlinarith [mul_nonneg hm hξ, mul_nonneg hm hζ, mul_nonneg hξ hζ, mul_nonneg (mul_nonneg hm hm) hm,
    mul_nonneg (mul_nonneg hm hm) hξ, mul_nonneg (mul_nonneg hm hm) hζ,
    mul_nonneg (mul_nonneg hm hξ) hζ, mul_nonneg (mul_nonneg (mul_nonneg hm hm) hm) hm,
    mul_nonneg (mul_nonneg (mul_nonneg hm hm) hm) hξ, mul_nonneg (mul_nonneg (mul_nonneg hm hm) hm) hζ,
    mul_nonneg (mul_nonneg (mul_nonneg hm hm) hξ) hζ, mul_nonneg hz10 hm]

theorem Fb_nonneg (k x₁ z₁ x₂ z₂ μ₁ μ₂ : ℤ) (hk : 5 ≤ k) (hx1 : k - 2 ≤ x₁) (hx1' : x₁ ≤ k)
    (hz1 : k - 2 ≤ z₁) (hz1' : z₁ ≤ k) (hx2 : k - 2 ≤ x₂) (hx2' : x₂ ≤ k) (hz2 : k - 2 ≤ z₂) (hz2' : z₂ ≤ k)
    (hμ1 : μ₁ ≤ k) (hμ2 : μ₂ ≤ k) :
    0 ≤ (k - 2) * ((k - 1) * (k - 2) + 1) * ((k - 2) * x₁ * (z₁ - 1) + (k - 2) * x₂ * (z₂ - 1))
        - x₁ * z₁ * μ₁ - x₂ * z₂ * μ₂ - x₁ - x₂ := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 5 := ⟨k - 5, by omega⟩
  have hm : 0 ≤ m := by omega
  have h1 : 0 ≤ z₁ - 1 := by omega
  have h2 : 0 ≤ z₂ - 1 := by omega
  have hz10 : 0 ≤ z₁ := by omega
  have hz20 : 0 ≤ z₂ := by omega
  have hx10 : 0 ≤ x₁ := by omega
  have hx20 : 0 ≤ x₂ := by omega
  have e1 : x₁ * z₁ * μ₁ ≤ x₁ * z₁ * (m + 5) := mul_le_mul_of_nonneg_left hμ1 (mul_nonneg hx10 hz10)
  have e2 : x₂ * z₂ * μ₂ ≤ x₂ * z₂ * (m + 5) := mul_le_mul_of_nonneg_left hμ2 (mul_nonneg hx20 hz20)
  nlinarith [mul_nonneg hm hx10, mul_nonneg hm hz10, mul_nonneg (mul_nonneg hm hm) hx10,
    mul_nonneg (mul_nonneg hx10 h1) hm, mul_nonneg (mul_nonneg hx20 h2) hm,
    mul_nonneg (mul_nonneg (mul_nonneg hx10 h1) hm) hm, mul_nonneg (mul_nonneg (mul_nonneg hx20 h2) hm) hm,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hx10 h1) hm) hm) hm,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hx20 h2) hm) hm) hm,
    mul_nonneg hx10 h1, mul_nonneg hx20 h2]

theorem CB_nonneg (k x₁ z₁ x₂ z₂ μ₁ μ₂ : ℤ) (hk : 5 ≤ k) (hx1 : k - 2 ≤ x₁) (hx1' : x₁ ≤ k)
    (hz1 : k - 2 ≤ z₁) (hz1' : z₁ ≤ k) (hx2 : k - 2 ≤ x₂) (hx2' : x₂ ≤ k) (hz2 : k - 2 ≤ z₂) (hz2' : z₂ ≤ k)
    (c1 : x₁ ≤ x₂ + 1) (c2 : z₁ ≤ z₂ + 1) (hμ1 : μ₁ ≤ k) (hμ2 : μ₂ ≤ k) :
    0 ≤ (k - 2) * ((k - 1) * (k - 2) + 1) * ((k - 2) * x₂ * (z₂ - 1) - (k - 2) * x₁)
        - x₁ * z₁ * μ₁ - x₂ * z₂ * μ₂ - x₁ - x₂ := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 5 := ⟨k - 5, by omega⟩
  obtain ⟨ξ, rfl⟩ : ∃ ξ, x₂ = m + 3 + ξ := ⟨x₂ - m - 3, by omega⟩
  obtain ⟨ζ, rfl⟩ : ∃ ζ, z₂ = m + 3 + ζ := ⟨z₂ - m - 3, by omega⟩
  have hm : 0 ≤ m := by omega
  have hξ : 0 ≤ ξ := by omega
  have hζ : 0 ≤ ζ := by omega
  have hx1'' : x₁ ≤ m + 4 + ξ := by omega
  have hz1'' : z₁ ≤ m + 4 + ζ := by omega
  have hx10 : 0 ≤ x₁ := by omega
  have hz10 : 0 ≤ z₁ := by omega
  have e1 : x₁ * z₁ * μ₁ ≤ (m + 4 + ξ) * (m + 4 + ζ) * (m + 5) := by
    calc x₁ * z₁ * μ₁ ≤ x₁ * z₁ * (m + 5) := mul_le_mul_of_nonneg_left hμ1 (mul_nonneg hx10 hz10)
      _ ≤ (m + 4 + ξ) * (m + 4 + ζ) * (m + 5) :=
          mul_le_mul_of_nonneg_right (mul_le_mul hx1'' hz1'' hz10 (by omega)) (by omega)
  have e2 : (m + 3 + ξ) * (m + 3 + ζ) * μ₂ ≤ (m + 3 + ξ) * (m + 3 + ζ) * (m + 5) :=
    mul_le_mul_of_nonneg_left hμ2 (mul_nonneg (by omega) (by omega))
  nlinarith [mul_nonneg hm hξ, mul_nonneg hm hζ, mul_nonneg hξ hζ, mul_nonneg (mul_nonneg hm hm) hm,
    mul_nonneg (mul_nonneg hm hm) hξ, mul_nonneg (mul_nonneg hm hm) hζ,
    mul_nonneg (mul_nonneg hm hξ) hζ, mul_nonneg (mul_nonneg (mul_nonneg hm hm) hm) hm,
    mul_nonneg (mul_nonneg (mul_nonneg hm hm) hm) hξ, mul_nonneg (mul_nonneg (mul_nonneg hm hm) hm) hζ,
    mul_nonneg (mul_nonneg (mul_nonneg hm hm) hξ) hζ, mul_nonneg hx10 hm]

/-- The assembled C-side arithmetic lemma. -/
theorem pairC_arith (k t b x₁ z₁ x₂ z₂ M₁ M₂ p₁ p₂ q₁ q₂ : ℤ) (hk : 5 ≤ k)
    (hx1 : k - 2 ≤ x₁) (hx1' : x₁ ≤ k) (hz1 : k - 2 ≤ z₁) (hz1' : z₁ ≤ k)
    (hx2 : k - 2 ≤ x₂) (hx2' : x₂ ≤ k) (hz2 : k - 2 ≤ z₂) (hz2' : z₂ ≤ k)
    (c1 : x₁ ≤ x₂ + 1) (c1' : x₂ ≤ x₁ + 1) (c2 : z₁ ≤ z₂ + 1) (c2' : z₂ ≤ z₁ + 1)
    (hM1 : 0 ≤ M₁) (hM1' : M₁ ≤ 1) (hM2 : 0 ≤ M₂) (hM2' : M₂ ≤ 1)
    (hp1 : 0 ≤ p₁) (hp2 : 0 ≤ p₂) (hq1 : 0 ≤ q₁) (hq2 : 0 ≤ q₂)
    (ht : p₁ + p₂ ≤ t) (hb : q₁ + q₂ ≤ b) :
    0 ≤ (k - 2) * ((k - 1) * (k - 2) + 1)
          * (((k - 2) ^ 2 * (1 - M₁) * x₁ * z₁ + ((k - 2) * z₁ * (x₁ - 1) - 1) * (t - p₁)
                + (k - 2) * x₁ * (z₁ - 1) * (b - q₁) - ((k - 2) * z₁ + 1) * p₁ - (k - 2) * x₁ * q₁)
             + ((k - 2) ^ 2 * (1 - M₂) * x₂ * z₂ + ((k - 2) * z₂ * (x₂ - 1) - 1) * (t - p₂)
                + (k - 2) * x₂ * (z₂ - 1) * (b - q₂) - ((k - 2) * z₂ + 1) * p₂ - (k - 2) * x₂ * q₂))
        + (x₁ * z₁ * ((k - 3) * (1 - M₁) - (k - M₁) * (t + b)) - z₁ * t - x₁ * b)
        + (x₂ * z₂ * ((k - 3) * (1 - M₂) - (k - M₂) * (t + b)) - z₂ * t - x₂ * b) := by
  obtain ⟨t', rfl⟩ : ∃ t', t = p₁ + p₂ + t' := ⟨t - p₁ - p₂, by ring⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = q₁ + q₂ + b' := ⟨b - q₁ - q₂, by ring⟩
  have ht' : 0 ≤ t' := by linarith
  have hb' : 0 ≤ b' := by linarith
  have hμ1 : k - M₁ ≤ k := by linarith
  have hμ2 : k - M₂ ≤ k := by linarith
  have Ft := Ft_nonneg k x₁ z₁ x₂ z₂ (k - M₁) (k - M₂) hk hx1 hx1' hz1 hz1' hx2 hx2' hz2 hz2' hμ1 hμ2
  have Fb := Fb_nonneg k x₁ z₁ x₂ z₂ (k - M₁) (k - M₂) hk hx1 hx1' hz1 hz1' hx2 hx2' hz2 hz2' hμ1 hμ2
  have CT1 := CT_nonneg k x₁ z₁ x₂ z₂ (k - M₁) (k - M₂) hk hx1 hx1' hz1 hz1' hx2 hx2' hz2 hz2' c1 c2 hμ1 hμ2
  have CT2 := CT_nonneg k x₂ z₂ x₁ z₁ (k - M₂) (k - M₁) hk hx2 hx2' hz2 hz2' hx1 hx1' hz1 hz1' c1' c2' hμ2 hμ1
  have CB1 := CB_nonneg k x₁ z₁ x₂ z₂ (k - M₁) (k - M₂) hk hx1 hx1' hz1 hz1' hx2 hx2' hz2 hz2' c1 c2 hμ1 hμ2
  have CB2 := CB_nonneg k x₂ z₂ x₁ z₁ (k - M₂) (k - M₁) hk hx2 hx2' hz2 hz2' hx1 hx1' hz1 hz1' c1' c2' hμ2 hμ1
  have hk2 : 0 ≤ k - 2 := by linarith
  have hk3 : 0 ≤ k - 3 := by linarith
  have hcc : 0 ≤ (k - 2) * ((k - 1) * (k - 2) + 1) := mul_nonneg hk2 (by nlinarith)
  have hx10 : 0 ≤ x₁ := by linarith
  have hz10 : 0 ≤ z₁ := by linarith
  have hx20 : 0 ≤ x₂ := by linarith
  have hz20 : 0 ≤ z₂ := by linarith
  have A1 : 0 ≤ (1 - M₁) * ((k - 2) * ((k - 1) * (k - 2) + 1) * (k - 2) ^ 2 * x₁ * z₁ + x₁ * z₁ * (k - 3)) :=
    mul_nonneg (by linarith) (add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hcc (sq_nonneg _)) hx10) hz10)
      (mul_nonneg (mul_nonneg hx10 hz10) hk3))
  have A2 : 0 ≤ (1 - M₂) * ((k - 2) * ((k - 1) * (k - 2) + 1) * (k - 2) ^ 2 * x₂ * z₂ + x₂ * z₂ * (k - 3)) :=
    mul_nonneg (by linarith) (add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hcc (sq_nonneg _)) hx20) hz20)
      (mul_nonneg (mul_nonneg hx20 hz20) hk3))
  have P1 := mul_nonneg ht' Ft
  have P2 := mul_nonneg hb' Fb
  have P3 := mul_nonneg hp1 CT1
  have P4 := mul_nonneg hp2 CT2
  have P5 := mul_nonneg hq1 CB1
  have P6 := mul_nonneg hq2 CB2
  linarith

/-- `pairC_arith` with the constant `cc` as a named parameter. -/
theorem pairC_arith' (c k t b x₁ z₁ x₂ z₂ M₁ M₂ p₁ p₂ q₁ q₂ : ℤ)
    (hc : c = (k - 2) * ((k - 1) * (k - 2) + 1)) (hk : 5 ≤ k)
    (hx1 : k - 2 ≤ x₁) (hx1' : x₁ ≤ k) (hz1 : k - 2 ≤ z₁) (hz1' : z₁ ≤ k)
    (hx2 : k - 2 ≤ x₂) (hx2' : x₂ ≤ k) (hz2 : k - 2 ≤ z₂) (hz2' : z₂ ≤ k)
    (c1 : x₁ ≤ x₂ + 1) (c1' : x₂ ≤ x₁ + 1) (c2 : z₁ ≤ z₂ + 1) (c2' : z₂ ≤ z₁ + 1)
    (hM1 : 0 ≤ M₁) (hM1' : M₁ ≤ 1) (hM2 : 0 ≤ M₂) (hM2' : M₂ ≤ 1)
    (hp1 : 0 ≤ p₁) (hp2 : 0 ≤ p₂) (hq1 : 0 ≤ q₁) (hq2 : 0 ≤ q₂)
    (ht : p₁ + p₂ ≤ t) (hb : q₁ + q₂ ≤ b) :
    0 ≤ c * (((k - 2) ^ 2 * (1 - M₁) * x₁ * z₁ + ((k - 2) * z₁ * (x₁ - 1) - 1) * (t - p₁)
                + (k - 2) * x₁ * (z₁ - 1) * (b - q₁) - ((k - 2) * z₁ + 1) * p₁ - (k - 2) * x₁ * q₁)
             + ((k - 2) ^ 2 * (1 - M₂) * x₂ * z₂ + ((k - 2) * z₂ * (x₂ - 1) - 1) * (t - p₂)
                + (k - 2) * x₂ * (z₂ - 1) * (b - q₂) - ((k - 2) * z₂ + 1) * p₂ - (k - 2) * x₂ * q₂))
        + (x₁ * z₁ * ((k - 3) * (1 - M₁) - (k - M₁) * (t + b)) - z₁ * t - x₁ * b)
        + (x₂ * z₂ * ((k - 3) * (1 - M₂) - (k - M₂) * (t + b)) - z₂ * t - x₂ * b) := by
  subst hc
  exact pairC_arith k t b x₁ z₁ x₂ z₂ M₁ M₂ p₁ p₂ q₁ q₂ hk hx1 hx1' hz1 hz1' hx2 hx2' hz2 hz2'
    c1 c1' c2 c2' hM1 hM1' hM2 hM2' hp1 hp2 hq1 hq2 ht hb

end Grid3
