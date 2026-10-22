/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# The bookkeeping of one colour at `k = 7`

A colour mismatched at an edge is made to agree by a move through the hole of its star. The star is
deleted just before (`card_unpair`: the count grows by the star's hit event `E`), and the move
loses at most its bad set, which is at most `θ·E` (absorbed) plus `ε·Z` (residual). Three cases:

* **H**: the star pays the whole move. With `E ≥ γ·Z₀` (the box bound) and
  `(1 - ε - θ)·γ ≥ ε·(1 - γ)`, the count does not drop (`step_H`).
* **D**: the move owns a unit of the old column's vertical difference, which pays `1 - γ_V`; with
  `ε ≤ γ_V` (`step_D`).
* **Double**: the star serves two moves, the second through the same hole after the first; its hit
  event drifts by at most `1 + δ` in between. Star and unit together pay
  `(1 - ε)² + ((1 - ε)² - (1 - ε)·θ - θ·(1 + δ))·γ ≥ 1 - γ_V` (`step_double`).

All three are inequalities between rationals; the counts enter as hypotheses.
-/

namespace GridGen.Gauge

/-- **An H-move.** `Z₀ = Z₋ + E` after the deletion, `E ≥ γ Z₀`, and the move keeps
`Z₁ ≥ Z₀ - θ E - ε Z₀`. -/
theorem step_H {Zm Z0 Z1 E γ θ ε : ℚ} (hZm : 0 ≤ Zm) (hE0 : 0 ≤ E) (hdel : Z0 = Zm + E)
    (hγ : γ * Z0 ≤ E) (hmove : Z0 - θ * E - ε * Z0 ≤ Z1) (hε : 0 ≤ ε) (hγ1 : γ < 1)
    (hcond : ε * (1 - γ) ≤ (1 - ε - θ) * γ) (hθ : θ ≤ 1 - ε) : Zm ≤ Z1 := by
  subst hdel
  -- `E ≥ γ/(1-γ) Zm`
  have hE : γ * Zm ≤ (1 - γ) * E := by nlinarith
  have h1 : Z1 ≥ (1 - ε) * Zm + (1 - ε - θ) * E := by nlinarith
  have h2 : (1 - ε - θ) * γ * Zm ≤ (1 - ε - θ) * ((1 - γ) * E) :=
    mul_le_mul_of_nonneg_left hE (by linarith) |>.trans_eq' (by ring)
  have hg : 0 < 1 - γ := by linarith
  -- multiply the target by `1 - γ`
  have : (1 - γ) * Zm ≤ (1 - γ) * Z1 := by nlinarith
  exact le_of_mul_le_mul_left this hg

/-- **A D-move.** -/
theorem step_D {Zm Z0 Z1 E θ ε γV : ℚ} (hZm : 0 ≤ Zm) (hE0 : 0 ≤ E) (hdel : Z0 = Zm + E)
    (hmove : Z0 - θ * E - ε * Z0 ≤ Z1) (hθ : θ ≤ 1 - ε) (hεV : ε ≤ γV) :
    (1 - γV) * Zm ≤ Z1 := by
  subst hdel
  nlinarith

/-- **A double.** The deletion, the first move (in the cover `Z₀`), the second move (after the
drift `E₁ ≤ (1 + δ) E`). -/
theorem step_double {Zm Z0 Z1 Z2 E E1 γ θ ε δ γV : ℚ} (hZm : 0 ≤ Zm) (hE0 : 0 ≤ E)
    (hdel : Z0 = Zm + E) (hγ : γ * Z0 ≤ E) (hm1 : Z0 - θ * E - ε * Z0 ≤ Z1)
    (hm2 : Z1 - θ * E1 - ε * Z1 ≤ Z2) (hdrift : E1 ≤ (1 + δ) * E) (hθ0 : 0 ≤ θ) (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1) (hγ0 : 0 ≤ γ)
    (hcoef : 0 ≤ (1 - ε) ^ 2 - (1 - ε) * θ - θ * (1 + δ))
    (hcond : 1 - γV ≤ (1 - ε) ^ 2 + ((1 - ε) ^ 2 - (1 - ε) * θ - θ * (1 + δ)) * γ) :
    (1 - γV) * Zm ≤ Z2 := by
  subst hdel
  have hZ1 : (1 - ε) * (Zm + E) - θ * E ≤ Z1 := by linarith
  have hZ2 : (1 - ε) * Z1 - θ * E1 ≤ Z2 := by linarith
  have hE1 : θ * E1 ≤ θ * ((1 + δ) * E) := mul_le_mul_of_nonneg_left hdrift hθ0
  have h1e : 0 ≤ 1 - ε := by linarith
  have hZ1' : (1 - ε) * ((1 - ε) * (Zm + E) - θ * E) ≤ (1 - ε) * Z1 :=
    mul_le_mul_of_nonneg_left hZ1 h1e
  -- `Z₂ ≥ (1-ε)² Zm + coef · E` and `E ≥ γ Zm`
  have hEZ : γ * Zm ≤ E := by nlinarith
  have hc : ((1 - ε) ^ 2 - (1 - ε) * θ - θ * (1 + δ)) * (γ * Zm) ≤
      ((1 - ε) ^ 2 - (1 - ε) * θ - θ * (1 + δ)) * E := mul_le_mul_of_nonneg_left hEZ hcoef
  have hmain : (1 - ε) ^ 2 * Zm + ((1 - ε) ^ 2 - (1 - ε) * θ - θ * (1 + δ)) * E ≤ Z2 := by
    nlinarith
  have hfin : (1 - γV) * Zm ≤ ((1 - ε) ^ 2 + ((1 - ε) ^ 2 - (1 - ε) * θ - θ * (1 + δ)) * γ) * Zm :=
    mul_le_mul_of_nonneg_right hcond hZm
  nlinarith

end GridGen.Gauge
