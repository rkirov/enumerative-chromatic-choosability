/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.State

/-!
# Height four: constants of the averaged gain

The averaged fibre ratio `qk` and the quadratic lower bound for the logarithm (`log_quad`). The
averaged gain at `k = 6` (`F6val`, `F6cap`) is in `Seam6.lean` and checked in `Cert6.lean`. (For
`k ≥ 7` every grid is ECC by the gauge route, `GridGen/Gauge/`, so the averaged gains and
certificates for `k ≥ 7` that once lived here were removed.)
-/

namespace GridGen.Four

open Real

/-- The averaged fibre ratio `q = 1/(ρ(k-3))`. -/
noncomputable def qk (k : ℕ) : ℝ := 1 / (rho k * ((k - 3 : ℕ) : ℝ))

/-- `log (1 + x/A) ≥ x/A - x²/(2A²)`. -/
theorem log_quad {x A : ℝ} (hx : 0 ≤ x) (hA : 0 < A) :
    x / A - x ^ 2 / (2 * A ^ 2) ≤ log (1 + x / A) := by
  have := log_one_add_ge (div_nonneg hx hA.le)
  have e : x / A - (x / A) ^ 2 / 2 = x / A - x ^ 2 / (2 * A ^ 2) := by field_simp
  linarith

end GridGen.Four
