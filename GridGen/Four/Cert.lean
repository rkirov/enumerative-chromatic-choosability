/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.State

/-!
# Height four: the averaged gain

After averaging, the per-state gain becomes a function of the three list mismatches alone:
`Fval k μ₂ μ₃ μ₄`, or `Fcap k μ₂ μ₃ μ₄` with the pattern term capped. `Cert7.lean` checks them at
`k = 7`. (For `k ≥ 8` every grid is ECC by the gauge route, `GridGen/Gauge/`, so the certificate
for `k = 8` that once lived here was removed.)
-/

namespace GridGen.Four

open Real

/-- The averaged fibre ratio `q = 1/(ρ(k-3))`. -/
noncomputable def qk (k : ℕ) : ℝ := 1 / (rho k * ((k - 3 : ℕ) : ℝ))

/-- The averaged gain. -/
noncomputable def Fval (k : ℕ) (μ2 μ3 μ4 : ℝ) : ℝ :=
  log (1 + μ2 / kA ((k : ℝ) - 1)) + log (1 + μ3 / kA ((k : ℝ) - 1))
    + log (1 + μ4 / kA ((k : ℝ) - 1))
    - 2 * qk k * (μ2 + μ3 + μ4) / (((k : ℝ) - 1) * ((k : ℝ) - 1 - 1))
    - J3 μ2 μ3 * ((μ2 + 1) * (μ3 + 1) / (((k : ℝ) - 1) ^ 2 * ((k : ℝ) - 1 - 1) ^ 2)
        + ku3 ((k : ℝ) - 1) * qk k)
    - J4 μ2 μ3 μ4 * ((μ3 + 2) * (μ4 + 1) / (((k : ℝ) - 1) * ((k : ℝ) - 1 - 1) ^ 3)
        + ku4e ((k : ℝ) - 1) * qk k + ku4b ((k : ℝ) - 1))
    - eta k * (1 + 4 * qk k) * (μ2 + 2 * μ3 + μ4)

/-- The averaged gain with the pattern term capped at `(1-ρ)/ρ`. -/
noncomputable def Fcap (k : ℕ) (μ2 μ3 μ4 : ℝ) : ℝ :=
  log (1 + μ2 / kA ((k : ℝ) - 1)) + log (1 + μ3 / kA ((k : ℝ) - 1))
    + log (1 + μ4 / kA ((k : ℝ) - 1))
    - 2 * qk k * (μ2 + μ3 + μ4) / (((k : ℝ) - 1) * ((k : ℝ) - 1 - 1))
    - J3 μ2 μ3 * ((μ2 + 1) * (μ3 + 1) / (((k : ℝ) - 1) ^ 2 * ((k : ℝ) - 1 - 1) ^ 2)
        + ku3 ((k : ℝ) - 1) * qk k)
    - J4 μ2 μ3 μ4 * ((μ3 + 2) * (μ4 + 1) / (((k : ℝ) - 1) * ((k : ℝ) - 1 - 1) ^ 3)
        + ku4e ((k : ℝ) - 1) * qk k + ku4b ((k : ℝ) - 1))
    - (1 - rho k) / rho k

/-- `log (1 + x/A) ≥ x/A - x²/(2A²)`. -/
theorem log_quad {x A : ℝ} (hx : 0 ≤ x) (hA : 0 < A) :
    x / A - x ^ 2 / (2 * A ^ 2) ≤ log (1 + x / A) := by
  have := log_one_add_ge (div_nonneg hx hA.le)
  have e : x / A - (x / A) ^ 2 / 2 = x / A - x ^ 2 / (2 * A ^ 2) := by field_simp
  linarith

end GridGen.Four
