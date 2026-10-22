/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Seven.Final7
import GridGen.Gauge.Seven.Reflect7
import GridGen.Gauge.Seven.BoxT2

/-!
# Every grid is 7-ECC

The box bounds: `θ₂` in the head-row orientation (`absorb_two_vert`), reflected for the last-row
orientation (`absD_of_absH`).
-/

namespace GridGen.Gauge

/-- **The head-row two-cell box bound.** -/
theorem absHBound : AbsHBound :=
  fun hK hA hP hc _ _ _ hxy hx hy hh v hv hhole _ ha₀ h7 =>
    absorb_two_vert hK hA hP hc hxy hx hy hh v hv hhole ha₀ h7

end GridGen.Gauge
