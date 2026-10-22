/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Seven.Final7
import GridGen.Gauge.Seven.Reflect7
import GridGen.Gauge.Seven.BoxT2
import GridGen.Gauge.Seven.BoxJ3

/-!
# Every grid is 7-ECC

The box bounds (`boxes7`): the vertical three-cell path against the star of its middle row
(`joint_three`), and the two-cell path against the star of its head row (`absorb_two_vert`),
reflected for the last row (`absD_of_absH`). With them the seam bounds hold (`k7Bounds_of_boxes`)
and every grid is 7-ECC.
-/

open SimpleGraph ListColoring
open scoped SimpleGraph

namespace GridGen.Gauge

/-- **The head-row two-cell box bound.** -/
theorem absHBound : AbsHBound :=
  fun hK hA hP hc _ _ _ hxy hx hy hh v hv hhole _ ha₀ h7 =>
    absorb_two_vert hK hA hP hc hxy hx hy hh v hv hhole ha₀ h7

/-- **The box bounds at `k = 7`.** -/
theorem boxes7 : Boxes7 where
  joint3 hK hA hP hc _ _ _ _ hxy hx hy hh hℓ v hv hhole _ ha₀ h7 :=
    joint_three hK hA hP hc hxy hx hy hh hℓ v hv hhole ha₀ h7
  absH := absHBound
  absD := absD_of_absH absHBound

/-- **The seam bounds at `k = 7`.** -/
theorem k7Bounds : K7Bounds := k7Bounds_of_boxes boxes7

/-- **`rowG m □ P_{n+1}` is `7`-ECC.** -/
theorem ecc_rowG_boxProd_seven' (m n : ℕ) : (rowG m □ pathG n).ECCAt 7 :=
  ecc_rowG_boxProd_seven k7Bounds m n

end GridGen.Gauge

namespace ListColoring

open GridGen.Gauge

/-- **Every rectangular grid is ECC at every list size at least 7.** Both dimensions are
unrestricted; `pathG n` has `n + 1` vertices. -/
theorem ecc_boxProd_pathG_of_seven {k : ℕ} (hk : 7 ≤ k) (r n : ℕ) :
    (pathG r □ pathG n).ECCAt k :=
  ecc_boxProd_pathG_of_seven_of_boxes boxes7 hk r n

end ListColoring
