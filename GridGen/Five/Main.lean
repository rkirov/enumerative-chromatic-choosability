/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.Final
import GridGen.Five.Six
import GridGen.Five.Init5
import GridGen.Gauge.Seven.Assemble7

/-!
# Height five: `P₅ □ P_{n+1}` is `k`-ECC for every `k ≥ 6`

At `k = 6` the height-five seam inequality (`seam5Holds_six`) and initial inequality
(`init5Holds_six`) feed GridGen's telescoping (`ecc_pathG_four_of_holds`); for `k ≥ 7` every grid
is `k`-ECC (`ListColoring.ecc_boxProd_pathG_of_seven`, the gauge route).
-/

namespace GridGen.Five

open SimpleGraph ListColoring
open scoped SimpleGraph

/-- **`P₅ □ P_{n+1}` is `k`-ECC for every `k ≥ 6`.** -/
theorem ecc_boxProd_pathG_four {k : ℕ} (hk : 6 ≤ k) (n : ℕ) : (pathG 4 □ pathG n).ECCAt k := by
  rcases (show k = 6 ∨ 7 ≤ k by omega) with rfl | hk7
  · exact ecc_pathG_four_of_holds seam5Holds_six init5Holds_six n
  · exact ecc_boxProd_pathG_of_seven hk7 4 n

end GridGen.Five
