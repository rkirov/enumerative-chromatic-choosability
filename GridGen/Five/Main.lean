/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.Final
import GridGen.Five.Six
import GridGen.Five.Init5
import GridGen.Five.K5.Seam
import GridGen.Five.K5.Init
import GridGen.Gauge.Seven.Assemble7

/-!
# Height five: `P₅ □ P_{n+1}` is `k`-ECC for every `k ≥ 5`

At `k = 5` the height-five seam inequality on the cone of Codex (OpenAI)
(`K5.seam55Holds`, `GridGen/Five/K5/`) and the initial inequality (`K5.init55Holds`) feed GridGen's
telescoping (`K5.ecc_pathG_four_of_holds5`); at `k = 6` the height-five seam inequality
(`seam5Holds_six`) and initial inequality (`init5Holds_six`) do (`ecc_pathG_four_of_holds`); for
`k ≥ 7` every grid is `k`-ECC (`ListColoring.ecc_boxProd_pathG_of_seven`, the gauge route).
-/

namespace GridGen.Five

open SimpleGraph ListColoring
open scoped SimpleGraph

/-- **`P₅ □ P_{n+1}` is `k`-ECC for every `k ≥ 5`.** -/
theorem ecc_boxProd_pathG_four {k : ℕ} (hk : 5 ≤ k) (n : ℕ) : (pathG 4 □ pathG n).ECCAt k := by
  rcases (show k = 5 ∨ k = 6 ∨ 7 ≤ k by omega) with rfl | rfl | hk7
  · exact K5.ecc_pathG_four_of_holds5 K5.seam55Holds K5.init55Holds n
  · exact ecc_pathG_four_of_holds seam5Holds_six init5Holds_six n
  · exact ecc_boxProd_pathG_of_seven hk7 4 n

end GridGen.Five
