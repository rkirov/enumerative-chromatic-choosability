/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Six.Seam
import GridGen.Six.Init
import GridGen.Gauge.Seven.Assemble7

/-!
# Height six: `P₆ □ P_{n+1}` is `k`-ECC for every `k ≥ 6`

At `k = 6` the height-six seam inequality on the cone of Codex (OpenAI) (`seam66Holds`,
`GridGen/Six/Seam.lean`) and the initial inequality (`init66Holds`, `GridGen/Six/Init.lean`) feed
GridGen's telescoping (`ecc_pathG_five_of_holds6`); for `k ≥ 7` every grid is `k`-ECC
(`ListColoring.ecc_boxProd_pathG_of_seven`, the gauge route).
-/

namespace GridGen.Six

open SimpleGraph ListColoring
open scoped SimpleGraph

/-- **`P₆ □ P_{n+1}` is `6`-ECC.** -/
theorem ecc_boxProd_pathG_five_six (n : ℕ) : (pathG 5 □ pathG n).ECCAt 6 :=
  ecc_pathG_five_of_holds6 seam66Holds init66Holds n

/-- **`P₆ □ P_{n+1}` is `k`-ECC for every `k ≥ 6`.** -/
theorem ecc_boxProd_pathG_five {k : ℕ} (hk : 6 ≤ k) (n : ℕ) : (pathG 5 □ pathG n).ECCAt k := by
  rcases (show k = 6 ∨ 7 ≤ k by omega) with rfl | hk7
  · exact ecc_boxProd_pathG_five_six n
  · exact ecc_boxProd_pathG_of_seven hk7 5 n

end GridGen.Six
