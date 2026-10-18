/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.Final
import GridGen.Four.Seam7
import GridGen.Four.Init
import GridGen.Gauge.Eight.Main8

/-!
# Height four: `P₄ □ P_{n+1}` is `k`-ECC for every `k ≥ 7`

For `k = 7` the height-four seam inequality (`seam4Holds_seven`) and initial inequality
(`init4Holds`) feed GridGen's telescoping (`ecc_pathG_three_of_holds`); for `k ≥ 8` every grid is
`k`-ECC (`ListColoring.ecc_boxProd_pathG_of_eight`, the gauge route).

The seam inequality is the multiplicative localisation of this formalisation's research notes
(`ai_research_notes/H4_LOCALIZATION_2026-10-15.md`), with the invariant box `ρ = 1 - 2/(k-2)³` and
the one-sided row error bounds due to Codex (OpenAI), `CODEX_H4_SEAM_BOUNDS_2026-10-15.md`. At
`k = 7` the pattern term is capped, and the five smallest mismatch triples are certified exactly.
-/

namespace GridGen.Four

open SimpleGraph ListColoring
open scoped SimpleGraph

/-- **`P₄ □ P_{n+1}` is `k`-ECC for every `k ≥ 7`.** -/
theorem ecc_boxProd_pathG_three {k : ℕ} (hk : 7 ≤ k) (n : ℕ) : (pathG 3 □ pathG n).ECCAt k := by
  rcases (show k = 7 ∨ 8 ≤ k by omega) with rfl | hk8
  · exact ecc_pathG_three_of_holds (by norm_num) seam4Holds_seven (init4Holds le_rfl) n
  · exact ecc_boxProd_pathG_of_eight hk8 3 n

end GridGen.Four
