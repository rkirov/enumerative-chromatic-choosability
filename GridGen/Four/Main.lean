/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.Final
import GridGen.Four.Six
import GridGen.Four.Init
import GridGen.Gauge.Seven.Assemble7

/-!
# Height four: `P₄ □ P_{n+1}` is `k`-ECC for every `k ≥ 6`

For `k = 6` the height-four seam inequality (`seam4Holds_six`) and initial inequality
(`init4Holds_six`) feed GridGen's telescoping (`ecc_pathG_three_of_holds`); for `k ≥ 7` every grid
is `k`-ECC (`ListColoring.ecc_boxProd_pathG_of_seven`, the gauge route).

The seam inequality is the multiplicative localisation of this formalisation's research notes
(`ai_research_notes/H4_LOCALIZATION_2026-10-15.md`), with the invariant box `ρ = 1 - 2/(k-2)³` and
the one-sided row error bounds due to Codex (OpenAI), `CODEX_H4_SEAM_BOUNDS_2026-10-15.md`. At
`k = 6` the box edge is `487/500`, the row bounds are sharpened (`CountBound6`, `Fibre6`), the
pattern term is capped by a uniform-class comparison (`pattern_six`), and sixteen small triples
(69 list shapes) are certified exactly (`Small6`).
-/

namespace GridGen.Four

open SimpleGraph ListColoring
open scoped SimpleGraph

/-- **`P₄ □ P_{n+1}` is `k`-ECC for every `k ≥ 6`.** -/
theorem ecc_boxProd_pathG_three {k : ℕ} (hk : 6 ≤ k) (n : ℕ) : (pathG 3 □ pathG n).ECCAt k := by
  rcases (show k = 6 ∨ 7 ≤ k by omega) with rfl | hk7
  · exact ecc_pathG_three_of_holds (by norm_num) seam4Holds_six init4Holds_six n
  · exact ecc_boxProd_pathG_of_seven hk7 3 n

end GridGen.Four
