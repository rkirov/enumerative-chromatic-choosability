/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.Final
import GridGen.Four.Seam
import GridGen.Four.Init
import GridGen.PeelDegree

/-!
# Height four: `P₄ □ P_{n+1}` is `k`-ECC for every `k ≥ 8`

For `8 ≤ k ≤ 15` the height-four seam inequality (`seam4Holds`) and initial inequality
(`init4Holds`) feed GridGen's telescoping (`ecc_pathG_three_of_holds`); for `k ≥ 16` every grid is
`k`-ECC (`ListColoring.ecc_boxProd_pathG_of_sixteen`).

The seam inequality is the multiplicative localisation of this formalisation's research notes
(`ai_research_notes/H4_LOCALIZATION_2026-10-15.md`), with the invariant box `ρ = 1 - 2/(k-2)³` and
the one-sided row error bounds due to Codex (OpenAI), `CODEX_H4_SEAM_BOUNDS_2026-10-15.md`.
-/

namespace GridGen.Four

open SimpleGraph ListColoring
open scoped SimpleGraph

/-- **`P₄ □ P_{n+1}` is `k`-ECC for every `k ≥ 8`.** -/
theorem ecc_boxProd_pathG_three {k : ℕ} (hk : 8 ≤ k) (n : ℕ) : (pathG 3 □ pathG n).ECCAt k := by
  by_cases h : k ≤ 15
  · exact ecc_pathG_three_of_holds (by omega) (seam4Holds hk h) (init4Holds hk) n
  · exact ecc_boxProd_pathG_of_sixteen (by omega) 3 n

end GridGen.Four
