/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.Bridge

/-!
# Height four: the grid `P₄ □ P_{n+1}` from the two height-four inequalities

For `k ≥ 5`, the height-four seam inequality `Seam4Holds k` and initial inequality
`Init4Holds k` (`GridGen/Four/Statement.lean`) give the explicit two-step, first-seam and initial
hypotheses of GridGen's telescoping for the row graph `pathG 3` (`GridGen/Four/Bridge.lean`), and
`GridGen.ecc_of_explicit` turns them into `k`-ECC of `pathG 3 □ pathG n` for every `n`.
-/

namespace GridGen.Four

open SimpleGraph ListColoring
open scoped SimpleGraph

/-- **`P₄ □ P_{n+1}` is `k`-ECC, given the height-four seam and initial inequalities at `k ≥ 5`.** -/
theorem ecc_pathG_three_of_holds {k : ℕ} (hk : 5 ≤ k) (hS : Seam4Holds k) (hI : Init4Holds k)
    (n : ℕ) : (pathG 3 □ pathG n).ECCAt k :=
  ecc_of_explicit (pathG 3) (twoStepExplicit_of_seam hk hS) (firstSeamExplicit_of_seam hk hS)
    (init_of_init4 hk hI) n

end GridGen.Four
