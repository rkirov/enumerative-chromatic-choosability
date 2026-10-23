/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.Bridge

/-!
# Height five: the grid `P₅ □ P_{n+1}` from the two height-five inequalities

At `k = 6`, the height-five seam inequality `Seam5Holds 6` and initial inequality
`Init5Holds 6` (`GridGen/Five/Statement.lean`) give the explicit two-step, first-seam and initial
hypotheses of GridGen's telescoping for the row graph `pathG 4` (`GridGen/Five/Bridge.lean`), and
`GridGen.ecc_of_explicit` turns them into `6`-ECC of `pathG 4 □ pathG n` for every `n`.
-/

namespace GridGen.Five

open SimpleGraph ListColoring
open scoped SimpleGraph

/-- **`P₅ □ P_{n+1}` is `6`-ECC, given the height-five seam and initial inequalities at
`k = 6`.** -/
theorem ecc_pathG_four_of_holds (hS : Seam5Holds 6) (hI : Init5Holds 6) (n : ℕ) :
    (pathG 4 □ pathG n).ECCAt 6 :=
  ecc_of_explicit (pathG 4) (twoStepExplicit_of_seam hS) (firstSeamExplicit_of_seam hS)
    (init_of_init5 hI) n

end GridGen.Five
