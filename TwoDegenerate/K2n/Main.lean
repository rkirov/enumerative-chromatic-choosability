/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import TwoDegenerate.K2n.R0
import TwoDegenerate.K2n.R1
import TwoDegenerate.K2n.R2
import TwoDegenerate.K2n.R3
import TwoDegenerate.K2n.R4

/-!
# `K₂,₂₅` is enumeratively chromatic-choosable at four

Kaul, Kumar, Liu, Mudrock, Rewers, Shin, Tanahara and To (*Bounding the list color function
threshold from above*, Involve 16 (2023), Theorem 7(ii)) prove that `K₂,ₙ` is ECC at four for
`n ≤ 24` and not for `n ≥ 27`, and leave `n = 25, 26` open. `TwoDegenerate/Counterexample.lean`
settles `n = 26` negatively. This file settles `n = 25` positively, so the threshold is exact:
`K₂,ₙ` is ECC at four exactly when `n ≤ 25`.

The proof is `le_col_of_keyGoals` (`TwoDegenerate/K2n/Reduction.lean`) applied to one kernel-checked
certificate per overlap `|A ∩ B| = 0, …, 4` of the two hub lists (`TwoDegenerate/K2n/R*.lean`).
-/

namespace SimpleGraph.TwoDegenerate.K2_25

open K2n K2n.K2_25

/-- `K₂,₂₅`, on `Fin 2 ⊕ Fin 25`. -/
abbrev G : SimpleGraph (Fin 2 ⊕ Fin 25) := completeBipartiteGraph (Fin 2) (Fin 25)

/-- The number of ordinary four-colourings of `K₂,₂₅`, `4·3²⁵ + 12·2²⁵`. -/
theorem colConst_four : G.colConst 4 = 4 * 3 ^ 25 + 12 * 2 ^ 25 := by
  rw [colConst, col_completeBipartite_two_right]
  decide

theorem keyGoals : ∀ r ≤ 4, ∃ K, KeyGoal (4 * 3 ^ 25 + 12 * 2 ^ 25) 25 r K := by
  intro r hr
  match r, hr with
  | 0, _ => exact ⟨_, keyGoal0⟩
  | 1, _ => exact ⟨_, keyGoal1⟩
  | 2, _ => exact ⟨_, keyGoal2⟩
  | 3, _ => exact ⟨_, keyGoal3⟩
  | 4, _ => exact ⟨_, keyGoal4⟩

/-- **`K₂,₂₅` is enumeratively chromatic-choosable at four**: no assignment of four-element
lists admits fewer colourings than the constant one. -/
theorem eccAt_four : (completeBipartiteGraph (Fin 2) (Fin 25)).ECCAt 4 := by
  intro L hL
  rw [colConst_four]
  exact le_col_of_keyGoals keyGoals L hL

/-- The threshold, pinned down: `K₂,₂₅` is ECC at four and `K₂,₂₆` is not. -/
theorem eccAt_four_twentyFive_and_not_twentySix :
    (completeBipartiteGraph (Fin 2) (Fin 25)).ECCAt 4 ∧
      ¬ (completeBipartiteGraph (Fin 2) (Fin 26)).ECCAt 4 :=
  ⟨eccAt_four, K2_26.not_eccAt_four⟩

end SimpleGraph.TwoDegenerate.K2_25

#print axioms SimpleGraph.TwoDegenerate.K2_25.eccAt_four
#print axioms SimpleGraph.TwoDegenerate.K2_25.eccAt_four_twentyFive_and_not_twentySix
