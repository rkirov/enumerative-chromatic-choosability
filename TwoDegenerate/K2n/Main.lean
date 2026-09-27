/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import TwoDegenerate.K2n.Positive3
import TwoDegenerate.K2n.Positive4
import TwoDegenerate.K2n.Positive5
import TwoDegenerate.K2n.Negative

/-!
# `K₂,ₙ` at list sizes three, four and five

For `k = 3, 4, 5`, `K₂,ₙ` is enumeratively chromatic-choosable at `k` exactly when `n ≤ 11`,
`n ≤ 25`, `n ≤ 43` respectively.

Kaul, Kumar, Liu, Mudrock, Rewers, Shin, Tanahara and To (*Bounding the list color function
threshold from above*, Involve 16 (2023), Theorem 7) prove: ECC at three for `2 ≤ n ≤ 10` and not
for `n ≥ 12`; at four for `2 ≤ n ≤ 24` and not for `n ≥ 27`; at five for `2 ≤ n ≤ 43` and not for
`n ≥ 44`. They leave `K₂,₁₁` at three and `K₂,₂₅`, `K₂,₂₆` at four open. Here `K₂,₁₁` is ECC at
three, `K₂,₂₅` is ECC at four and `K₂,₂₆` is not, which settles all three.

The proofs are independent of theirs, except that the negative side uses the list family of
their Lemma 11:

* positive (`n ≤ N`): every list assignment reduces to one numeric inequality per overlap of the hub
  lists (`TwoDegenerate/K2n/Reduction.lean`), each closed by a kernel-checked AM–GM
  branch-and-bound certificate (`TwoDegenerate/K2n/Checker.lean`, generated files in
  `TwoDegenerate/K2n/Cert/` and `Keys/`), where they use floating-point checks of AM–GM bounds;
* negative (`n > N`): the Lemma 11 family, with an induction on `n / 4`
  (`TwoDegenerate/K2n/Witness.lean`, `Negative.lean`) in place of their appeal to Theorem 14 of
  Kaul–Kumar–Mudrock–Rewers–Shin–To for large `n`.
-/

namespace SimpleGraph.TwoDegenerate

open K2n

/-- **`K₂,ₙ` is ECC at three exactly when `n ≤ 11`.** -/
theorem completeBipartite_two_eccAt_three_iff (n : ℕ) :
    (completeBipartiteGraph (Fin 2) (Fin n)).ECCAt 3 ↔ n ≤ 11 :=
  ⟨fun h => by by_contra hn; exact not_eccAt_three (by omega) h, eccAt_3_of_le⟩

/-- **`K₂,ₙ` is ECC at four exactly when `n ≤ 25`.** -/
theorem completeBipartite_two_eccAt_four_iff (n : ℕ) :
    (completeBipartiteGraph (Fin 2) (Fin n)).ECCAt 4 ↔ n ≤ 25 :=
  ⟨fun h => by by_contra hn; exact not_eccAt_four (by omega) h, eccAt_4_of_le⟩

/-- **`K₂,ₙ` is ECC at five exactly when `n ≤ 43`.** -/
theorem completeBipartite_two_eccAt_five_iff (n : ℕ) :
    (completeBipartiteGraph (Fin 2) (Fin n)).ECCAt 5 ↔ n ≤ 43 :=
  ⟨fun h => by by_contra hn; exact not_eccAt_five (by omega) h, eccAt_5_of_le⟩

/-- `K₂,₁₁` is ECC at three: the case Kaul et al. leave open at list size three. -/
theorem K2_11.eccAt_three : (completeBipartiteGraph (Fin 2) (Fin 11)).ECCAt 3 :=
  eccAt_3_of_le le_rfl

/-- `K₂,₂₅` is ECC at four. -/
theorem K2_25.eccAt_four : (completeBipartiteGraph (Fin 2) (Fin 25)).ECCAt 4 :=
  eccAt_4_of_le le_rfl

/-- The threshold at four, pinned down: `K₂,₂₅` is ECC at four and `K₂,₂₆` is not. -/
theorem K2_25.eccAt_four_twentyFive_and_not_twentySix :
    (completeBipartiteGraph (Fin 2) (Fin 25)).ECCAt 4 ∧
      ¬ (completeBipartiteGraph (Fin 2) (Fin 26)).ECCAt 4 :=
  ⟨K2_25.eccAt_four, K2_26.not_eccAt_four⟩

end SimpleGraph.TwoDegenerate

#print axioms SimpleGraph.TwoDegenerate.completeBipartite_two_eccAt_three_iff
#print axioms SimpleGraph.TwoDegenerate.completeBipartite_two_eccAt_four_iff
#print axioms SimpleGraph.TwoDegenerate.completeBipartite_two_eccAt_five_iff
