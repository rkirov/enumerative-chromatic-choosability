/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.PolymerPeelCertificate
import GridGen.PolymerGridDegree
import ListColoring.BoxProd

/-!
# Degree thresholds from the degree-sensitive certificate

Instances of `GridGen.Polymer.eccAt_of_certifiedPeelAt` (`PolymerPeelCertificate.lean`): the
deletion ratio is needed only at vertices of residual degree at most `D - 1`, so the root budget is
the branch odd mass `o` (`s o ≤ s - 1`), while the full-degree root only has to keep its odd mass
`r` below `1`. Each certificate is a rational identity checked by `norm_num`.

| `Δ ≤` | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|
| here | 11 | 17 | 22 | 28 | 33 | 39 |
| `SmallDegree.lean`, `DegreeFourTwenty.lean` | 15 | 20 | 26 | 32 | 37 | 43 |

Each threshold is the least this certificate shape reaches (checked numerically, not in Lean).
The degree-sensitive induction was proposed by Codex (OpenAI); see
`ai_research_notes/CODEX_GRID_ALL_HEIGHTS_2026-10-07.md` §3, which also sketches `k ≥ 16` at
degree four by keeping the neighbour-pair blocks at a degree-three root (not done here).
-/

namespace GridGen.Polymer

theorem parityCert_peel_three :
    ParityCert 3 ((71 / 50 : ℝ) / (11 : ℕ)) (549 / 500) (59 / 200) (231 / 500) := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_, by norm_num⟩ <;>
    norm_num [parityPower]

theorem parityCert_peel_four :
    ParityCert 4 ((7 / 5 : ℝ) / (17 : ℕ)) (549 / 500) (57 / 200) (391 / 1000) := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_, by norm_num⟩ <;>
    norm_num [parityPower]

theorem parityCert_peel_five :
    ParityCert 5 ((3 / 2 : ℝ) / (22 : ℕ)) (283 / 250) (333 / 1000) (427 / 1000) := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_, by norm_num⟩ <;>
    norm_num [parityPower]

theorem parityCert_peel_six :
    ParityCert 6 ((73 / 50 : ℝ) / (28 : ℕ)) (1121 / 1000) (157 / 500) (77 / 200) := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_, by norm_num⟩ <;>
    norm_num [parityPower]

theorem parityCert_peel_seven :
    ParityCert 7 ((8 / 5 : ℝ) / (33 : ℕ)) (583 / 500) (3 / 8) (56 / 125) := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_, by norm_num⟩ <;>
    norm_num [parityPower]

theorem parityCert_peel_eight :
    ParityCert 8 ((38 / 25 : ℝ) / (39 : ℕ)) (571 / 500) (341 / 1000) (99 / 250) := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_, by norm_num⟩ <;>
    norm_num [parityPower]

end GridGen.Polymer

namespace SimpleGraph

open GridGen.Polymer

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Every finite subcubic graph is ECC at every list size at least 11. -/
theorem eccAt_of_degree_le_three_eleven (hdeg : ∀ v, G.degree v ≤ 3) {k : ℕ} (hk : 11 ≤ k) :
    G.ECCAt k :=
  eccAt_of_certifiedPeelAt G hdeg (certifiedPeelAt_of_parityCert parityCert_peel_three
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk)

/-- **Every finite graph of maximum degree at most four is ECC at every list size at least 17.** -/
theorem eccAt_of_degree_le_four_seventeen (hdeg : ∀ v, G.degree v ≤ 4) {k : ℕ} (hk : 17 ≤ k) :
    G.ECCAt k :=
  eccAt_of_certifiedPeelAt G hdeg (certifiedPeelAt_of_parityCert parityCert_peel_four
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk)

/-- Every finite graph of maximum degree at most five is ECC at every list size at least 22. -/
theorem eccAt_of_degree_le_five_twentyTwo (hdeg : ∀ v, G.degree v ≤ 5) {k : ℕ} (hk : 22 ≤ k) :
    G.ECCAt k :=
  eccAt_of_certifiedPeelAt G hdeg (certifiedPeelAt_of_parityCert parityCert_peel_five
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk)

/-- Every finite graph of maximum degree at most six is ECC at every list size at least 28. -/
theorem eccAt_of_degree_le_six_twentyEight (hdeg : ∀ v, G.degree v ≤ 6) {k : ℕ} (hk : 28 ≤ k) :
    G.ECCAt k :=
  eccAt_of_certifiedPeelAt G hdeg (certifiedPeelAt_of_parityCert parityCert_peel_six
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk)

/-- Every finite graph of maximum degree at most seven is ECC at every list size at least 33. -/
theorem eccAt_of_degree_le_seven_thirtyThree (hdeg : ∀ v, G.degree v ≤ 7) {k : ℕ}
    (hk : 33 ≤ k) : G.ECCAt k :=
  eccAt_of_certifiedPeelAt G hdeg (certifiedPeelAt_of_parityCert parityCert_peel_seven
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk)

/-- Every finite graph of maximum degree at most eight is ECC at every list size at least 39. -/
theorem eccAt_of_degree_le_eight_thirtyNine (hdeg : ∀ v, G.degree v ≤ 8) {k : ℕ}
    (hk : 39 ≤ k) : G.ECCAt k :=
  eccAt_of_certifiedPeelAt G hdeg (certifiedPeelAt_of_parityCert parityCert_peel_eight
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk)

end SimpleGraph

namespace ListColoring

open SimpleGraph
open scoped SimpleGraph

/-- **Every rectangular grid is ECC at every list size at least 17.** Both dimensions are
unrestricted; `pathG n` has `n + 1` vertices. -/
theorem ecc_boxProd_pathG_of_seventeen {k : ℕ} (hk : 17 ≤ k) (n m : ℕ) :
    (pathG n □ pathG m).ECCAt k := by
  classical
  apply SimpleGraph.eccAt_of_degree_le_four_seventeen _ _ hk
  intro v
  convert! GridGen.Polymer.degree_full_grid_le_four n m v

end ListColoring
