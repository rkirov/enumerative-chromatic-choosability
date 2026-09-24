import GridGen.PolymerCertificate

/-!
# Degree-specific thresholds for maximum degree three and five to eight

Instances of `GridGen.Polymer.eccAt_of_parityCert` with exact polynomial certificates
(`D - 1` ports per branch, `D` at the root) instead of the hyperbolic majorant of
`GridGen/MaximumDegree.lean`, which uses `D` ports throughout. Each certificate is a rational
identity checked by `norm_num`.

| `Δ ≤` | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|
| here | 15 | 20 (`DegreeFourTwenty.lean`) | 26 | 32 | 37 | 43 |
| `⌈5.67Δ⌉` | 18 | 23 | 29 | 35 | 40 | 46 |

For each degree the threshold is the least one this certificate shape reaches (checked
numerically, not in Lean); it is not claimed optimal for ECC. The constants track Dong–Koh's
bounds for real chromatic roots (`4.765Δ` at `Δ = 3`, `5.664Δ` in general), which come from
the same kind of tree recursion; see `GridGen/MAX_DEGREE_ECC_LITERATURE_2026-09-12.md`.
-/

namespace GridGen.Polymer

theorem parityCert_degree_three :
    ParityCert 3 ((3 / 2 : ℝ) / (15 : ℕ)) (132 / 125) (27 / 125) (1 / 3) := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_, by norm_num⟩ <;>
    norm_num [parityPower]

theorem parityCert_degree_five :
    ParityCert 5 ((8 / 5 : ℝ) / (26 : ℕ)) (111 / 100) (29 / 100) (3 / 8) := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_, by norm_num⟩ <;>
    norm_num [parityPower]

theorem parityCert_degree_six :
    ParityCert 6 ((3 / 2 : ℝ) / (32 : ℕ)) (11 / 10) (7 / 25) (1 / 3) := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_, by norm_num⟩ <;>
    norm_num [parityPower]

theorem parityCert_degree_seven :
    ParityCert 7 ((8 / 5 : ℝ) / (37 : ℕ)) (9 / 8) (63 / 200) (3 / 8) := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_, by norm_num⟩ <;>
    norm_num [parityPower]

theorem parityCert_degree_eight :
    ParityCert 8 ((8 / 5 : ℝ) / (43 : ℕ)) (113 / 100) (8 / 25) (3 / 8) := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_, by norm_num⟩ <;>
    norm_num [parityPower]

end GridGen.Polymer

namespace SimpleGraph

open GridGen.Polymer

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Every finite subcubic graph is ECC at every list size at least 15. -/
theorem eccAt_of_degree_le_three (hdeg : ∀ v, G.degree v ≤ 3) {k : ℕ}
    (hk : 15 ≤ k) : G.ECCAt k :=
  eccAt_of_parityCert G hdeg parityCert_degree_three (by norm_num) (by norm_num)
    (by norm_num) hk

/-- Every finite graph of maximum degree at most five is ECC at every list size at least 26. -/
theorem eccAt_of_degree_le_five (hdeg : ∀ v, G.degree v ≤ 5) {k : ℕ}
    (hk : 26 ≤ k) : G.ECCAt k :=
  eccAt_of_parityCert G hdeg parityCert_degree_five (by norm_num) (by norm_num)
    (by norm_num) hk

/-- Every finite graph of maximum degree at most six is ECC at every list size at least 32. -/
theorem eccAt_of_degree_le_six (hdeg : ∀ v, G.degree v ≤ 6) {k : ℕ}
    (hk : 32 ≤ k) : G.ECCAt k :=
  eccAt_of_parityCert G hdeg parityCert_degree_six (by norm_num) (by norm_num)
    (by norm_num) hk

/-- Every finite graph of maximum degree at most seven is ECC at every list size at least 37. -/
theorem eccAt_of_degree_le_seven (hdeg : ∀ v, G.degree v ≤ 7) {k : ℕ}
    (hk : 37 ≤ k) : G.ECCAt k :=
  eccAt_of_parityCert G hdeg parityCert_degree_seven (by norm_num) (by norm_num)
    (by norm_num) hk

/-- Every finite graph of maximum degree at most eight is ECC at every list size at least 43. -/
theorem eccAt_of_degree_le_eight (hdeg : ∀ v, G.degree v ≤ 8) {k : ℕ}
    (hk : 43 ≤ k) : G.ECCAt k :=
  eccAt_of_parityCert G hdeg parityCert_degree_eight (by norm_num) (by norm_num)
    (by norm_num) hk

end SimpleGraph
