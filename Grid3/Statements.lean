/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Grid3.PairC
import Grid3.DepthTwo
import Grid3.Obstructions
import Grid3.Four.Main

/-!
# Height-three grids are enumeratively chromatic-choosable at every list size `k ≥ 3`

The headline results of `Grid3/`, in the vocabulary of the rest of the repository: `k ≥ 4` is
proved in this file, `k = 3` in `Grid3/Three/Main.lean` (see the last section), and together
they settle `P₃ □ P_{n+1}` at every list size `k ≥ 3`.

`pathG m` is the path of *length* `m`, on `m + 1` vertices, so `pathG 2 □ pathG n` is the
`3 × (n+1)` grid — `P₃ □ P_{n+1}`. The theorem is the height-three case of the conclusion of
`ListColoring.OpenProblem.grid_of_question1`, proved unconditionally instead of from
Kirov–Naimi's Question 1.

## The proof, in one paragraph

An exact telescoping identity (`Grid3.total_vec_ge_fw`) writes the colouring count minus the
uniform count as an initial term plus one term per seam, each of the form "the actual seam minus
the uniform pattern transfer, applied to the uniform future counts". At height three there are
two patterns (`a = c` or not), and every horizon reduces to two integer inequalities per seam,
`(H1)` and `(C1_r)` (`Grid3.seam_le`). Both are linear in the state vector, and the vector at a
seam is a nonnegative combination of the successor indicators of the states one column back
(`Grid3.allSeamsOK_of_lookback`), so it suffices to prove them for one state and three
consecutive columns of lists (`Grid3.ecc_of_colOK`). Fibred over the middle colour, each becomes
a sum of per-colour terms, and a *pair lemma* — any two distinct colours have nonnegative sum —
closes it (`Grid3.ecc_of_pairOK`). The pair lemmas (`Grid3.pairH_of_five`, `Grid3.pairC_of_five`)
come from a pointwise bound on each state's deficiency (`Grid3.LB_le_dH`), exact at uniform, and
an integer inequality whose threshold is exactly `(k-2)(k-3) ≥ k+1`, i.e. `k ≥ 5`
(`Grid3.pair_arith`, `Grid3.pairC_arith`).

## The `k = 4` case

At `k = 4` the one-column lookback condition is false (`Grid3.not_depthOK_four_one`): its
explicit `(C1_r)` witness has deficit exactly one. Two columns of lookback suffice
(`Grid3.ecc_grid3_four_of_depthTwo`), and `Grid3/Four/` discharges the two surviving obligations
`Grid3.InitialTwoSeamsOK 4` and `Grid3.DepthTwoLocalOK 4`. The per-colour terms are bounded by a
*conditional* pair lemma (`Grid3.Four.pair_main`) — the pair sum is at least `1`, or at least `-1`
in two explicit *Bad* configurations — and a regular-colour lemma (`Grid3.Four.single_main`), both
families of LP certificates over the Venn atoms of the five lists involved, checked by
`linear_combination` (`Grid3/Four/ArithPair/`, `Grid3/Four/ArithSingle.lean`). Assembled over a
column (`Grid3.Four.colC_or`), a Bad column costs exactly one, and an injection from the Bad
states two columns back into states with surplus at least one pays for it
(`Grid3.Four.sum_GC_nonneg`).

## `k = 3`

There the inequality `(C1_r)` is false on actual chains, so this route cannot work; see
`ai_research_notes/GRID_HEIGHT3_EIGENFUNCTIONAL_2026-08-25.md`. The `k = 3` case is proved by the
entropy (Parry–Rényi) certificate route in `Grid3/Three/Main.lean`
(`Grid3.Three.ecc_grid3_three`, and `ecc_boxProd_pathG_two_of_three` for every `k ≥ 3`). That
module is not imported here because it depends on the 22,157 kernel-checked seam records of
`Grid3/Three/Cert/Data/`, which are built separately (see `Grid3/Three/README.md`).
-/

namespace ListColoring

open SimpleGraph

/-- **Height-three grids are `k`-ECC for every `k ≥ 5`.** No assignment of `k`-element lists to
the `3 × (n+1)` grid admits fewer colourings than the constant assignment does. -/
theorem ecc_boxProd_pathG_two {k : ℕ} (hk : 5 ≤ k) (n : ℕ) : (pathG 2 □ pathG n).ECCAt k :=
  Grid3.ecc_grid3_of_five hk n

/-- The same, in the `P_ℓ = P` form of `ListColoring.OpenProblem.GridTarget`. -/
theorem gridTarget_boxProd_pathG_two {k : ℕ} (hk : 5 ≤ k) (n : ℕ) :
    (pathG 2 □ pathG n).listColorFunction k = (pathG 2 □ pathG n).colConst k :=
  (ecc_iff_listColorFunction_eq k).mp (ecc_boxProd_pathG_two hk n)

/-- **Height-three grids are `k`-ECC for every `k ≥ 4`.** For `k ≥ 5` this is the one-column
lookback proof of `Grid3.PairC`; for `k = 4` it is the two-column lookback proof of `Grid3/Four/`
(`Grid3.Four.ecc_grid3_four`), whose arithmetic core is a family of LP certificates checked by
`linear_combination`. -/
theorem ecc_boxProd_pathG_two_of_four {k : ℕ} (hk : 4 ≤ k) (n : ℕ) :
    (pathG 2 □ pathG n).ECCAt k := by
  rcases Nat.lt_or_ge k 5 with h | h
  · have hk4 : k = 4 := by omega
    subst hk4
    exact Grid3.Four.ecc_grid3_four n
  · exact Grid3.ecc_grid3_of_five h n

/-- The same, in the `P_ℓ = P` form of `ListColoring.OpenProblem.GridTarget`. -/
theorem gridTarget_boxProd_pathG_two_of_four {k : ℕ} (hk : 4 ≤ k) (n : ℕ) :
    (pathG 2 □ pathG n).listColorFunction k = (pathG 2 □ pathG n).colConst k :=
  (ecc_iff_listColorFunction_eq k).mp (ecc_boxProd_pathG_two_of_four hk n)

/-- **The uniform count, in closed form:** `P(P₃ □ P_{n+1}, k) = Fne k n · k(k-1)² + Dp k n · k(k-1)`,
where `Fne`, `Dp` are the integer sequences of `Grid3.Transfer` (`12, 54, 246, 1122, 5118, …` at
`k = 3`). -/
theorem colConst_boxProd_pathG_two {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    (pathG 2 □ pathG n).colConst k
      = Grid3.Fne k n * (k * (k - 1) ^ 2) + Grid3.Dp k n * (k * (k - 1)) :=
  Grid3.colConst_eq hk n

end ListColoring

#print axioms ListColoring.ecc_boxProd_pathG_two
#print axioms ListColoring.ecc_boxProd_pathG_two_of_four
#print axioms ListColoring.gridTarget_boxProd_pathG_two
#print axioms ListColoring.colConst_boxProd_pathG_two
