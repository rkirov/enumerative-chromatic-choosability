import Ladder.Graph

/-!
# Ladders are enumeratively chromatic-choosable at every list size `k ≥ 3`

The headline results of `Ladder/`, stated in the vocabulary of the rest of the repository.

`pathG m` is the path of *length* `m`, on `m + 1` vertices, so `pathG 1 □ pathG n` is the
`2 × (n+1)` grid — the ladder `P₂ □ P_{n+1}`. The theorem is the height-two case of the conclusion
of `ListColoring.OpenProblem.grid_of_question1`, proved here unconditionally instead of from
Kirov–Naimi's Question 1.

`k ≥ 3` is sharp, and not an artefact: `pathG 1 □ pathG 2` is the `2 × 3` grid, whose
three-pairs-from-a-three-colour-palette assignment admits one colouring against a uniform count of
two. In the proof the hypothesis enters at exactly one place, `Ladder.inv_ones` — the first rung's
all-ones vector satisfies the transfer invariant iff `2k ≤ k² - k`.
-/

namespace ListColoring

open SimpleGraph

/-- **Ladders are `k`-ECC for every `k ≥ 3`.** No assignment of `k`-element lists to the
`2 × (n+1)` grid admits fewer colourings than the constant assignment does. -/
theorem ecc_boxProd_pathG_one {k : ℕ} (hk : 3 ≤ k) (n : ℕ) : (pathG 1 □ pathG n).ECCAt k :=
  Ladder.ecc_ladder hk n

/-- The same, in the `P_ℓ = P` form of `ListColoring.OpenProblem.GridTarget`: that conjecture holds
whenever one side is a single edge. -/
theorem gridTarget_boxProd_pathG_one {k : ℕ} (hk : 3 ≤ k) (n : ℕ) :
    (pathG 1 □ pathG n).listColorFunction k = (pathG 1 □ pathG n).colConst k :=
  (ecc_iff_listColorFunction_eq k).mp (ecc_boxProd_pathG_one hk n)

/-- **The uniform count, in closed form:** `P(P₂ □ P_{n+1}, k) = k(k-1)(k² - 3k + 3)ⁿ`.

The transfer eigenvalue `k² - 3k + 3 = (k-1)(k-2) + 1` is the number of ways to extend a rung
`(a,b)` with `a ≠ b` to the next one. -/
theorem colConst_boxProd_pathG_one {k : ℕ} (hk : 3 ≤ k) (n : ℕ) :
    (pathG 1 □ pathG n).colConst k = k * (k - 1) * (k * k - 3 * k + 3) ^ n := by
  have hlam : Ladder.lam k = k * k - 3 * k + 3 := by
    have h := Ladder.lam_eq (k := k) (by omega)
    have hge : 3 * k ≤ k * k := Nat.mul_le_mul_right k hk
    generalize k * k = m at h hge
    omega
  rw [Ladder.colConst_eq hk n, hlam]

end ListColoring

#print axioms ListColoring.ecc_boxProd_pathG_one
#print axioms ListColoring.gridTarget_boxProd_pathG_one
#print axioms ListColoring.colConst_boxProd_pathG_one
