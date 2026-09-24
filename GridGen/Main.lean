/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Graph
import GridGen.Uniform

/-!
# `H □ P_{n+1}` is `k`-ECC, from the two-step seam inequality

The general-height reduction of `ai_research_notes/GRID_REVIEW_2026-09-02.md` §5.6, for an
arbitrary row graph `H` (`H = pathG (m-1)` gives the grid `P_m □ P_{n+1}`). Two hypotheses,
both statements about at most three consecutive columns of `k`-lists:

* `TwoStep H k` — the seam inequality at every horizon, one column back (`DepthOK` at depth `1`)
  and at the first seam (`ShortOK`), for the reference `Φ` = uniform futures by equality pattern;
* `Init H k` — the first column's states, weighted by their `n`-column uniform futures, weigh at
  least the uniform count.

Under them, `H □ pathG n` is `k`-ECC for every `n` (`ecc_of_twoStep`). Neither hypothesis is
proved here for any `H` beyond what `Grid3/` establishes at height three; the conjecture that
both hold for every path `H` and every `k ≥ 5` is `GeneralHeightConjecture`, a `Prop`, and
`ecc_grid_of_conjecture` records that it implies that every grid is `k`-ECC for `k ≥ 5`.
-/

namespace GridGen

open SimpleGraph ListColoring Finset
open scoped SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

theorem Lof_isKCols {k n : ℕ} {M : ListAssignment (V × PathV n)}
    (hM : IsNListAssignment M k) : IsKCols k (Lof n M) :=
  fun _ _ => hM _

/-- The colouring count is the total of the abstract chain of the assignment's lists. -/
theorem col_eq_total_vec (n : ℕ) (M : ListAssignment (V × PathV n)) :
    (H □ pathG n).col M = total (cols H (Lof n M) n) (vec H (Lof n M) n) := by
  rw [col_eq_total H M, total_congr (fun s hs => cnt_eq_vec H n M s hs), col_eq_cols]

/-- The uniform assignment gives the uniform sequence of columns. -/
theorem Lof_constList (n k : ℕ) : Lof n (constList (V × PathV n) k) = uniformCols k := by
  funext j v; rfl

/-- **The uniform count, in closed form.** -/
theorem colConst_eq (k n : ℕ) :
    (H □ pathG n).colConst k = ∑ s ∈ states H (unif k), F H k n s := by
  rw [colConst, col_eq_total_vec, Lof_constList, total_uniform]

/-- **The initial condition.** A column of `k`-lists, weighted by the `n`-column uniform futures
of its states' patterns, weighs at least the uniform column. -/
def Init (k : ℕ) : Prop :=
  ∀ X : Lists V, IsKLists k X → ∀ n,
    ∑ s ∈ states H (unif k), F H k n s ≤ ∑ s ∈ states H X, Φ H k n s

/-- **The two-step hypothesis.** The seam inequality for the pattern reference, at every
horizon, on every path vector one column back and at the first seam of every `k`-list chain. -/
def TwoStep (k : ℕ) : Prop := DepthOK H (Φ H k) k 1 ∧ ShortOK H (Φ H k) k 1

/-- **The conditional theorem, counting form.** -/
theorem colConst_le_col {k : ℕ} (h2 : TwoStep H k) (hi : Init H k) (n : ℕ)
    (M : ListAssignment (V × PathV n)) (hM : IsNListAssignment M k) :
    (H □ pathG n).colConst k ≤ (H □ pathG n).col M := by
  rw [colConst_eq, col_eq_total_vec]
  have hall := allSeams_of_lookback H (Φ H k) h2.1 h2.2
  have hseams : ∀ j, j < n →
      Seam H (Φ H k) (cols H (Lof n M) j) (vec H (Lof n M) j) (Lof n M (j + 1)) (n - (j + 1)) :=
    fun j _ => hall _ (Lof_isKCols hM) j _
  have htel := total_vec_ge_fw H (Φ H k) (Lof n M) n (Φ_zero H k) hseams
  exact le_trans (hi _ (fun v => hM _) n) htel

/-- **`H □ P_{n+1}` is `k`-ECC, provided the two-step and initial hypotheses hold.** -/
theorem ecc_of_twoStep {k : ℕ} (h2 : TwoStep H k) (hi : Init H k) (n : ℕ) :
    (H □ pathG n).ECCAt k :=
  fun M hM => colConst_le_col H h2 hi n M hM

/-! ### Grids -/

/-- **The general-height conjecture.** For every height and every `k ≥ 5`, both hypotheses hold
for the path row graph. Evidence: `ai_research_notes/GRID_REVIEW_2026-09-02.md` §5.6. -/
def GeneralHeightConjecture : Prop :=
  ∀ r k : ℕ, 5 ≤ k → TwoStep (pathG r) k ∧ Init (pathG r) k

/-- **Every grid is `k`-ECC for `k ≥ 5`, from the conjecture.** `pathG r □ pathG n` is
`P_{r+1} □ P_{n+1}`. -/
theorem ecc_grid_of_conjecture (h : GeneralHeightConjecture) (r n k : ℕ) (hk : 5 ≤ k) :
    (pathG r □ pathG n).ECCAt k :=
  ecc_of_twoStep (pathG r) (h r k hk).1 (h r k hk).2 n

end GridGen
