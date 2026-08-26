/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Grid3.Graph
import Grid3.Uniform

/-!
# Height three: the conditional theorem

Two integer inequalities at every seam of every `k`-list chain — `(H1)` and `(C1_r)` of
`Grid3.Transfer` — imply that `P_3 □ P_{n+1}` is `k`-ECC. This file assembles
`Grid3.Transfer` (the telescoping), `Grid3.Uniform` (the uniform counts and the initial
condition) and `Grid3.Graph` (the graph) into that statement, and records the uniform count in
closed form.

The seam inequalities themselves are proved downstream at `k ≥ 5`. At `k = 4` the depth-one
condition used there is false and must be replaced by the depth-two interface of
`Grid3.DepthTwo`.
-/

namespace Grid3

open SimpleGraph ListColoring Finset
open scoped SimpleGraph

/-- One column consists of three `k`-lists. -/
def IsKColumn (k : ℕ) (C : ColumnLists) : Prop :=
  C.1.card = k ∧ C.2.1.card = k ∧ C.2.2.card = k

/-- A sequence of columns of `k`-lists. -/
def IsKCols (k : ℕ) (L : Cols) : Prop := ∀ j, IsKColumn k (L j)

/-- **The hypothesis.** Every seam of every chain of `k`-list columns satisfies `(H1)` and
`(C1_r)`. -/
def AllSeamsOK (k : ℕ) : Prop := ∀ L : Cols, IsKCols k L → ∀ j, SeamOK k L j

theorem Lof_isKCols {k n : ℕ} {M : ListAssignment (PathV 2 × PathV n)}
    (hM : IsNListAssignment M k) : IsKCols k (Lof n M) :=
  fun _ => ⟨hM _, hM _, hM _⟩

theorem total_congr {S : Finset State} {N N' : State → ℕ} (h : ∀ s ∈ S, N s = N' s) :
    total S N = total S N' :=
  Finset.sum_congr rfl h

/-- The colouring count is the total of the abstract chain of the assignment's lists. -/
theorem col_eq_total_vec (n : ℕ) (M : ListAssignment (PathV 2 × PathV n)) :
    (pathG 2 □ pathG n).col M = total (cols (Lof n M) n) (vec (Lof n M) n) := by
  rw [col_eq_total, total_congr (fun s hs => cnt_eq_vec n M s hs), col_eq_cols]

/-- The uniform assignment gives the uniform sequence of columns. -/
theorem Lof_constList (n k : ℕ) : Lof n (constList (PathV 2 × PathV n) k) = uniformCols k := by
  funext j; rfl

/-- **The uniform count, in closed form.** `P(P_3 □ P_{n+1}, k) = Fne k n · k(k-1)² + Dp k n · k(k-1)`
— at `k = 3`: `12, 54, 246, 1122, 5118, …`. -/
theorem colConst_eq {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    (pathG 2 □ pathG n).colConst k = Fne k n * (k * (k - 1) ^ 2) + Dp k n * (k * (k - 1)) := by
  rw [colConst, col_eq_total_vec, Lof_constList,
    total_uniform k n (fun s hs => succ_uniform hk hs) (fun s hs => eqSucc_uniform hk hs),
    sum_Fpat, card_states_uniform, card_eq_states_uniform]

/-- **The conditional theorem, counting form.** -/
theorem colConst_le_col {k : ℕ} (hk : 3 ≤ k) (hall : AllSeamsOK k) (n : ℕ)
    (M : ListAssignment (PathV 2 × PathV n)) (hM : IsNListAssignment M k) :
    (pathG 2 □ pathG n).colConst k ≤ (pathG 2 □ pathG n).col M := by
  rw [colConst_eq (by omega) n, col_eq_total_vec]
  have hseams : ∀ j, j < n → SeamOK k (Lof n M) j := fun j _ => hall _ (Lof_isKCols hM) j
  have htel := total_vec_ge_fw k (Lof n M) n hseams
  rw [sum_Fpat] at htel
  -- the initial column
  have hT : (Lof n M 0).1.card = k := hM _
  have hMm : (Lof n M 0).2.1.card = k := hM _
  have hB : (Lof n M 0).2.2.card = k := hM _
  have hst := card_states_ge hT hMm hB
  have hinit := init_cond hk hT hMm hB
  have hcd := cc_mul_Dp_le k n
  refine le_trans ?_ htel
  unfold cols columnStates
  zify at hst hinit hcd ⊢
  nlinarith [mul_le_mul_of_nonneg_left hinit (Int.natCast_nonneg (Dp k n)),
    mul_nonneg (sub_nonneg.mpr hcd) (sub_nonneg.mpr hst)]

/-- **`P_3 □ P_{n+1}` is `k`-ECC, provided every seam satisfies `(H1)` and `(C1_r)`.** -/
theorem ecc_of_allSeamsOK {k : ℕ} (hk : 3 ≤ k) (hall : AllSeamsOK k) (n : ℕ) :
    (pathG 2 □ pathG n).ECCAt k :=
  fun M hM => colConst_le_col hk hall n M hM

end Grid3
