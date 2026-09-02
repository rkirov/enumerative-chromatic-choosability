import Grid3.AllU

/-!
# Top-level assembly of the `k = 3` height-three ECC theorem (staging)

This scratch file records the top-level three-case split of the corrected `k = 3` proof and wires
the **all-`U`** case (Case C) to the verified `Grid3.AllU.colConst_le_col_of_allU`
(milestone 3).  The nonuniform half (`entropy_half`, Cases A/B combined) is the remaining
obligation — milestones 1, 2, 4, 6 — and is the ONLY `sorry` here.

It lives under `k3_entropy/` (outside the `Grid3` build) precisely because it still contains a
`sorry`; nothing sorry-bearing goes under `Grid3/`.
-/

open SimpleGraph Finset ListColoring
open scoped SimpleGraph

namespace Grid3.Three

/-- **Type-`U` predicate** for a column: all three row-lists agree. -/
def ColIsU (n : ℕ) (L : ListAssignment (PathV 2 × PathV n)) (c : PathV n) : Prop :=
  L (rowT, c) = L (rowM, c) ∧ L (rowM, c) = L (rowB, c)

/-- **The entropy half (Cases A + B).**  A three-list assignment with at least one nonuniform
column.  Remaining obligation: instantiate the Markov model and certificate (milestones 1, 2, 4, 6)
and apply `entropy_half_from_card` / `entropy_half_from_card_one_bonus`. -/
theorem entropy_half (n : ℕ) (L : ListAssignment (PathV 2 × PathV n))
    (h3 : IsNListAssignment L 3) (hne : ∃ c, ¬ ColIsU n L c) :
    (pathG 2 □ pathG n).colConst 3 ≤ (pathG 2 □ pathG n).col L := by
  sorry

/-- **Height-three grids are `3`-ECC.**  The `k = 3` case of `ecc_boxProd_pathG_two`, via the
three-case split: all columns type `U` (Case C, `Grid3.AllU.colConst_le_col_of_allU`), or some
column nonuniform (Cases A/B, `entropy_half`). -/
theorem ecc_grid3_three (n : ℕ) : (pathG 2 □ pathG n).ECCAt 3 := by
  intro L h3
  by_cases hall : ∀ c, ColIsU n L c
  · -- Case C: every column is type U.
    apply Grid3.AllU.colConst_le_col_of_allU n L h3
    intro r c
    rcases Grid3.row_eq r with h | h | h
    · rw [h]
    · rw [h]; exact (hall c).1.symm
    · rw [h]; exact ((hall c).1.trans (hall c).2).symm
  · -- Cases A/B: some column is nonuniform.
    rw [not_forall] at hall
    exact entropy_half n L h3 hall

end Grid3.Three
