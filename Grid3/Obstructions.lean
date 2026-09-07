/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Grid3.Middle

/-!
# Why the depth-one proof cannot cover palette four

The `k ≥ 5` proof reduces every seam to `ColOK k`, a condition one column back. This file
records an exact counterexample to its `(C1_r)` half at `k = 4`. Thus changing the arithmetic
threshold in `Grid3.Pair` cannot prove the palette-four theorem; some additional history, such
as the depth-two interface in `Grid3.DepthTwo`, is necessary.
-/

namespace Grid3

private def badX : Finset ℕ := {0, 1, 4}
private def badY : Finset ℕ := {0, 1, 2}
private def badZ : Finset ℕ := {0, 1, 3}
private def badT : Finset ℕ := {0, 1, 3, 4}
private def badM : Finset ℕ := {0, 1, 2, 3}
private def badW : Finset ℕ := {0, 1, 2, 4}

private def badC₀ : ColumnLists := (badM, badM, badM)
private def badC₁ : ColumnLists := (badW, badM, badM)
private def badC₂ : ColumnLists := (badT, badM, badM)

private def badCols (j : ℕ) : ColumnLists :=
  if j = 0 then badC₀ else if j = 1 then badC₁ else badC₂

/-- The signed `(C1_r)` deficiency of the witness is exactly `-1`. -/
theorem bad_dC_sum_four : ∑ s ∈ states badX badY badZ, dC 4 badT badM badM s = -1 := by
  unfold badX badY badZ badT badM
  decide

/-- The exact depth-one obstruction: the right side of `(C1_r)` is one less than the left. -/
theorem not_colC1r_four : ¬ ColC1r 4 badX badY badZ badT badM badM := by
  unfold ColC1r badX badY badZ badT badM
  decide

/-- Consequently the six-list depth-one condition used by the `k ≥ 5` theorem is false at four. -/
theorem not_colOK_four : ¬ ColOK 4 := by
  intro h
  exact not_colC1r_four
    (h badX badY badZ badT badM badM (by norm_num [NearK, badX])
      (by norm_num [NearK, badY]) (by norm_num [NearK, badZ]) (by norm_num [badT])
      (by norm_num [badM]) (by norm_num [badM])).2

/-- More strongly, the actual depth-one lookback condition is false at `k = 4`. The starting
state `(2,3,2)` in `badC₀` produces the punctured column `(badX,badY,badZ)` in `badC₁`, so the
next seam is exactly `not_colC1r_four`. -/
theorem not_depthOK_four_one : ¬ DepthOK 4 1 := by
  intro h
  have hL : IsKCols 4 badCols := by
    intro j
    by_cases h0 : j = 0
    · subst j
      norm_num [IsKColumn, badCols, badC₀, badM]
    by_cases h1 : j = 1
    · subst j
      norm_num [IsKColumn, badCols, badC₁, badW, badM]
    · norm_num [IsKColumn, badCols, h0, h1, badC₂, badT, badM]
  have hs : (2, 3, 2) ∈ cols badCols 0 := by
    norm_num [cols, columnStates, badCols, badC₀, badM, states]
  have hc : C1r (cols badCols 1) (pathVec badCols 0 (2, 3, 2) 1)
      (badCols 2).1 (badCols 2).2.1 (badCols 2).2.2 4 := by
    simpa using (h badCols hL 0 (2, 3, 2) hs).2
  have hp := pathVec_one badCols 0 hs
  have hcInd : C1r (cols badCols 1)
      (fun s => if s ∈ states ((badCols 1).1.erase 2) ((badCols 1).2.1.erase 3)
        ((badCols 1).2.2.erase 2) then 1 else 0)
      (badCols 2).1 (badCols 2).2.1 (badCols 2).2.2 4 :=
    C1r_congr (by simpa using hp) hc
  have hsub := states_erase_subset (badCols 1).1 (badCols 1).2.1 (badCols 1).2.2 (2, 3, 2)
  have hcSmall := (C1r_indicator_iff hsub).1 hcInd
  have hcol := (C1r_ones_iff 4 ((badCols 1).1.erase 2) ((badCols 1).2.1.erase 3)
    ((badCols 1).2.2.erase 2) (badCols 2).1 (badCols 2).2.1 (badCols 2).2.2).1 hcSmall
  have hX : (badCols 1).1.erase 2 = badX := by
    unfold badCols badC₁ badW badX
    decide
  have hY : (badCols 1).2.1.erase 3 = badY := by
    unfold badCols badC₁ badM badY
    decide
  have hZ : (badCols 1).2.2.erase 2 = badZ := by
    unfold badCols badC₁ badM badZ
    decide
  rw [hX, hY, hZ] at hcol
  exact not_colC1r_four (by simpa [badCols, badC₂, badT, badM] using hcol)

end Grid3

#print axioms Grid3.not_colOK_four
#print axioms Grid3.not_depthOK_four_one
