/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Grid3.Four.Depth

/-!
# Height-three grids are `4`-ECC

The two obligations of `Grid3.DepthTwo` — the first two seams of every chain, and the seam two
columns after any state — both follow from the core inequality `Grid3.Four.sum_GC_nonneg` (and
its `(H1)` companion), via the vector identities of `Grid3.Four.Depth`.
-/

open Finset

namespace Grid3
namespace Four

/-- **The depth-two local condition at `k = 4`.** -/
theorem depthTwoLocalOK_four : DepthTwoLocalOK 4 := by
  intro C₀ C₁ C₂ C₃ _ h1 h2 h3 s₀ _
  refine localSeamOK_of_sums (twoStepVec_eq C₁ C₂ s₀) ?_ ?_
  · exact sum_GH_nonneg h2 h3
  · exact sum_GC_nonneg (nearK_erase h1.1 _) (nearK_erase h1.2.2 _) h2 h3

/-- **The first two seams at `k = 4`.** -/
theorem initialTwoSeamsOK_four : InitialTwoSeamsOK 4 := by
  intro C₀ C₁ C₂ h0 h1 h2
  obtain ⟨hT0, hM0, hB0⟩ := h0
  refine ⟨?_, ?_⟩
  · -- the first seam: the all-ones vector on `C₀`
    unfold LocalSeamOK columnStates
    refine ⟨(H1_ones_iff _ _ _ _ _ _ _).mpr ?_, (C1r_ones_iff _ _ _ _ _ _ _).mpr ?_⟩
    · exact colH1_of_sum (colH_four (nearK_of_card hT0) (nearK_of_card hM0)
        (nearK_of_card hB0) h1.1 h1.2.1 h1.2.2)
    · refine colC1r_of_sum ?_
      rcases colC_or (nearK_of_card hT0) (nearK_of_card hM0) (nearK_of_card hB0) h1.1
          h1.2.1 h1.2.2 with h | ⟨y₀, hy₀, hyM, hirr, hb⟩
      · exact h
      · -- a full column of `4`-lists cannot be Bad: a punctured list would have three colours
        exfalso
        rcases hb with hb | hb
        · rcases hb with ⟨_, _, _, _, _, _, hZ3, _, _, _, _, _⟩
          omega
        · rcases hb with ⟨_, _, _, _, _, hX3, _, _, _, _, _, _⟩
          omega
  · -- the second seam: the vector after one transfer
    exact localSeamOK_of_sums (stepOnes_eq C₀ C₁)
      (sum_GH_nonneg h1 h2)
      (sum_GC_nonneg (nearK_of_card hT0) (nearK_of_card hB0) h1 h2)

/-- **Height-three grids are `4`-ECC.** -/
theorem ecc_grid3_four (n : ℕ) : (ListColoring.pathG 2 □ ListColoring.pathG n).ECCAt 4 :=
  ecc_grid3_four_of_depthTwo initialTwoSeamsOK_four depthTwoLocalOK_four n

end Four
end Grid3
