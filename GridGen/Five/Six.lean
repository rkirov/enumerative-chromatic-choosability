/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.Small5
import GridGen.Five.Cert5

/-!
# Height five: the seam inequality at `k = 6`

The mismatches `μⱼ = 6 - |Bⱼ₋₁ ∩ Bⱼ|` form a quad of integers in `[0, 6]`. The quads of
`exactQuads5` are certified exactly, column type by column type (`seam_exact5`); every other quad
by the analytic certificate, by relabelling, or by a dual certificate over the state bits
(`seam_nonexact5`).
-/

namespace GridGen.Five

open Finset

/-- **The height-five seam inequality at `k = 6`.** -/
theorem seam5Holds_six : Seam5Holds 6 := by
  intro w hw X₁ X₂ X₃ X₄ X₅ B₁ B₂ B₃ B₄ B₅ hX₁ hX₂ hX₃ hX₄ hX₅ hB₁ hB₂ hB₃ hB₄ hB₅
  have k2 : (B₁ ∩ B₂).card ≤ 6 := hB₁ ▸ card_le_card inter_subset_left
  have k3 : (B₂ ∩ B₃).card ≤ 6 := hB₂ ▸ card_le_card inter_subset_left
  have k4 : (B₃ ∩ B₄).card ≤ 6 := hB₃ ▸ card_le_card inter_subset_left
  have k5 : (B₄ ∩ B₅).card ≤ 6 := hB₄ ▸ card_le_card inter_subset_left
  have x1 : 5 ≤ X₁.card := hX₁.1
  have x2 : 5 ≤ X₂.card := hX₂.1
  have x3 : 5 ≤ X₃.card := hX₃.1
  have x4 : 5 ≤ X₄.card := hX₄.1
  have x5 : 5 ≤ X₅.card := hX₅.1
  by_cases hq : (6 - (B₁ ∩ B₂).card, 6 - (B₂ ∩ B₃).card, 6 - (B₃ ∩ B₄).card,
      6 - (B₄ ∩ B₅).card) ∈ exactQuads5
  · exact seam_exact5 hw x1 x2 x3 x4 x5 hB₁ hB₂ hB₃ hB₄ hB₅ hq (by omega) (by omega)
      (by omega) (by omega)
  · exact seam_nonexact5 hw x1 x2 x3 x4 x5 hB₁ hB₂ hB₃ hB₄ hB₅ (by omega) (by omega)
      (by omega) (by omega) hq (by omega) (by omega) (by omega) (by omega)

end GridGen.Five
