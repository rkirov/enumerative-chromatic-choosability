/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.Count5

/-!
# Height five: the universal count constant, checked (Kappa5a)

`kapOK n₁ … n₅` (`GridGen/Five/Count5.lean`) for list sizes `n₁ = 5` and all
`n₂, …, n₅ ∈ {5, 6}`, by kernel evaluation:
`128018 · N5(greedy) · n₂n₃n₄ ≥ 123125 · ∏ⱼ (nⱼ₋₁nⱼ - eⱼ)` at every profile of consecutive
intersections (`ai_research_notes/H5_K6_ANALYTIC_2026-10-23.md`, Lemma 6).
-/

namespace GridGen.Five

theorem kap_55555 : kapOK 5 5 5 5 5 = true := by decide +kernel

theorem kap_55556 : kapOK 5 5 5 5 6 = true := by decide +kernel

theorem kap_55565 : kapOK 5 5 5 6 5 = true := by decide +kernel

theorem kap_55566 : kapOK 5 5 5 6 6 = true := by decide +kernel

theorem kap_55655 : kapOK 5 5 6 5 5 = true := by decide +kernel

theorem kap_55656 : kapOK 5 5 6 5 6 = true := by decide +kernel

theorem kap_55665 : kapOK 5 5 6 6 5 = true := by decide +kernel

theorem kap_55666 : kapOK 5 5 6 6 6 = true := by decide +kernel

theorem kap_56555 : kapOK 5 6 5 5 5 = true := by decide +kernel

theorem kap_56556 : kapOK 5 6 5 5 6 = true := by decide +kernel

theorem kap_56565 : kapOK 5 6 5 6 5 = true := by decide +kernel

theorem kap_56566 : kapOK 5 6 5 6 6 = true := by decide +kernel

theorem kap_56655 : kapOK 5 6 6 5 5 = true := by decide +kernel

theorem kap_56656 : kapOK 5 6 6 5 6 = true := by decide +kernel

theorem kap_56665 : kapOK 5 6 6 6 5 = true := by decide +kernel

theorem kap_56666 : kapOK 5 6 6 6 6 = true := by decide +kernel

end GridGen.Five
