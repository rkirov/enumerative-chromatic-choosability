/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.Kappa5a

/-!
# Height five: the universal count constant, checked (Kappa5b)

`kapOK n₁ … n₅` (`GridGen/Five/Count5.lean`) for list sizes `n₁ = 6` and all
`n₂, …, n₅ ∈ {5, 6}`, by kernel evaluation:
`128018 · N5(greedy) · n₂n₃n₄ ≥ 123125 · ∏ⱼ (nⱼ₋₁nⱼ - eⱼ)` at every profile of consecutive
intersections (`ai_research_notes/H5_K6_ANALYTIC_2026-10-23.md`, Lemma 6).
-/

namespace GridGen.Five

theorem kap_65555 : kapOK 6 5 5 5 5 = true := by decide +kernel

theorem kap_65556 : kapOK 6 5 5 5 6 = true := by decide +kernel

theorem kap_65565 : kapOK 6 5 5 6 5 = true := by decide +kernel

theorem kap_65566 : kapOK 6 5 5 6 6 = true := by decide +kernel

theorem kap_65655 : kapOK 6 5 6 5 5 = true := by decide +kernel

theorem kap_65656 : kapOK 6 5 6 5 6 = true := by decide +kernel

theorem kap_65665 : kapOK 6 5 6 6 5 = true := by decide +kernel

theorem kap_65666 : kapOK 6 5 6 6 6 = true := by decide +kernel

theorem kap_66555 : kapOK 6 6 5 5 5 = true := by decide +kernel

theorem kap_66556 : kapOK 6 6 5 5 6 = true := by decide +kernel

theorem kap_66565 : kapOK 6 6 5 6 5 = true := by decide +kernel

theorem kap_66566 : kapOK 6 6 5 6 6 = true := by decide +kernel

theorem kap_66655 : kapOK 6 6 6 5 5 = true := by decide +kernel

theorem kap_66656 : kapOK 6 6 6 5 6 = true := by decide +kernel

theorem kap_66665 : kapOK 6 6 6 6 5 = true := by decide +kernel

theorem kap_66666 : kapOK 6 6 6 6 6 = true := by decide +kernel

/-- **The universal count constant** for all list sizes in `{5, 6}`. -/
theorem kapOK_all {n1 n2 n3 n4 n5 : ℕ} (h1 : n1 = 5 ∨ n1 = 6) (h2 : n2 = 5 ∨ n2 = 6)
    (h3 : n3 = 5 ∨ n3 = 6) (h4 : n4 = 5 ∨ n4 = 6) (h5 : n5 = 5 ∨ n5 = 6) :
    kapOK n1 n2 n3 n4 n5 = true := by
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> rcases h3 with rfl | rfl <;>
    rcases h4 with rfl | rfl <;> rcases h5 with rfl | rfl
  · exact kap_55555
  · exact kap_55556
  · exact kap_55565
  · exact kap_55566
  · exact kap_55655
  · exact kap_55656
  · exact kap_55665
  · exact kap_55666
  · exact kap_56555
  · exact kap_56556
  · exact kap_56565
  · exact kap_56566
  · exact kap_56655
  · exact kap_56656
  · exact kap_56665
  · exact kap_56666
  · exact kap_65555
  · exact kap_65556
  · exact kap_65565
  · exact kap_65566
  · exact kap_65655
  · exact kap_65656
  · exact kap_65665
  · exact kap_65666
  · exact kap_66555
  · exact kap_66556
  · exact kap_66565
  · exact kap_66566
  · exact kap_66655
  · exact kap_66656
  · exact kap_66665
  · exact kap_66666

end GridGen.Five
