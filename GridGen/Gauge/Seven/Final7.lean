/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Seven.Main7
import GridGen.Gauge.Seven.Drift7
import GridGen.Gauge.Seven.Box7

/-!
# The seam bounds at `k = 7`

From the box bounds (`Boxes7`) the seam bounds `K7Bounds` follow:

* the star: `γ = 432/69101` (`box_bound_seven`);
* the move: `θ = 41/200`, `ε = 1/249` (`move_H`, `move_D`, `thetaM_le`, `epsM_le`);
* the drift: `δ = 7/50` (`drift7`);
* the relaxation constant `γ_V = 27/5075`.

The numeric conditions of `Bounds7` hold for these values (`k7Bounds_of_boxes`).
-/

open Finset SimpleGraph ListColoring
open scoped Classical SimpleGraph

set_option linter.unusedSectionVars false

namespace GridGen.Gauge

/-- **The seam bounds at `k = 7`**, from the box bounds. -/
theorem k7Bounds_of_boxes (B : Boxes7) : K7Bounds := by
  intro c m P A hc hA hP
  refine ⟨⟨432 / 69101, 41 / 200, 1 / 249, 7 / 50, gammaV7, ?_, ?_, ?_, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num, by norm_num [gammaV7],
    by norm_num [gammaV7], by norm_num, by norm_num [gammaV7]⟩, rfl⟩
  · intro N hK v a₀ ha h7 hPv x₀ hx
    have h := box_bound_seven (P := P) hK hA hc v ha hx h7 hPv
    have hq : ((slab c m 7 P A N).Ω.card : ℚ) * 432 ≤
        ((slab c m 7 P A N).Ω.filter (Hit hc v a₀ x₀)).card * 69101 := by exact_mod_cast h
    unfold Z
    linarith
  · intro M hK w x y hx hy hxy r hr h hh hhole a₀ ha₀ h7
    have hθ := thetaM_le
    have hε := epsM_le
    have hH0 : (0 : ℚ) ≤ ((slab c m 7 P A M).Ω.filter (Hit hc r a₀ h)).card := by positivity
    have hZ0 : (0 : ℚ) ≤ (slab c m 7 P A M).Ω.card := by positivity
    have key : (((slab c m 7 P A M).Ω.filter (Bad hc M w x y)).card : ℚ) ≤
        thetaM * ((slab c m 7 P A M).Ω.filter (Hit hc r a₀ h)).card +
          epsM * (slab c m 7 P A M).Ω.card := by
      obtain ⟨rv, hrv⟩ := r
      simp only at hr
      rcases hr with rfl | rfl
      · exact move_D B hK hA hP hc hxy hx hy hh hrv hhole ha₀ h7
      · exact move_H B hK hA hP hc hxy hx hy hh hrv hhole ha₀ h7
    unfold Z
    have := mul_le_mul_of_nonneg_right hθ hH0
    have := mul_le_mul_of_nonneg_right hε hZ0
    linarith
  · intro M hK r x h hx hh hxh _ a₀ _ _
    exact drift7 (P := P) hK hA hc r hx hh hxh

/-- **`P_m □ P_n` is 7-ECC**, given the box bounds. -/
theorem ecc_rowG_boxProd_seven_of_boxes (B : Boxes7) (m n : ℕ) :
    (rowG m □ pathG n).ECCAt 7 :=
  ecc_rowG_boxProd_seven (k7Bounds_of_boxes B) m n

end GridGen.Gauge

namespace ListColoring

open GridGen.Gauge

/-- **Every rectangular grid is ECC at every list size at least 7**, given the box bounds. -/
theorem ecc_boxProd_pathG_of_seven_of_boxes (B : Boxes7) {k : ℕ} (hk : 7 ≤ k) (r n : ℕ) :
    (pathG r □ pathG n).ECCAt k := by
  classical
  rcases Nat.eq_or_lt_of_le hk with rfl | hk'
  · rw [SimpleGraph.ecc_iso (boxProdIsoLeft (pathG n) (pathIso r)) 7]
    convert! ecc_rowG_boxProd_seven_of_boxes B (r + 1) n
  · exact ecc_boxProd_pathG_of_eight hk' r n

end ListColoring
