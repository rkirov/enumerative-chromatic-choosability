/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.BitCert5

/-!
# Height five, `k = 6`: the seam inequality away from the exact quads

The analytic half of `Seam5Holds 6` (`ai_research_notes/H5_K6_LEAN_BLUEPRINT_2026-10-23.md`): for
every mismatch quad `(μ₂, μ₃, μ₄, μ₅) ∈ [0,6]⁴` outside `exactQuads5`,

* `(0,0,0,0)`: state by state, by relabelling (`seam_zero5`);
* the `38` quads of `bitQuads5`: dual certificates over the state bits (`seam_bit5`);
* every other quad: the averaged certificate `F5` (`seam_F5_quads`).
-/

namespace GridGen.Five

open Finset

/-- **The seam inequality on every quad outside the exact layer.** -/
theorem seam_nonexact5 {w : Wt5} (hw : InBox5 w) {X₁ X₂ X₃ X₄ X₅ B₁ B₂ B₃ B₄ B₅ : Finset ℕ}
    (hX₁ : 5 ≤ X₁.card) (hX₂ : 5 ≤ X₂.card) (hX₃ : 5 ≤ X₃.card) (hX₄ : 5 ≤ X₄.card)
    (hX₅ : 5 ≤ X₅.card) (hB₁ : B₁.card = 6) (hB₂ : B₂.card = 6) (hB₃ : B₃.card = 6)
    (hB₄ : B₄.card = 6) (hB₅ : B₅.card = 6) {m2 m3 m4 m5 : ℕ} (hm2 : m2 ≤ 6) (hm3 : m3 ≤ 6)
    (hm4 : m4 ≤ 6) (hm5 : m5 ≤ 6) (hq : (m2, m3, m4, m5) ∉ exactQuads5)
    (c2 : (B₁ ∩ B₂).card + m2 = 6) (c3 : (B₂ ∩ B₃).card + m3 = 6)
    (c4 : (B₃ ∩ B₄).card + m4 = 6) (c5 : (B₄ ∩ B₅).card + m5 = 6) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 6 w s ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GB w B₁ B₂ B₃ B₄ B₅ s := by
  by_cases hb : (m2, m3, m4, m5) ∈ bitQuads5
  · exact seam_bit5 hw hX₁ hX₂ hX₃ hX₄ hX₅ hB₁ hB₂ hB₃ hB₄ hB₅ hb c2 c3 c4 c5
  by_cases hz : m2 + m3 + m4 + m5 = 0
  · have e : ∀ {B C : Finset ℕ} {m : ℕ}, B.card = 6 → C.card = 6 → (B ∩ C).card + m = 6 →
        m = 0 → B = C := fun hB hC h hm =>
      Four.eq_of_mu_zero hB hC (by rw [mu_eq_of h, hm]; simp)
    have e12 := e hB₁ hB₂ c2 (by omega)
    have e23 := e hB₂ hB₃ c3 (by omega)
    have e34 := e hB₃ hB₄ c4 (by omega)
    have e45 := e hB₄ hB₅ c5 (by omega)
    subst e12 e23 e34 e45
    exact seam_zero5 hw hB₁
  · exact seam_F5_quads hw hX₁ hX₂ hX₃ hX₄ hX₅ hB₁ hB₂ hB₃ hB₄ hB₅ hm2 hm3 hm4 hm5 hq hb hz
      c2 c3 c4 c5

end GridGen.Five
