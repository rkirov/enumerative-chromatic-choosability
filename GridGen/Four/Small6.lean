/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.Small6.Dispatch

/-!
# Height four, `k = 6`: the seam inequality at the sixteen small mismatch triples

At `k = 6` the averaged analytic certificate fails at sixteen mismatch triples `(μ₂, μ₃, μ₄)`
(`ExactTriple6`; `(0,0,0)` is not among them). There the lists have one of 69 shapes (atom sizes
of `B₁, …, B₄`, `dispatch6`), each with an exact certificate checked by kernel evaluation
(`Small6/Cert*.lean`, `table6_ok`), which gives the seam inequality (`exact_seam6`).
-/

namespace GridGen.Four

open Finset

/-- **The height-four seam inequality at `k = 6` for the sixteen small mismatch triples.** -/
theorem seam_exact6 {w : Wt} (hw : InBox 6 w) {X₁ X₂ X₃ X₄ B₁ B₂ B₃ B₄ : Finset ℕ}
    (hX₁ : 5 ≤ X₁.card) (hX₂ : 5 ≤ X₂.card) (hX₃ : 5 ≤ X₃.card) (hX₄ : 5 ≤ X₄.card)
    (hB₁ : B₁.card = 6) (hB₂ : B₂.card = 6) (hB₃ : B₃.card = 6) (hB₄ : B₄.card = 6)
    {m2 m3 m4 : ℕ} (hs : ExactTriple6 m2 m3 m4)
    (h12 : (B₁ ∩ B₂).card + m2 = 6) (h23 : (B₂ ∩ B₃).card + m3 = 6)
    (h34 : (B₃ ∩ B₄).card + m4 = 6) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄, GU 6 w s ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄, GB w B₁ B₂ B₃ B₄ s := by
  obtain ⟨sp, hsp, hA⟩ := dispatch6 hs hB₁ hB₂ hB₃ hB₄ h12 h23 h34
  obtain ⟨hok, hspec⟩ := table6_ok sp hsp
  exact exact_seam6 sp hok hspec hA hw hX₁ hX₂ hX₃ hX₄

end GridGen.Four
