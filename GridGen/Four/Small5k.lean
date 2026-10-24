/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.Small5k.Dispatch

/-!
# Height four, `k = 5`: the seam inequality at the fourteen exact mismatch triples

At the fourteen triples of `ExactTriple5k` (`ai_research_notes/H4_K5_ANALYTIC_2026-10-24.md` §4,
with `(0,1,2)` and `(2,1,0)` moved here by `H4_K5_REVIEW_2026-10-24.md` fix 1) the lists have one
of 59 shapes (atom sizes of `B₁, …, B₄`, `dispatch5k`), each with an exact certificate checked by
kernel evaluation (`Small5k/Cert*.lean`, `table5k_ok`), which gives the seam inequality
(`exact_seam5k`).
-/

namespace GridGen.Four

open Finset

/-- **The height-four seam inequality at `k = 5` for the fourteen exact mismatch triples.** -/
theorem seam_exact5k {w : Wt} (hw : InBox 5 w) {X₁ X₂ X₃ X₄ B₁ B₂ B₃ B₄ : Finset ℕ}
    (hX₁ : 4 ≤ X₁.card) (hX₂ : 4 ≤ X₂.card) (hX₃ : 4 ≤ X₃.card) (hX₄ : 4 ≤ X₄.card)
    (hB₁ : B₁.card = 5) (hB₂ : B₂.card = 5) (hB₃ : B₃.card = 5) (hB₄ : B₄.card = 5)
    {m2 m3 m4 : ℕ} (hs : ExactTriple5k m2 m3 m4)
    (h12 : (B₁ ∩ B₂).card + m2 = 5) (h23 : (B₂ ∩ B₃).card + m3 = 5)
    (h34 : (B₃ ∩ B₄).card + m4 = 5) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄, GU 5 w s ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄, GB w B₁ B₂ B₃ B₄ s := by
  obtain ⟨sp, hsp, hA⟩ := dispatch5k hs hB₁ hB₂ hB₃ hB₄ h12 h23 h34
  obtain ⟨hok, hspec⟩ := table5k_ok sp hsp
  exact exact_seam5k sp hok hspec hA hw hX₁ hX₂ hX₃ hX₄

end GridGen.Four
