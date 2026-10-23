/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.Quads
import GridGen.Five.Small5.Disp_0001
import GridGen.Five.Small5.Disp_0010
import GridGen.Five.Small5.Disp_0002
import GridGen.Five.Small5.Disp_0011
import GridGen.Five.Small5.Disp_0020
import GridGen.Five.Small5.Disp_0101
import GridGen.Five.Small5.Disp_0110
import GridGen.Five.Small5.Disp_1001
import GridGen.Five.Small5.Disp_0021
import GridGen.Five.Small5.Disp_0030
import GridGen.Five.Small5.Disp_0111
import GridGen.Five.Small5.Disp_0120
import GridGen.Five.Small5.Disp_0201

/-!
# Height five, `k = 6`: the seam inequality at the exact quads

At the twenty-four mismatch quads `exactQuads5` (`GridGen/Five/Quads.lean`) the lists have one of
58 shapes up to row reflection (atom sizes of `B₁, …, B₅`, `Small5/Disp_*.lean`), each with an
exact certificate checked by kernel evaluation (`Small5/Cert*.lean`, `table5_ok`), which gives the
seam inequality (`Ex5.exact_seam5`, `GridGen/Five/Exact5.lean`). The eleven quads that are not
the representatives of their reflection class reduce to their reflections (`Ex5.seam_of_rev`).
-/

namespace GridGen.Five

open Finset Ex5

/-- **The height-five seam inequality at `k = 6` for the exact quads.** -/
theorem seam_exact5 {w : Wt5} (hw : InBox5 w) {X₁ X₂ X₃ X₄ X₅ B₁ B₂ B₃ B₄ B₅ : Finset ℕ}
    (hX₁ : 5 ≤ X₁.card) (hX₂ : 5 ≤ X₂.card) (hX₃ : 5 ≤ X₃.card) (hX₄ : 5 ≤ X₄.card)
    (hX₅ : 5 ≤ X₅.card) (hB₁ : B₁.card = 6) (hB₂ : B₂.card = 6) (hB₃ : B₃.card = 6)
    (hB₄ : B₄.card = 6) (hB₅ : B₅.card = 6) {m2 m3 m4 m5 : ℕ}
    (hq : (m2, m3, m4, m5) ∈ exactQuads5)
    (c2 : (B₁ ∩ B₂).card + m2 = 6) (c3 : (B₂ ∩ B₃).card + m3 = 6)
    (c4 : (B₃ ∩ B₄).card + m4 = 6) (c5 : (B₄ ∩ B₅).card + m5 = 6) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 6 w s ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GB w B₁ B₂ B₃ B₄ B₅ s := by
  have r2 : (B₂ ∩ B₁).card + m2 = 6 := by rw [Finset.inter_comm]; exact c2
  have r3 : (B₃ ∩ B₂).card + m3 = 6 := by rw [Finset.inter_comm]; exact c3
  have r4 : (B₄ ∩ B₃).card + m4 = 6 := by rw [Finset.inter_comm]; exact c4
  have r5 : (B₅ ∩ B₄).card + m5 = 6 := by rw [Finset.inter_comm]; exact c5
  simp only [exactQuads5, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hq
  rcases hq with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl,
      rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl,
      rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl,
      rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl,
      rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl,
      rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl,
      rfl, rfl⟩
  · obtain ⟨sp, hsp, hA⟩ := dispatch_0001 hB₁ hB₂ hB₃ hB₄ hB₅ c2 c3 c4 c5
    obtain ⟨hs, ha⟩ := table5_ok sp hsp
    exact exact_seam5 sp ha hs hB₁ hB₂ hB₃ hB₄ hB₅ hA hw hX₁ hX₂ hX₃ hX₄ hX₅
  · apply seam_of_rev
    obtain ⟨sp, hsp, hA⟩ := dispatch_0001 hB₅ hB₄ hB₃ hB₂ hB₁ r5 r4 r3 r2
    obtain ⟨hs, ha⟩ := table5_ok sp hsp
    exact exact_seam5 sp ha hs hB₅ hB₄ hB₃ hB₂ hB₁ hA hw hX₅ hX₄ hX₃ hX₂ hX₁
  · obtain ⟨sp, hsp, hA⟩ := dispatch_0010 hB₁ hB₂ hB₃ hB₄ hB₅ c2 c3 c4 c5
    obtain ⟨hs, ha⟩ := table5_ok sp hsp
    exact exact_seam5 sp ha hs hB₁ hB₂ hB₃ hB₄ hB₅ hA hw hX₁ hX₂ hX₃ hX₄ hX₅
  · apply seam_of_rev
    obtain ⟨sp, hsp, hA⟩ := dispatch_0010 hB₅ hB₄ hB₃ hB₂ hB₁ r5 r4 r3 r2
    obtain ⟨hs, ha⟩ := table5_ok sp hsp
    exact exact_seam5 sp ha hs hB₅ hB₄ hB₃ hB₂ hB₁ hA hw hX₅ hX₄ hX₃ hX₂ hX₁
  · obtain ⟨sp, hsp, hA⟩ := dispatch_0002 hB₁ hB₂ hB₃ hB₄ hB₅ c2 c3 c4 c5
    obtain ⟨hs, ha⟩ := table5_ok sp hsp
    exact exact_seam5 sp ha hs hB₁ hB₂ hB₃ hB₄ hB₅ hA hw hX₁ hX₂ hX₃ hX₄ hX₅
  · apply seam_of_rev
    obtain ⟨sp, hsp, hA⟩ := dispatch_0002 hB₅ hB₄ hB₃ hB₂ hB₁ r5 r4 r3 r2
    obtain ⟨hs, ha⟩ := table5_ok sp hsp
    exact exact_seam5 sp ha hs hB₅ hB₄ hB₃ hB₂ hB₁ hA hw hX₅ hX₄ hX₃ hX₂ hX₁
  · obtain ⟨sp, hsp, hA⟩ := dispatch_0020 hB₁ hB₂ hB₃ hB₄ hB₅ c2 c3 c4 c5
    obtain ⟨hs, ha⟩ := table5_ok sp hsp
    exact exact_seam5 sp ha hs hB₁ hB₂ hB₃ hB₄ hB₅ hA hw hX₁ hX₂ hX₃ hX₄ hX₅
  · apply seam_of_rev
    obtain ⟨sp, hsp, hA⟩ := dispatch_0020 hB₅ hB₄ hB₃ hB₂ hB₁ r5 r4 r3 r2
    obtain ⟨hs, ha⟩ := table5_ok sp hsp
    exact exact_seam5 sp ha hs hB₅ hB₄ hB₃ hB₂ hB₁ hA hw hX₅ hX₄ hX₃ hX₂ hX₁
  · obtain ⟨sp, hsp, hA⟩ := dispatch_0011 hB₁ hB₂ hB₃ hB₄ hB₅ c2 c3 c4 c5
    obtain ⟨hs, ha⟩ := table5_ok sp hsp
    exact exact_seam5 sp ha hs hB₁ hB₂ hB₃ hB₄ hB₅ hA hw hX₁ hX₂ hX₃ hX₄ hX₅
  · apply seam_of_rev
    obtain ⟨sp, hsp, hA⟩ := dispatch_0011 hB₅ hB₄ hB₃ hB₂ hB₁ r5 r4 r3 r2
    obtain ⟨hs, ha⟩ := table5_ok sp hsp
    exact exact_seam5 sp ha hs hB₅ hB₄ hB₃ hB₂ hB₁ hA hw hX₅ hX₄ hX₃ hX₂ hX₁
  · obtain ⟨sp, hsp, hA⟩ := dispatch_0101 hB₁ hB₂ hB₃ hB₄ hB₅ c2 c3 c4 c5
    obtain ⟨hs, ha⟩ := table5_ok sp hsp
    exact exact_seam5 sp ha hs hB₁ hB₂ hB₃ hB₄ hB₅ hA hw hX₁ hX₂ hX₃ hX₄ hX₅
  · apply seam_of_rev
    obtain ⟨sp, hsp, hA⟩ := dispatch_0101 hB₅ hB₄ hB₃ hB₂ hB₁ r5 r4 r3 r2
    obtain ⟨hs, ha⟩ := table5_ok sp hsp
    exact exact_seam5 sp ha hs hB₅ hB₄ hB₃ hB₂ hB₁ hA hw hX₅ hX₄ hX₃ hX₂ hX₁
  · obtain ⟨sp, hsp, hA⟩ := dispatch_1001 hB₁ hB₂ hB₃ hB₄ hB₅ c2 c3 c4 c5
    obtain ⟨hs, ha⟩ := table5_ok sp hsp
    exact exact_seam5 sp ha hs hB₁ hB₂ hB₃ hB₄ hB₅ hA hw hX₁ hX₂ hX₃ hX₄ hX₅
  · obtain ⟨sp, hsp, hA⟩ := dispatch_0110 hB₁ hB₂ hB₃ hB₄ hB₅ c2 c3 c4 c5
    obtain ⟨hs, ha⟩ := table5_ok sp hsp
    exact exact_seam5 sp ha hs hB₁ hB₂ hB₃ hB₄ hB₅ hA hw hX₁ hX₂ hX₃ hX₄ hX₅
  · obtain ⟨sp, hsp, hA⟩ := dispatch_0021 hB₁ hB₂ hB₃ hB₄ hB₅ c2 c3 c4 c5
    obtain ⟨hs, ha⟩ := table5_ok sp hsp
    exact exact_seam5 sp ha hs hB₁ hB₂ hB₃ hB₄ hB₅ hA hw hX₁ hX₂ hX₃ hX₄ hX₅
  · apply seam_of_rev
    obtain ⟨sp, hsp, hA⟩ := dispatch_0021 hB₅ hB₄ hB₃ hB₂ hB₁ r5 r4 r3 r2
    obtain ⟨hs, ha⟩ := table5_ok sp hsp
    exact exact_seam5 sp ha hs hB₅ hB₄ hB₃ hB₂ hB₁ hA hw hX₅ hX₄ hX₃ hX₂ hX₁
  · obtain ⟨sp, hsp, hA⟩ := dispatch_0030 hB₁ hB₂ hB₃ hB₄ hB₅ c2 c3 c4 c5
    obtain ⟨hs, ha⟩ := table5_ok sp hsp
    exact exact_seam5 sp ha hs hB₁ hB₂ hB₃ hB₄ hB₅ hA hw hX₁ hX₂ hX₃ hX₄ hX₅
  · apply seam_of_rev
    obtain ⟨sp, hsp, hA⟩ := dispatch_0030 hB₅ hB₄ hB₃ hB₂ hB₁ r5 r4 r3 r2
    obtain ⟨hs, ha⟩ := table5_ok sp hsp
    exact exact_seam5 sp ha hs hB₅ hB₄ hB₃ hB₂ hB₁ hA hw hX₅ hX₄ hX₃ hX₂ hX₁
  · obtain ⟨sp, hsp, hA⟩ := dispatch_0111 hB₁ hB₂ hB₃ hB₄ hB₅ c2 c3 c4 c5
    obtain ⟨hs, ha⟩ := table5_ok sp hsp
    exact exact_seam5 sp ha hs hB₁ hB₂ hB₃ hB₄ hB₅ hA hw hX₁ hX₂ hX₃ hX₄ hX₅
  · apply seam_of_rev
    obtain ⟨sp, hsp, hA⟩ := dispatch_0111 hB₅ hB₄ hB₃ hB₂ hB₁ r5 r4 r3 r2
    obtain ⟨hs, ha⟩ := table5_ok sp hsp
    exact exact_seam5 sp ha hs hB₅ hB₄ hB₃ hB₂ hB₁ hA hw hX₅ hX₄ hX₃ hX₂ hX₁
  · obtain ⟨sp, hsp, hA⟩ := dispatch_0120 hB₁ hB₂ hB₃ hB₄ hB₅ c2 c3 c4 c5
    obtain ⟨hs, ha⟩ := table5_ok sp hsp
    exact exact_seam5 sp ha hs hB₁ hB₂ hB₃ hB₄ hB₅ hA hw hX₁ hX₂ hX₃ hX₄ hX₅
  · apply seam_of_rev
    obtain ⟨sp, hsp, hA⟩ := dispatch_0120 hB₅ hB₄ hB₃ hB₂ hB₁ r5 r4 r3 r2
    obtain ⟨hs, ha⟩ := table5_ok sp hsp
    exact exact_seam5 sp ha hs hB₅ hB₄ hB₃ hB₂ hB₁ hA hw hX₅ hX₄ hX₃ hX₂ hX₁
  · obtain ⟨sp, hsp, hA⟩ := dispatch_0201 hB₁ hB₂ hB₃ hB₄ hB₅ c2 c3 c4 c5
    obtain ⟨hs, ha⟩ := table5_ok sp hsp
    exact exact_seam5 sp ha hs hB₁ hB₂ hB₃ hB₄ hB₅ hA hw hX₁ hX₂ hX₃ hX₄ hX₅
  · apply seam_of_rev
    obtain ⟨sp, hsp, hA⟩ := dispatch_0201 hB₅ hB₄ hB₃ hB₂ hB₁ r5 r4 r3 r2
    obtain ⟨hs, ha⟩ := table5_ok sp hsp
    exact exact_seam5 sp ha hs hB₅ hB₄ hB₃ hB₂ hB₁ hA hw hX₅ hX₄ hX₃ hX₂ hX₁

end GridGen.Five
