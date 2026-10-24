/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.BitCert5k.Part00
import GridGen.Four.BitCert5k.Part01
import GridGen.Four.BitCert5k.Part02
import GridGen.Four.BitCert5k.Part03
import GridGen.Four.BitCert5k.Part04
import GridGen.Four.BitCert5k.Part05
import GridGen.Four.BitCert5k.Part06
import GridGen.Four.BitCert5k.Part07
import GridGen.Four.BitCert5k.Part08
import GridGen.Four.BitCert5k.Part09
import GridGen.Four.BitCert5k.Part10
import GridGen.Four.BitCert5k.Part11
import GridGen.Four.BitCert5k.Part12
import GridGen.Four.BitCert5k.Part13
import GridGen.Four.BitCert5k.Part14
import GridGen.Four.BitCert5k.Part15

/-!
# Height four, `k = 5`: the seam inequality off the exact triples

The 201 dual certificates over the state bits (`BitCert5k/Part*.lean`), one for every mismatch
triple other than `(0,0,0)` and the fourteen exact triples, give the seam inequality there
(`seam_of_bit5k`).
-/

namespace GridGen.Four

open Finset

/-- All bit certificates. -/
def bitAll5k : List ((ℕ × ℕ × ℕ) × BitCert) :=
  List.flatten [bitPart00, bitPart01, bitPart02, bitPart03, bitPart04, bitPart05,
    bitPart06, bitPart07, bitPart08, bitPart09, bitPart10, bitPart11,
    bitPart12, bitPart13, bitPart14, bitPart15]

theorem bitAll5k_ok : ∀ x ∈ bitAll5k, bitOK x.1.1 x.1.2.1 x.1.2.2 x.2 = true := by
  intro x hx
  obtain ⟨l, hl, hx⟩ := List.mem_flatten.mp hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  exacts [bitPart00_ok x hx, bitPart01_ok x hx, bitPart02_ok x hx, bitPart03_ok x hx,
    bitPart04_ok x hx, bitPart05_ok x hx, bitPart06_ok x hx, bitPart07_ok x hx, bitPart08_ok x hx,
    bitPart09_ok x hx, bitPart10_ok x hx, bitPart11_ok x hx, bitPart12_ok x hx, bitPart13_ok x hx,
    bitPart14_ok x hx, bitPart15_ok x hx]

/-- **The seam inequality at `k = 5` for a mismatch triple with a bit certificate.** -/
theorem seam_bit_all5k {w : Wt} (hw : InBox 5 w) {X₁ X₂ X₃ X₄ B₁ B₂ B₃ B₄ : Finset ℕ}
    (h₁ : 4 ≤ X₁.card) (h₂ : 4 ≤ X₂.card) (h₃ : 4 ≤ X₃.card) (h₄ : 4 ≤ X₄.card)
    (hB₁ : B₁.card = 5) (hB₂ : B₂.card = 5) (hB₃ : B₃.card = 5) (hB₄ : B₄.card = 5)
    {m2 m3 m4 : ℕ} (c2 : (B₁ ∩ B₂).card + m2 = 5) (c3 : (B₂ ∩ B₃).card + m3 = 5)
    (c4 : (B₃ ∩ B₄).card + m4 = 5) (hmem : (m2, m3, m4) ∈ bitAll5k.map Prod.fst) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄, GU 5 w s ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄, GB w B₁ B₂ B₃ B₄ s := by
  obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hmem
  have hok := bitAll5k_ok x hx
  rw [hxe] at hok
  exact seam_of_bit5k hw h₁ h₂ h₃ h₄ hB₁ hB₂ hB₃ hB₄ c2 c3 c4 x.2 hok

end GridGen.Four
