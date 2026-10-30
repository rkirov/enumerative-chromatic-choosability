/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Six.BitTrees

/-!
# Height six at `k = 6`: the certificate records

A certificate record (`BCert6`) is a mismatch class `μ`, a denominator `D`, a constant `K` and
pins with integer multipliers (Codex's (OpenAI) certificates,
`ai_research_notes/cx/h6k6/analytic_rational.jsonl`, with the pins written as blocks and peeling
chains and re-checked exactly by `ai_research_notes/h6k6lean/gen_bit6.py`). `certOKc` checks a
compact certificate (pins without equalities, one enumeration with the denominators `NML`),
`certOKp` the static part of a pattern-aware one and `certOKpat` its enumeration at the canonical
patterns `a, …, a + b - 1`. `seam_certc` and `seam_certp` turn passed checks into the seam.
-/

namespace GridGen.Six

open Finset

/-- A certificate record. -/
structure BCert6 where
  mu : List ℕ
  D : ℕ
  K : ℕ
  pins : List BPin6
  rt : List (List ℕ)
  qs : List (List (ℕ × ℕ))

instance : Inhabited BCert6 := ⟨⟨[], 0, 0, [], [], []⟩⟩

/-- The static checks of a certificate. -/
def certStatic (C : BCert6) : Bool :=
  decide (0 < C.D) && C.pins.all BPin6.okb && decide (lamBnd C.pins C.mu ≤ C.K) &&
    decide (C.mu.length = 5) && decide (C.rt = rowTable C.pins) &&
    decide (C.qs = lastLists C.pins)

/-- **The check of a compact certificate.** -/
def certOKc (C : BCert6) : Bool :=
  certStatic C && eqFree C.pins &&
    chkW (C.mu.getD 0 0) (C.mu.getD 1 0) (C.mu.getD 2 0) (C.mu.getD 3 0) (C.mu.getD 4 0)
      C.D C.K NMT C.rt C.qs (maskOf (fun q => eqOKp q (0, 1, 0, 1, 0, 1)) C.pins)

/-- The enumeration of a pattern-aware certificate at the patterns `a, …, a + b - 1`. -/
def certOKpat (C : BCert6) (a b : ℕ) : Bool :=
  (List.range' a b).all fun i =>
    chkW (C.mu.getD 0 0) (C.mu.getD 1 0) (C.mu.getD 2 0) (C.mu.getD 3 0) (C.mu.getD 4 0)
      C.D C.K (DRT.getD (orb (canons.getD i (0, 0, 0, 0, 0, 0))) default) C.rt C.qs
      (maskOf (fun q => eqOKp q (canons.getD i (0, 0, 0, 0, 0, 0))) C.pins)

theorem mu_five {C : BCert6} (h : C.mu.length = 5) :
    C.mu = [C.mu.getD 0 0, C.mu.getD 1 0, C.mu.getD 2 0, C.mu.getD 3 0, C.mu.getD 4 0] := by
  match C.mu, h with
  | [a, b, c, d, e], _ => rfl

section seams

variable {w : Wt6} {X₁ X₂ X₃ X₄ X₅ X₆ B₁ B₂ B₃ B₄ B₅ B₆ : Finset ℕ}

theorem seam_certc (hw : InCone6 w) (h₁ : 5 ≤ X₁.card) (h₂ : 5 ≤ X₂.card) (h₃ : 5 ≤ X₃.card)
    (h₄ : 5 ≤ X₄.card) (h₅ : 5 ≤ X₅.card) (h₆ : 5 ≤ X₆.card)
    (hB₁ : B₁.card = 6) (hB₂ : B₂.card = 6) (hB₃ : B₃.card = 6) (hB₄ : B₄.card = 6)
    (hB₅ : B₅.card = 6) (hB₆ : B₆.card = 6) {C : BCert6} (hm : MOK B₁ B₂ B₃ B₄ B₅ B₆ C.mu)
    (hC : certOKc C = true) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, GU 6 w s
      ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, GB w B₁ B₂ B₃ B₄ B₅ B₆ s := by
  simp only [certOKc, certStatic, Bool.and_eq_true, decide_eq_true_eq] at hC
  obtain ⟨⟨⟨⟨⟨⟨⟨hD, hP⟩, hL⟩, hl⟩, hrt⟩, hlam⟩, hE⟩, hk⟩ := hC
  rw [hrt, hlam] at hk
  rw [mu_five hl] at hm hL
  exact seam_compact hw h₁ h₂ h₃ h₄ h₅ h₆ hB₁ hB₂ hB₃ hB₄ hB₅ hB₆ hm hD hP hE hL NMT_ok hk

theorem seam_certp (hw : InCone6 w) (h₁ : 5 ≤ X₁.card) (h₂ : 5 ≤ X₂.card) (h₃ : 5 ≤ X₃.card)
    (h₄ : 5 ≤ X₄.card) (h₅ : 5 ≤ X₅.card) (h₆ : 5 ≤ X₆.card)
    (hB₁ : B₁.card = 6) (hB₂ : B₂.card = 6) (hB₃ : B₃.card = 6) (hB₄ : B₄.card = 6)
    (hB₅ : B₅.card = 6) (hB₆ : B₆.card = 6) {C : BCert6} (hm : MOK B₁ B₂ B₃ B₄ B₅ B₆ C.mu)
    (hS : certStatic C = true) (h0 : certOKpat C 0 13 = true) (h1 : certOKpat C 13 13 = true)
    (h2 : certOKpat C 26 13 = true) (h3 : certOKpat C 39 13 = true) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, GU 6 w s
      ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, GB w B₁ B₂ B₃ B₄ B₅ B₆ s := by
  simp only [certStatic, Bool.and_eq_true, decide_eq_true_eq] at hS
  obtain ⟨⟨⟨⟨⟨hD, hP⟩, hL⟩, hl⟩, hrt⟩, hlam⟩ := hS
  rw [mu_five hl] at hm hL
  refine seam_pattern hw h₁ h₂ h₃ h₄ h₅ h₆ hB₁ hB₂ hB₃ hB₄ hB₅ hB₆ hm hD hP hL DRT_ok fun i hi => ?_
  rw [← hrt, ← hlam]
  have pick : ∀ a b, certOKpat C a b = true → a ≤ i → i < a + b →
      chkW (C.mu.getD 0 0) (C.mu.getD 1 0) (C.mu.getD 2 0) (C.mu.getD 3 0) (C.mu.getD 4 0)
        C.D C.K (DRT.getD (orb (canons.getD i (0, 0, 0, 0, 0, 0))) default) C.rt C.qs
        (maskOf (fun q => eqOKp q (canons.getD i (0, 0, 0, 0, 0, 0))) C.pins) = true := by
    intro a b h ha hb
    exact List.all_eq_true.mp h i (List.mem_range'_1.mpr ⟨ha, hb⟩)
  rcases Nat.lt_or_ge i 13 with g | g
  · exact pick 0 13 h0 (by omega) (by omega)
  rcases Nat.lt_or_ge i 26 with g' | g'
  · exact pick 13 13 h1 g (by omega)
  rcases Nat.lt_or_ge i 39 with g'' | g''
  · exact pick 26 13 h2 g' (by omega)
  · exact pick 39 13 h3 g'' (by omega)

end seams

end GridGen.Six
