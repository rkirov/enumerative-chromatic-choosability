/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.Defs

/-!
# Height four: the local data of a column against the next lists

For a column `s` and next lists `B₁, …, B₄` of `k` colours, the successor lists are
`Aᵢ = Bᵢ.erase sᵢ`. Their sizes and consecutive intersections are expressed through three kinds of
local data, defined with their basic lemmas in `GridGen/Lookback/Common.lean` (they serve every
height):

* `hb B c`: the bonus, `1` when the colour `c` is missing from `B`;
* `mu k B C = k - |B ∩ C|`: the mismatch of two consecutive lists;
* `zz B C a b`: how many of `a, b` lie in the difference sets `B ∖ C`, `C ∖ B`.

This file records the four-row counting inequalities (inclusion–exclusion, and the monotonicity
of colouring counts in the lists) that the rate bounds of `LogBounds.lean` take as hypotheses,
and the sizes of a list punctured at two to four state colours.
-/

namespace GridGen.Four

open Finset GridGen.Lookback

/-! ### Counting inequalities -/

/-- The colourings of three rows whose last row lies in a smaller list. -/
theorem M3_bounds (A₁ A₂ A₃ : Finset ℕ) :
    0 ≤ (A₁.card : ℝ) * (A₂ ∩ A₃).card - (A₁ ∩ A₂ ∩ A₃).card ∧
    (A₁.card : ℝ) * (A₂ ∩ A₃).card - (A₁ ∩ A₂ ∩ A₃).card
      ≤ (A₁.card : ℝ) * A₂.card - (A₁ ∩ A₂).card := by
  have h1 := card_sts2 A₁ (A₂ ∩ A₃)
  have h2 := card_sts2 A₁ A₂
  have hsub : sts2 A₁ (A₂ ∩ A₃) ⊆ sts2 A₁ A₂ := by
    intro p hp; rw [mem_sts2] at hp ⊢; exact ⟨hp.1, (Finset.mem_inter.mp hp.2.1).1, hp.2.2⟩
  have hc := Finset.card_le_card hsub
  have heq : A₁ ∩ (A₂ ∩ A₃) = A₁ ∩ A₂ ∩ A₃ := by ext; simp
  rw [heq] at h1
  have h1' : ((sts2 A₁ (A₂ ∩ A₃)).card : ℝ) = A₁.card * (A₂ ∩ A₃).card - (A₁ ∩ A₂ ∩ A₃).card := by
    exact_mod_cast h1
  have h2' : ((sts2 A₁ A₂).card : ℝ) = A₁.card * A₂.card - (A₁ ∩ A₂).card := by exact_mod_cast h2
  have hc' : ((sts2 A₁ (A₂ ∩ A₃)).card : ℝ) ≤ (sts2 A₁ A₂).card := by exact_mod_cast hc
  constructor
  · rw [← h1']; exact Nat.cast_nonneg _
  · rw [← h1', ← h2']; exact hc'

/-- The colourings of four rows whose last row lies in a smaller list, and the count of three rows. -/
theorem M4_bounds (A₁ A₂ A₃ A₄ : Finset ℕ) :
    0 ≤ (A₁.card : ℝ) * ((A₂.card : ℝ) * (A₃ ∩ A₄).card - (A₂ ∩ A₃ ∩ A₄).card)
        - ((A₁ ∩ A₂).card * (A₃ ∩ A₄).card - (A₁ ∩ A₂ ∩ A₃ ∩ A₄).card) ∧
    (A₁.card : ℝ) * ((A₂.card : ℝ) * (A₃ ∩ A₄).card - (A₂ ∩ A₃ ∩ A₄).card)
        - ((A₁ ∩ A₂).card * (A₃ ∩ A₄).card - (A₁ ∩ A₂ ∩ A₃ ∩ A₄).card)
      ≤ (A₃.card : ℝ) * ((A₁.card : ℝ) * A₂.card - (A₁ ∩ A₂).card)
        - ((A₁.card : ℝ) * (A₂ ∩ A₃).card - (A₁ ∩ A₂ ∩ A₃).card) := by
  have hM := card_sts3 A₁ A₂ (A₃ ∩ A₄)
  have hN := card_sts3 A₁ A₂ A₃
  rw [card_sts2, card_sts2] at hM
  rw [card_sts2, card_sts2] at hN
  have e1 : A₂ ∩ (A₃ ∩ A₄) = A₂ ∩ A₃ ∩ A₄ := by ext; simp
  have e2 : A₁ ∩ A₂ ∩ (A₃ ∩ A₄) = A₁ ∩ A₂ ∩ A₃ ∩ A₄ := by ext; simp
  rw [e1, e2] at hM
  have hsub : sts3 A₁ A₂ (A₃ ∩ A₄) ⊆ sts3 A₁ A₂ A₃ := by
    intro p hp; rw [mem_sts3] at hp ⊢
    exact ⟨hp.1, hp.2.1, (Finset.mem_inter.mp hp.2.2.1).1, hp.2.2.2⟩
  have hc := Finset.card_le_card hsub
  have hM' : ((sts3 A₁ A₂ (A₃ ∩ A₄)).card : ℝ) = A₁.card * ((A₂.card : ℝ) * (A₃ ∩ A₄).card
      - (A₂ ∩ A₃ ∩ A₄).card) - ((A₁ ∩ A₂).card * (A₃ ∩ A₄).card - (A₁ ∩ A₂ ∩ A₃ ∩ A₄).card) := by
    exact_mod_cast hM
  have hN' : ((sts3 A₁ A₂ A₃).card : ℝ) = A₁.card * ((A₂.card : ℝ) * A₃.card - (A₂ ∩ A₃).card)
      - ((A₁ ∩ A₂).card * A₃.card - (A₁ ∩ A₂ ∩ A₃).card) := by exact_mod_cast hN
  have hc' : ((sts3 A₁ A₂ (A₃ ∩ A₄)).card : ℝ) ≤ (sts3 A₁ A₂ A₃).card := by exact_mod_cast hc
  constructor
  · rw [← hM']; exact Nat.cast_nonneg _
  · rw [← hM']; rw [hN'] at hc'; linarith

/-- **The count in the form used by the rates.** -/
theorem card_sts_rates (A₁ A₂ A₃ A₄ : Finset ℕ) :
    ((sts A₁ A₂ A₃ A₄).card : ℝ) =
      (A₄.card : ℝ) * ((A₃.card : ℝ) * ((A₁.card : ℝ) * A₂.card - (A₁ ∩ A₂).card)
          - ((A₁.card : ℝ) * (A₂ ∩ A₃).card - (A₁ ∩ A₂ ∩ A₃).card))
        - ((A₁.card : ℝ) * ((A₂.card : ℝ) * (A₃ ∩ A₄).card - (A₂ ∩ A₃ ∩ A₄).card)
          - ((A₁ ∩ A₂).card * (A₃ ∩ A₄).card - (A₁ ∩ A₂ ∩ A₃ ∩ A₄).card)) := by
  have h := card_sts_formula A₁ A₂ A₃ A₄
  have h' : ((sts A₁ A₂ A₃ A₄).card : ℝ) = (A₁.card : ℝ) * A₂.card * A₃.card * A₄.card
        - (A₁ ∩ A₂).card * A₃.card * A₄.card - A₁.card * (A₂ ∩ A₃).card * A₄.card
        - A₁.card * A₂.card * (A₃ ∩ A₄).card
        + (A₁ ∩ A₂ ∩ A₃).card * A₄.card + A₁.card * (A₂ ∩ A₃ ∩ A₄).card
        + (A₁ ∩ A₂).card * (A₃ ∩ A₄).card - (A₁ ∩ A₂ ∩ A₃ ∩ A₄).card := by exact_mod_cast h
  rw [h']; ring

/-! ### Lists punctured at the state colours -/

/-- A list punctured at two or three of its colours. -/
theorem card_erase2 {k : ℕ} {B : Finset ℕ} (hB : B.card = k) {a b : ℕ} (ha : a ∈ B) (hb : b ∈ B)
    (hab : a ≠ b) : (((B.erase a) ∩ (B.erase b)).card : ℝ) = (k : ℝ) - 2 := by
  have : (B.erase a) ∩ (B.erase b) = (B.erase a).erase b := by
    ext x; simp only [Finset.mem_inter, Finset.mem_erase]; tauto
  rw [this, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩),
    Finset.card_erase_of_mem ha, hB]
  have : 2 ≤ k := by
    have := Finset.card_le_card (show ({a, b} : Finset ℕ) ⊆ B by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption)
    rw [Finset.card_pair hab, hB] at this; exact this
  push_cast [Nat.sub_sub, Nat.cast_sub this]; ring

theorem card_erase3 {k : ℕ} {B : Finset ℕ} (hB : B.card = k) {a b c : ℕ} (ha : a ∈ B)
    (hb : b ∈ B) (hc : c ∈ B) (hab : a ≠ b) (hbc : b ≠ c) :
    (((B.erase a) ∩ (B.erase b) ∩ (B.erase c)).card : ℝ)
      = (k : ℝ) - 3 + (if a = c then 1 else 0) := by
  have hset : (B.erase a) ∩ (B.erase b) ∩ (B.erase c) = B \ {a, b, c} := by
    ext x; simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert,
      Finset.mem_singleton]; tauto
  have hsub : ({a, b, c} : Finset ℕ) ⊆ B := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  rw [hset, Finset.card_sdiff_of_subset hsub, hB]
  have hk := Finset.card_le_card hsub
  split_ifs with hac
  · subst hac
    have : ({a, b, a} : Finset ℕ) = {a, b} := by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [this, Finset.card_pair hab] at hk ⊢
    rw [hB] at hk
    push_cast [Nat.cast_sub hk]; ring
  · have h3 : ({a, b, c} : Finset ℕ).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc]
    rw [h3] at hk ⊢
    rw [hB] at hk
    push_cast [Nat.cast_sub hk]; ring

theorem card_erase4 {k : ℕ} {B : Finset ℕ} (hB : B.card = k) {a b c d : ℕ} (ha : a ∈ B)
    (hb : b ∈ B) (hc : c ∈ B) (hd : d ∈ B) (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) :
    (((B.erase a) ∩ (B.erase b) ∩ (B.erase c) ∩ (B.erase d)).card : ℝ)
      = (k : ℝ) - 4 + (if a = c then 1 else 0) + (if b = d then 1 else 0)
        + (if a = d then 1 else 0) := by
  have hset : (B.erase a) ∩ (B.erase b) ∩ (B.erase c) ∩ (B.erase d) = B \ {a, b, c, d} := by
    ext x; simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert,
      Finset.mem_singleton]; tauto
  have hsub : ({a, b, c, d} : Finset ℕ) ⊆ B := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  rw [hset, Finset.card_sdiff_of_subset hsub, hB]
  have hk := Finset.card_le_card hsub
  rw [hB] at hk
  have hcard : (({a, b, c, d} : Finset ℕ).card : ℝ)
      = 4 - (if a = c then 1 else 0) - (if b = d then 1 else 0) - (if a = d then 1 else 0) := by
    by_cases hac : a = c <;> by_cases hbd : b = d <;> by_cases had : a = d
    · exact absurd (hac.symm.trans had) hcd
    · subst hac hbd
      have : ({a, b, a, b} : Finset ℕ) = {a, b} := by ext; simp
      rw [this, Finset.card_pair hab]; norm_num [had]
    · exact absurd (hac.symm.trans had) hcd
    · subst hac
      have : ({a, b, a, d} : Finset ℕ) = {a, b, d} := by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
      rw [this, Finset.card_insert_of_notMem (by simp [hab, had]),
        Finset.card_pair (fun h => hbd h)]
      norm_num [hbd, had]
    · exact absurd (had.trans hbd.symm) hab
    · subst hbd
      have : ({a, b, c, b} : Finset ℕ) = {a, b, c} := by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
      rw [this, Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc]
      norm_num [hac, had]
    · subst had
      have : ({a, b, c, a} : Finset ℕ) = {a, b, c} := by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
      rw [this, Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc]
      norm_num [hac, hbd]
    · rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
        Finset.card_insert_of_notMem (by simp [hbc, hbd]), Finset.card_pair hcd]
      norm_num [hac, hbd, had]
  have : (({a, b, c, d} : Finset ℕ).card : ℝ) ≤ k := by exact_mod_cast hk
  push_cast [Nat.cast_sub hk]
  rw [hcard]; ring

end GridGen.Four
