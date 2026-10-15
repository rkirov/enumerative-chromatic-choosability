/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.Defs

/-!
# Height four: the local data of a column against the next lists

For a column `s` and next lists `B₁, …, B₄` of `k` colours, the successor lists are
`Aᵢ = Bᵢ.erase sᵢ`. This file expresses their sizes and consecutive intersections through three
kinds of local data:

* `hb B c`: the bonus, `1` when the colour `c` is missing from `B`;
* `mu k B C = k - |B ∩ C|`: the mismatch of two consecutive lists;
* `zz B C a b`: how many of `a, b` lie in the difference sets `B ∖ C`, `C ∖ B`;

and records the counting inequalities (inclusion–exclusion, and the monotonicity of colouring
counts in the lists) that the rate bounds of `LogBounds.lean` take as hypotheses.
-/

namespace GridGen.Four

open Finset

/-- The bonus of a colour against a list. -/
noncomputable def hb (B : Finset ℕ) (c : ℕ) : ℝ := if c ∈ B then 0 else 1

/-- The mismatch of two lists of `k` colours. -/
noncomputable def mu (k : ℕ) (B C : Finset ℕ) : ℝ := (k : ℝ) - (B ∩ C).card

/-- State colours in the difference sets: `a ∈ B ∖ C` and `b ∈ C ∖ B`. -/
noncomputable def zz (B C : Finset ℕ) (a b : ℕ) : ℝ :=
  (if a ∈ B ∧ a ∉ C then 1 else 0) + (if b ∈ C ∧ b ∉ B then 1 else 0)

theorem hb_cases (B : Finset ℕ) (c : ℕ) : hb B c = 0 ∨ hb B c = 1 := by
  unfold hb; split_ifs <;> simp

theorem zz_nonneg (B C : Finset ℕ) (a b : ℕ) : 0 ≤ zz B C a b := by
  unfold zz; split_ifs <;> norm_num

theorem mu_nonneg {k : ℕ} {B C : Finset ℕ} (hB : B.card = k) : 0 ≤ mu k B C := by
  unfold mu
  have : (B ∩ C).card ≤ k := hB ▸ Finset.card_le_card Finset.inter_subset_left
  have : ((B ∩ C).card : ℝ) ≤ k := by exact_mod_cast this
  linarith

theorem mu_le {k : ℕ} (B C : Finset ℕ) : mu k B C ≤ k := by
  unfold mu; have : (0 : ℝ) ≤ (B ∩ C).card := Nat.cast_nonneg _; linarith

/-- Equal lists from zero mismatch. -/
theorem eq_of_mu_zero {k : ℕ} {B C : Finset ℕ} (hB : B.card = k) (hC : C.card = k)
    (h : mu k B C = 0) : B = C := by
  unfold mu at h
  have hc : (B ∩ C).card = k := by
    have : ((B ∩ C).card : ℝ) = k := by linarith
    exact_mod_cast this
  have h1 : B ∩ C = B := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
  have h2 : B ∩ C = C := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
  rw [← h1, h2]

/-- The size of a punctured list. -/
theorem card_erase_hb {k : ℕ} {B : Finset ℕ} (hB : B.card = k) (c : ℕ) :
    ((B.erase c).card : ℝ) = (k : ℝ) - 1 + hb B c := by
  unfold hb
  split_ifs with h
  · rw [Finset.card_erase_of_mem h, hB]
    have : 1 ≤ k := hB ▸ Finset.card_pos.mpr ⟨c, h⟩
    push_cast [Nat.cast_sub this]; ring
  · rw [Finset.erase_eq_of_notMem h, hB]; ring

/-- **Consecutive punctured lists.** -/
theorem card_inter_erase {k : ℕ} {B C : Finset ℕ} (hB : B.card = k) (hC : C.card = k)
    {a b : ℕ} (hab : a ≠ b) :
    (((B.erase a) ∩ (C.erase b)).card : ℝ) = ((k : ℝ) - mu k B C - 2) + hb B a + hb C b + zz B C a b := by
  have hset : (B.erase a) ∩ (C.erase b) = ((B ∩ C).erase a).erase b := by
    ext x; simp only [Finset.mem_inter, Finset.mem_erase]; tauto
  rw [hset]
  have e1 : ((((B ∩ C).erase a).erase b).card : ℝ)
      = (B ∩ C).card - (if a ∈ B ∩ C then 1 else 0) - (if b ∈ B ∩ C then 1 else 0) := by
    have hb' : b ∈ (B ∩ C).erase a ↔ b ∈ B ∩ C := by
      rw [Finset.mem_erase]; exact ⟨fun h => h.2, fun h => ⟨Ne.symm hab, h⟩⟩
    by_cases ha : a ∈ B ∩ C <;> by_cases hbm : b ∈ B ∩ C
    · rw [Finset.card_erase_of_mem (hb'.mpr hbm), Finset.card_erase_of_mem ha]
      have h1 : 1 ≤ (B ∩ C).card := Finset.card_pos.mpr ⟨a, ha⟩
      have h2 : 1 ≤ ((B ∩ C).erase a).card := Finset.card_pos.mpr ⟨b, hb'.mpr hbm⟩
      rw [Finset.card_erase_of_mem ha] at h2
      simp only [ha, hbm, if_true]; push_cast [Nat.cast_sub h1, Nat.cast_sub h2]; ring
    · rw [Finset.erase_eq_of_notMem (fun h => hbm (hb'.mp h)), Finset.card_erase_of_mem ha]
      have h1 : 1 ≤ (B ∩ C).card := Finset.card_pos.mpr ⟨a, ha⟩
      simp only [ha, hbm, if_true, if_false]; push_cast [Nat.cast_sub h1]; ring
    · rw [Finset.card_erase_of_mem (hb'.mpr hbm), Finset.erase_eq_of_notMem ha]
      have h1 : 1 ≤ (B ∩ C).card := Finset.card_pos.mpr ⟨b, hbm⟩
      simp only [ha, hbm, if_true, if_false]; push_cast [Nat.cast_sub h1]; ring
    · rw [Finset.erase_eq_of_notMem (fun h => hbm (hb'.mp h)), Finset.erase_eq_of_notMem ha]
      simp only [ha, hbm, if_false]; ring
  rw [e1]
  unfold mu hb zz
  simp only [Finset.mem_inter]
  by_cases haB : a ∈ B <;> by_cases haC : a ∈ C <;> by_cases hbB : b ∈ B <;> by_cases hbC : b ∈ C <;>
    simp [haB, haC, hbB, hbC] <;> (try ring)

/-! ### Counting inequalities -/

/-- Inclusion–exclusion inside the middle list. -/
theorem triple_ge (X Y Z : Finset ℕ) :
    ((X ∩ Y).card : ℝ) + (Y ∩ Z).card - Y.card ≤ (X ∩ Y ∩ Z).card := by
  have h := Finset.card_union_add_card_inter (X ∩ Y) (Y ∩ Z)
  have hsub : (X ∩ Y) ∪ (Y ∩ Z) ⊆ Y := Finset.union_subset Finset.inter_subset_right
    Finset.inter_subset_left
  have hle := Finset.card_le_card hsub
  have heq : (X ∩ Y) ∩ (Y ∩ Z) = X ∩ Y ∩ Z := by ext; simp only [Finset.mem_inter]; tauto
  rw [heq] at h
  have : ((X ∩ Y).card : ℝ) + (Y ∩ Z).card = ((X ∩ Y) ∪ (Y ∩ Z)).card + (X ∩ Y ∩ Z).card := by
    exact_mod_cast h.symm
  have : (((X ∩ Y) ∪ (Y ∩ Z)).card : ℝ) ≤ Y.card := by exact_mod_cast hle
  linarith

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
