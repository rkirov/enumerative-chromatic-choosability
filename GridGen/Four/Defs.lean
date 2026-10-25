/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Lookback.Common

/-!
# Height four: columns of four rows as tuples

The concrete model behind `GridGen/Four/`: a column state is a 4-tuple of colours (rows 1..4,
a path), proper when consecutive rows differ, and two states of adjacent columns are compatible
when they differ in every row. The proper colourings of the path from lists `A, B, C, D` are
`sts A B C D`. Their number has an exact inclusion–exclusion form in the sizes of the lists and
of their consecutive intersections (`card_sts`), obtained by prepending one row at a time:
a new first row with list `A` multiplies the count by `|A|` and subtracts the colourings whose
old first row already lies in `A` (`GridGen.Lookback.card_prepend`). The count of a triangle, a
row avoiding both rows of a two-row tail (`card_triangle`), and the lower bound
`|sts X| ≥ k(k-1)³ + k(k-2)·Σ|Xᵢ₋₁ ∖ Xᵢ|` for `k`-lists (`card_sts_gain`) serve heights four and
five alike. The helpers that do not mention the rows at all are in
`GridGen/Lookback/Common.lean`.
-/

namespace GridGen.Four

open Finset GridGen.Lookback

/-- A column of four rows. -/
abbrev T4 := ℕ × ℕ × ℕ × ℕ

/-- Rows of a column. -/
@[reducible] def r1 (t : T4) : ℕ := t.1
@[reducible] def r2 (t : T4) : ℕ := t.2.1
@[reducible] def r3 (t : T4) : ℕ := t.2.2.1
@[reducible] def r4 (t : T4) : ℕ := t.2.2.2

/-! ### Proper colourings of paths of two, three and four rows -/

/-- Proper colourings of a path of two rows. -/
def sts2 (C D : Finset ℕ) : Finset (ℕ × ℕ) := (C ×ˢ D).filter (fun p => p.1 ≠ p.2)

/-- Proper colourings of a path of three rows. -/
def sts3 (B C D : Finset ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (B ×ˢ sts2 C D).filter (fun p => p.1 ≠ p.2.1)

/-- Proper colourings of a path of four rows. -/
def sts (A B C D : Finset ℕ) : Finset T4 :=
  (A ×ˢ sts3 B C D).filter (fun p => p.1 ≠ p.2.1)

theorem mem_sts2 {C D : Finset ℕ} {p : ℕ × ℕ} : p ∈ sts2 C D ↔ p.1 ∈ C ∧ p.2 ∈ D ∧ p.1 ≠ p.2 := by
  simp [sts2, and_assoc]

theorem mem_sts3 {B C D : Finset ℕ} {p : ℕ × ℕ × ℕ} :
    p ∈ sts3 B C D ↔ p.1 ∈ B ∧ p.2.1 ∈ C ∧ p.2.2 ∈ D ∧ p.1 ≠ p.2.1 ∧ p.2.1 ≠ p.2.2 := by
  simp [sts3, mem_sts2]; tauto

theorem mem_sts {A B C D : Finset ℕ} {t : T4} :
    t ∈ sts A B C D ↔ r1 t ∈ A ∧ r2 t ∈ B ∧ r3 t ∈ C ∧ r4 t ∈ D ∧
      r1 t ≠ r2 t ∧ r2 t ≠ r3 t ∧ r3 t ≠ r4 t := by
  simp [sts, mem_sts3]; tauto

theorem card_sts2 (C D : Finset ℕ) : ((sts2 C D).card : ℤ) = C.card * D.card - (C ∩ D).card := by
  have h := card_prepend C D id
  simp only [id] at h
  rw [sts2, h, Finset.filter_mem_eq_inter, Finset.inter_comm]

theorem card_sts3 (B C D : Finset ℕ) :
    ((sts3 B C D).card : ℤ) = B.card * (sts2 C D).card - (sts2 (B ∩ C) D).card := by
  rw [sts3, card_prepend B (sts2 C D) Prod.fst]
  have h : (sts2 C D).filter (fun r => r.1 ∈ B) = sts2 (B ∩ C) D := by
    ext p; simp only [Finset.mem_filter, mem_sts2, Finset.mem_inter]; tauto
  rw [h]

theorem card_sts (A B C D : Finset ℕ) :
    ((sts A B C D).card : ℤ) = A.card * (sts3 B C D).card - (sts3 (A ∩ B) C D).card := by
  rw [sts, card_prepend A (sts3 B C D) Prod.fst]
  have h : (sts3 B C D).filter (fun r => r.1 ∈ A) = sts3 (A ∩ B) C D := by
    ext p; simp only [Finset.mem_filter, mem_sts3, Finset.mem_inter]; tauto
  rw [h]

/-- **The exact count of a four-row column.** -/
theorem card_sts_formula (A B C D : Finset ℕ) :
    ((sts A B C D).card : ℤ) =
      A.card * B.card * C.card * D.card
        - (A ∩ B).card * C.card * D.card - A.card * (B ∩ C).card * D.card
        - A.card * B.card * (C ∩ D).card
        + (A ∩ B ∩ C).card * D.card + A.card * (B ∩ C ∩ D).card
        + (A ∩ B).card * (C ∩ D).card - (A ∩ B ∩ C ∩ D).card := by
  rw [card_sts, card_sts3, card_sts3, card_sts2, card_sts2, card_sts2]
  ring

/-- A triangle with lists `S`, `X`, `Y`. -/
theorem card_triangle (S X Y : Finset ℕ) :
    (((S ×ˢ sts2 X Y).filter (fun p => p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2)).card : ℤ) =
      S.card * (X.card * Y.card - (X ∩ Y).card) - ((X ∩ S).card * Y.card - (X ∩ S ∩ Y).card)
        - (X.card * (Y ∩ S).card - (X ∩ (Y ∩ S)).card) := by
  have h := card_pairAvoid S (sts2 X Y) Prod.fst Prod.snd
  have e1 : (sts2 X Y).filter (fun r => r.1 ∈ S) = sts2 (X ∩ S) Y := by
    ext p; simp only [Finset.mem_filter, mem_sts2, Finset.mem_inter]; tauto
  have e2 : (sts2 X Y).filter (fun r => r.2 ∈ S) = sts2 X (Y ∩ S) := by
    ext p; simp only [Finset.mem_filter, mem_sts2, Finset.mem_inter]; tauto
  have e3 : (sts2 X Y).filter (fun r => r.1 ∈ S ∧ r.1 = r.2) = ∅ := by
    ext p; simp only [Finset.mem_filter, mem_sts2, Finset.notMem_empty, iff_false]; tauto
  rw [e1, e2, e3, Finset.card_empty, card_sts2, card_sts2, card_sts2] at h
  rw [h]; push_cast; ring

/-- **The count gain.** For `k`-lists, the number of proper columns exceeds the constant count
`k(k-1)³` by at least `k(k-2)` per consecutive mismatch. -/
theorem card_sts_gain {k : ℕ} {X₁ X₂ X₃ X₄ : Finset ℕ} (h₁ : X₁.card = k) (h₂ : X₂.card = k)
    (h₃ : X₃.card = k) (h₄ : X₄.card = k) (hk : 1 ≤ k) :
    (k : ℤ) * (k - 1) ^ 3 + k * (k - 2) * ((X₁ \ X₂).card + (X₂ \ X₃).card + (X₃ \ X₄).card)
      ≤ (sts X₁ X₂ X₃ X₄).card := by
  rw [card_sts_formula]
  have e12 := Finset.card_sdiff_add_card_inter X₁ X₂
  have e23 := Finset.card_sdiff_add_card_inter X₂ X₃
  have e34 := Finset.card_sdiff_add_card_inter X₃ X₄
  -- the triple intersections
  have t123 : (X₁ ∩ X₂).card + (X₂ ∩ X₃).card ≤ (X₁ ∩ X₂ ∩ X₃).card + k := by
    have h := Finset.card_union_add_card_inter (X₁ ∩ X₂) (X₂ ∩ X₃)
    have hi : X₁ ∩ X₂ ∩ (X₂ ∩ X₃) = X₁ ∩ X₂ ∩ X₃ := by
      ext x; simp only [mem_inter]; tauto
    have hu : (X₁ ∩ X₂ ∪ X₂ ∩ X₃).card ≤ X₂.card :=
      Finset.card_le_card (Finset.union_subset inter_subset_right inter_subset_left)
    rw [hi] at h
    omega
  have t234 : (X₂ ∩ X₃).card + (X₃ ∩ X₄).card ≤ (X₂ ∩ X₃ ∩ X₄).card + k := by
    have h := Finset.card_union_add_card_inter (X₂ ∩ X₃) (X₃ ∩ X₄)
    have hi : X₂ ∩ X₃ ∩ (X₃ ∩ X₄) = X₂ ∩ X₃ ∩ X₄ := by
      ext x; simp only [mem_inter]; tauto
    have hu : (X₂ ∩ X₃ ∪ X₃ ∩ X₄).card ≤ X₃.card :=
      Finset.card_le_card (Finset.union_subset inter_subset_right inter_subset_left)
    rw [hi] at h
    omega
  have hq : (X₁ ∩ X₂ ∩ X₃ ∩ X₄).card ≤ (X₂ ∩ X₃ ∩ X₄).card := by
    apply Finset.card_le_card
    intro x; simp only [mem_inter]; tauto
  rw [h₁, h₂, h₃, h₄]
  set μ₂ := (X₁ \ X₂).card
  set μ₃ := (X₂ \ X₃).card
  set μ₄ := (X₃ \ X₄).card
  set a₁₂ := (X₁ ∩ X₂).card
  set a₂₃ := (X₂ ∩ X₃).card
  set a₃₄ := (X₃ ∩ X₄).card
  set t₁ := (X₁ ∩ X₂ ∩ X₃).card
  set t₂ := (X₂ ∩ X₃ ∩ X₄).card
  set q := (X₁ ∩ X₂ ∩ X₃ ∩ X₄).card
  have z12 : (a₁₂ : ℤ) = k - μ₂ := by omega
  have z23 : (a₂₃ : ℤ) = k - μ₃ := by omega
  have z34 : (a₃₄ : ℤ) = k - μ₄ := by omega
  have zt1 : (k : ℤ) - μ₂ - μ₃ ≤ t₁ := by omega
  have zt2 : (k : ℤ) - μ₃ - μ₄ ≤ t₂ := by omega
  have zq : (q : ℤ) ≤ t₂ := by exact_mod_cast hq
  have hk1 : (1 : ℤ) ≤ k := by exact_mod_cast hk
  rw [z12, z23, z34]
  nlinarith [mul_nonneg (by positivity : (0 : ℤ) ≤ k) (by linarith : (0 : ℤ) ≤ t₁ - (k - μ₂ - μ₃)),
    mul_nonneg (by linarith : (0 : ℤ) ≤ k - 1) (by linarith : (0 : ℤ) ≤ t₂ - (k - μ₃ - μ₄)),
    mul_nonneg (by positivity : (0 : ℤ) ≤ μ₂) (by positivity : (0 : ℤ) ≤ μ₄),
    mul_nonneg (by positivity : (0 : ℤ) ≤ μ₃) (by linarith : (0 : ℤ) ≤ k - 1),
    mul_nonneg (by positivity : (0 : ℤ) ≤ μ₄) (by linarith : (0 : ℤ) ≤ k - 1)]

/-! ### Compatibility and the successors of a state -/

/-- Rowwise distinct: compatibility of adjacent columns. -/
def compat (s t : T4) : Prop := r1 s ≠ r1 t ∧ r2 s ≠ r2 t ∧ r3 s ≠ r3 t ∧ r4 s ≠ r4 t

instance (s t : T4) : Decidable (compat s t) := by unfold compat; infer_instance

/-- The successors of `s` in a column with lists `A, B, C, D` are the proper colourings from the
punctured lists. -/
theorem filter_compat_sts (s : T4) (A B C D : Finset ℕ) :
    (sts A B C D).filter (compat s) =
      sts (A.erase (r1 s)) (B.erase (r2 s)) (C.erase (r3 s)) (D.erase (r4 s)) := by
  ext t
  simp only [Finset.mem_filter, mem_sts, compat, Finset.mem_erase]
  constructor
  · rintro ⟨⟨h1, h2, h3, h4, p1, p2, p3⟩, c1, c2, c3, c4⟩
    exact ⟨⟨Ne.symm c1, h1⟩, ⟨Ne.symm c2, h2⟩, ⟨Ne.symm c3, h3⟩, ⟨Ne.symm c4, h4⟩, p1, p2, p3⟩
  · rintro ⟨⟨c1, h1⟩, ⟨c2, h2⟩, ⟨c3, h3⟩, ⟨c4, h4⟩, p1, p2, p3⟩
    exact ⟨⟨h1, h2, h3, h4, p1, p2, p3⟩, Ne.symm c1, Ne.symm c2, Ne.symm c3, Ne.symm c4⟩

/-! ### Pattern weights -/

/-- Weights of the three non-trivial height-four pattern classes, relative to `0101`:
`a` for `0102`/`0121`, `b` for `0120`, `c` for `0123`. -/
structure Wt where
  a : ℝ
  b : ℝ
  c : ℝ

/-- The pattern weight of a proper column. -/
noncomputable def gw (w : Wt) (t : T4) : ℝ :=
  if r1 t = r3 t ∧ r2 t = r4 t then 1
  else if r1 t = r3 t ∨ r2 t = r4 t then w.a
  else if r1 t = r4 t then w.b
  else w.c

/-- The pattern-weighted number of proper colourings. -/
noncomputable def G (w : Wt) (A B C D : Finset ℕ) : ℝ := ∑ t ∈ sts A B C D, gw w t

end GridGen.Four
