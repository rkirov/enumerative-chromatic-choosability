/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Height four: columns of four rows as tuples

The concrete model behind `GridGen/Four/`: a column state is a 4-tuple of colours (rows 1..4,
a path), proper when consecutive rows differ, and two states of adjacent columns are compatible
when they differ in every row. The proper colourings of the path from lists `A, B, C, D` are
`sts A B C D`. Their number has an exact inclusion–exclusion form in the sizes of the lists and
of their consecutive intersections (`card_sts`), obtained by prepending one row at a time:
a new first row with list `A` multiplies the count by `|A|` and subtracts the colourings whose
old first row already lies in `A`.
-/

namespace GridGen.Four

open Finset

/-- A column of four rows. -/
abbrev T4 := ℕ × ℕ × ℕ × ℕ

/-- Rows of a column. -/
@[reducible] def r1 (t : T4) : ℕ := t.1
@[reducible] def r2 (t : T4) : ℕ := t.2.1
@[reducible] def r3 (t : T4) : ℕ := t.2.2.1
@[reducible] def r4 (t : T4) : ℕ := t.2.2.2

/-- The card of a filtered product, as a sum over the first factor. -/
theorem card_filter_prod {α β : Type*} [DecidableEq α] [DecidableEq β] (S : Finset α)
    (C : Finset β) (P : α → Prop) [DecidablePred P] (Q : α → β → Prop) [∀ a b, Decidable (Q a b)] :
    ((S ×ˢ C).filter (fun x => P x.1 ∧ Q x.1 x.2)).card =
      ∑ a ∈ S.filter P, (C.filter (Q a)).card := by
  rw [Finset.card_filter, Finset.sum_product, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.card_filter]
  by_cases hP : P a
  · simp only [hP, true_and, ite_true]
  · simp only [hP, false_and, ite_false, Finset.sum_const_zero]

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

/-- Prepending a row: `#{(x, rest) : x ∈ A, x ≠ first rest} = |A|·#rest − #{rest : first ∈ A}`. -/
theorem card_prepend {β : Type*} [DecidableEq β] (A : Finset ℕ) (R : Finset β) (f : β → ℕ) :
    (((A ×ˢ R).filter (fun p => p.1 ≠ f p.2)).card : ℤ) =
      A.card * R.card - (R.filter (fun r => f r ∈ A)).card := by
  have h := card_filter_prod A R (fun _ => True) (fun a r => a ≠ f r)
  simp only [true_and, Finset.filter_true] at h
  rw [h]
  have hswap : ∑ a ∈ A, (R.filter (fun r => a ≠ f r)).card =
      ∑ r ∈ R, (A.filter (fun a => a ≠ f r)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  rw [hswap]
  have hterm : ∀ r ∈ R, ((A.filter (fun a => a ≠ f r)).card : ℤ) = A.card - if f r ∈ A then 1 else 0 := by
    intro r _
    rw [Finset.filter_ne' A (f r)]
    split_ifs with h
    · rw [Finset.card_erase_of_mem h]; push_cast [Nat.cast_sub (Finset.card_pos.mpr ⟨_, h⟩)]; ring
    · rw [Finset.erase_eq_of_notMem h]; ring
  push_cast
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    Finset.card_filter]
  push_cast
  ring

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
