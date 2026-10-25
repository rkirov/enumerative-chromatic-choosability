/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.Defs

/-!
# Height five: columns of five rows as tuples

The concrete model behind `GridGen/Five/`, `GridGen/Four/Defs.lean` with five rows. A column
state is a 5-tuple of colours (rows 1..5, a path), proper when consecutive rows differ, and two
states of adjacent columns are compatible when they differ in every row. A 5-tuple is a colour
followed by a 4-tuple (`T5 = ℕ × T4`), so the proper colourings from lists `A, B, C, D, E`,
`sts A B C D E`, prepend a first row to the height-four colourings `Four.sts B C D E`, and their
number is `|A| · |Four.sts B C D E| − |Four.sts (A ∩ B) C D E|` (`card_sts`).

**Patterns.** The equality pattern of a proper column is its colouring up to renaming the
colours: a restricted growth string of length five with distinct consecutive entries. There are
fifteen,

`01010, 01012, 01020, 01021, 01023, 01201, 01202, 01203, 01210, 01212, 01213, 01230, 01231,
01232, 01234`,

and reversing the rows pairs them into eleven orbits, numbered as in
`ai_research_notes/h5k6/boxes_k6.json` (`orb`):

* `0`: `01010`;
* `1`: `01012/01212`;
* `2`: `01020`;
* `3`: `01021/01202`;
* `4`: `01023/01232`;
* `5`: `01201`;
* `6`: `01203/01231`;
* `7`: `01210`;
* `8`: `01213`;
* `9`: `01230`;
* `10`: `01234`.

A pattern weight `w : Wt5` gives each orbit a real number; the alternating orbit `0` is the
reference and the box of `GridGen/Five/Statement.lean` pins it to `1`. The weight of a proper
column is that of its orbit (`gw`), and `G w A B C D E` is the pattern-weighted number of proper
colourings.
-/

namespace GridGen.Five

open Finset

/-- A column of five rows: a first colour followed by a column of four rows. -/
abbrev T5 := ℕ × ℕ × ℕ × ℕ × ℕ

/-- Rows of a column. -/
@[reducible] def r1 (t : T5) : ℕ := t.1
@[reducible] def r2 (t : T5) : ℕ := t.2.1
@[reducible] def r3 (t : T5) : ℕ := t.2.2.1
@[reducible] def r4 (t : T5) : ℕ := t.2.2.2.1
@[reducible] def r5 (t : T5) : ℕ := t.2.2.2.2

/-! ### Proper colourings of a path of five rows -/

/-- Proper colourings of a path of five rows: a first row in front of a proper column of four. -/
def sts (A B C D E : Finset ℕ) : Finset T5 :=
  (A ×ˢ Four.sts B C D E).filter (fun p => p.1 ≠ p.2.1)

theorem mem_sts {A B C D E : Finset ℕ} {t : T5} :
    t ∈ sts A B C D E ↔ r1 t ∈ A ∧ r2 t ∈ B ∧ r3 t ∈ C ∧ r4 t ∈ D ∧ r5 t ∈ E ∧
      r1 t ≠ r2 t ∧ r2 t ≠ r3 t ∧ r3 t ≠ r4 t ∧ r4 t ≠ r5 t := by
  simp only [sts, Finset.mem_filter, Finset.mem_product, Four.mem_sts]
  simp only [Four.r1, Four.r2, Four.r3, Four.r4, r1, r2, r3, r4, r5]
  tauto

/-- **The count of a five-row column**, by prepending the first row to the last four. -/
theorem card_sts (A B C D E : Finset ℕ) :
    ((sts A B C D E).card : ℤ) =
      A.card * (Four.sts B C D E).card - (Four.sts (A ∩ B) C D E).card := by
  rw [sts, Lookback.card_prepend A (Four.sts B C D E) Four.r1]
  have h : (Four.sts B C D E).filter (fun r => Four.r1 r ∈ A) = Four.sts (A ∩ B) C D E := by
    ext p; simp only [Finset.mem_filter, Four.mem_sts, Finset.mem_inter]; tauto
  rw [h]

/-! ### Compatibility and the successors of a state -/

/-- Rowwise distinct: compatibility of adjacent columns. -/
def compat (s t : T5) : Prop :=
  r1 s ≠ r1 t ∧ r2 s ≠ r2 t ∧ r3 s ≠ r3 t ∧ r4 s ≠ r4 t ∧ r5 s ≠ r5 t

instance (s t : T5) : Decidable (compat s t) := by unfold compat; infer_instance

/-- The successors of `s` in a column with lists `A, …, E` are the proper colourings from the
punctured lists. -/
theorem filter_compat_sts (s : T5) (A B C D E : Finset ℕ) :
    (sts A B C D E).filter (compat s) =
      sts (A.erase (r1 s)) (B.erase (r2 s)) (C.erase (r3 s)) (D.erase (r4 s))
        (E.erase (r5 s)) := by
  ext t
  simp only [Finset.mem_filter, mem_sts, compat, Finset.mem_erase]
  constructor
  · rintro ⟨⟨h1, h2, h3, h4, h5, p1, p2, p3, p4⟩, c1, c2, c3, c4, c5⟩
    exact ⟨⟨Ne.symm c1, h1⟩, ⟨Ne.symm c2, h2⟩, ⟨Ne.symm c3, h3⟩, ⟨Ne.symm c4, h4⟩,
      ⟨Ne.symm c5, h5⟩, p1, p2, p3, p4⟩
  · rintro ⟨⟨c1, h1⟩, ⟨c2, h2⟩, ⟨c3, h3⟩, ⟨c4, h4⟩, ⟨c5, h5⟩, p1, p2, p3, p4⟩
    exact ⟨⟨h1, h2, h3, h4, h5, p1, p2, p3, p4⟩, Ne.symm c1, Ne.symm c2, Ne.symm c3,
      Ne.symm c4, Ne.symm c5⟩

/-! ### Pattern orbits and weights -/

/-- The reflection orbit of the equality pattern of a proper column, read off the six
non-consecutive equalities (numbering in the module docstring). -/
def orb (t : T5) : Fin 11 :=
  if r1 t = r3 t then
    if r2 t = r4 t then (if r3 t = r5 t then 0 else 1)
    else if r3 t = r5 t then 2
    else if r2 t = r5 t then 3
    else 4
  else if r1 t = r4 t then
    if r2 t = r5 t then 5
    else if r3 t = r5 t then 3
    else 6
  else if r2 t = r4 t then
    if r3 t = r5 t then 1
    else if r1 t = r5 t then 7
    else 8
  else if r1 t = r5 t then 9
  else if r2 t = r5 t then 6
  else if r3 t = r5 t then 4
  else 10

/-- Pattern weights: one real number per reflection orbit. The box of
`GridGen/Five/Statement.lean` fixes the alternating orbit `0` at `1`. -/
abbrev Wt5 := Fin 11 → ℝ

/-- The pattern weight of a proper column. -/
def gw (w : Wt5) (t : T5) : ℝ := w (orb t)

/-- The pattern-weighted number of proper colourings. -/
noncomputable def G (w : Wt5) (A B C D E : Finset ℕ) : ℝ := ∑ t ∈ sts A B C D E, gw w t

end GridGen.Five
