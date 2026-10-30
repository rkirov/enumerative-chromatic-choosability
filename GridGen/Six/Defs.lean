/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.Defs

/-!
# Height six: columns of six rows as tuples

The concrete model behind `GridGen/Six/`, `GridGen/Five/Defs.lean` with six rows. A column state
is a 6-tuple of colours (rows 1..6, a path), proper when consecutive rows differ, and two states
of adjacent columns are compatible when they differ in every row. A 6-tuple is a colour followed
by a 5-tuple (`T6 = ℕ × T5`), so the proper colourings from lists `A, …, F`, `sts A B C D E F`,
prepend a first row to the height-five colourings `Five.sts B C D E F`, and their number is
`|A| · |Five.sts B C D E F| − |Five.sts (A ∩ B) C D E F|` (`card_sts`).

**Patterns.** The equality pattern of a proper column is its colouring up to renaming the
colours. There are fifty-two, and reversing the rows pairs them into thirty-two orbits, numbered
as in `ai_research_notes/cx/h6k6/cone6.json` (Codex, OpenAI) (`orb`, a decision tree on the ten
non-consecutive equalities; patterns as restricted growth strings):

* `0`: 010101;
* `1`: 010102/012121;
* `2`: 010120/012020;
* `3`: 010121/010202;
* `4`: 010123/012323;
* `5`: 010201/012101;
* `6`: 010203/012131;
* `7`: 010210/012010;
* `8`: 010212;
* `9`: 010213/012313;
* `10`: 010230/012030;
* `11`: 010231/012303;
* `12`: 010232;
* `13`: 010234/012343;
* `14`: 012012;
* `15`: 012013/012312;
* `16`: 012021/012102;
* `17`: 012023/012132;
* `18`: 012031/012302;
* `19`: 012032;
* `20`: 012034/012342;
* `21`: 012103/012321;
* `22`: 012120;
* `23`: 012123;
* `24`: 012130/012320;
* `25`: 012134/012324;
* `26`: 012301;
* `27`: 012304/012341;
* `28`: 012310;
* `29`: 012314;
* `30`: 012340;
* `31`: 012345;

A pattern weight `w : Wt6` gives each orbit a real number; the alternating orbit `0` is the
reference. The weight of a proper column is that of its orbit (`gw`), and `G w A B C D E F` is
the pattern-weighted number of proper colourings.

**The canonical realisation** `canon s` of the pattern of `s` records, for each row, the first
row with the same colour (the *first-occurrence string*), reading only the non-consecutive
equalities; on proper columns it has the pattern of `s` (`GridGen/Six/Relabel.lean`). The
uniform successors `GU k w s` of `s` are computed on it.
-/

namespace GridGen.Six

open Finset

/-- A column of six rows: a first colour followed by a column of five rows. -/
abbrev T6 := ℕ × Five.T5

/-- Rows of a column. -/
@[reducible] def r1 (t : T6) : ℕ := t.1
@[reducible] def r2 (t : T6) : ℕ := t.2.1
@[reducible] def r3 (t : T6) : ℕ := t.2.2.1
@[reducible] def r4 (t : T6) : ℕ := t.2.2.2.1
@[reducible] def r5 (t : T6) : ℕ := t.2.2.2.2.1
@[reducible] def r6 (t : T6) : ℕ := t.2.2.2.2.2

/-! ### Proper colourings of a path of six rows -/

/-- Proper colourings of a path of six rows: a first row in front of a proper column of five. -/
def sts (A B C D E F : Finset ℕ) : Finset T6 :=
  (A ×ˢ Five.sts B C D E F).filter (fun p => p.1 ≠ p.2.1)

theorem mem_sts {A B C D E F : Finset ℕ} {t : T6} :
    t ∈ sts A B C D E F ↔ r1 t ∈ A ∧ r2 t ∈ B ∧ r3 t ∈ C ∧ r4 t ∈ D ∧ r5 t ∈ E ∧ r6 t ∈ F ∧
      r1 t ≠ r2 t ∧ r2 t ≠ r3 t ∧ r3 t ≠ r4 t ∧ r4 t ≠ r5 t ∧ r5 t ≠ r6 t := by
  simp only [sts, Finset.mem_filter, Finset.mem_product, Five.mem_sts]
  simp only [Five.r1, Five.r2, Five.r3, Five.r4, Five.r5, r1, r2, r3, r4, r5, r6]
  tauto

/-- **The count of a six-row column**, by prepending the first row to the last five. -/
theorem card_sts (A B C D E F : Finset ℕ) :
    ((sts A B C D E F).card : ℤ) =
      A.card * (Five.sts B C D E F).card - (Five.sts (A ∩ B) C D E F).card := by
  rw [sts, Lookback.card_prepend A (Five.sts B C D E F) Five.r1]
  have h : (Five.sts B C D E F).filter (fun r => Five.r1 r ∈ A) = Five.sts (A ∩ B) C D E F := by
    ext p; simp only [Finset.mem_filter, Five.mem_sts, Finset.mem_inter]; tauto
  rw [h]

/-! ### Compatibility and the successors of a state -/

/-- Rowwise distinct: compatibility of adjacent columns. -/
def compat (s t : T6) : Prop :=
  r1 s ≠ r1 t ∧ r2 s ≠ r2 t ∧ r3 s ≠ r3 t ∧ r4 s ≠ r4 t ∧ r5 s ≠ r5 t ∧ r6 s ≠ r6 t

instance (s t : T6) : Decidable (compat s t) := by unfold compat; infer_instance

/-- The successors of `s` in a column with lists `A, …, F` are the proper colourings from the
punctured lists. -/
theorem filter_compat_sts (s : T6) (A B C D E F : Finset ℕ) :
    (sts A B C D E F).filter (compat s) =
      sts (A.erase (r1 s)) (B.erase (r2 s)) (C.erase (r3 s)) (D.erase (r4 s))
        (E.erase (r5 s)) (F.erase (r6 s)) := by
  ext t
  simp only [Finset.mem_filter, mem_sts, compat, Finset.mem_erase]
  constructor
  · rintro ⟨⟨h1, h2, h3, h4, h5, h6, p1, p2, p3, p4, p5⟩, c1, c2, c3, c4, c5, c6⟩
    exact ⟨⟨Ne.symm c1, h1⟩, ⟨Ne.symm c2, h2⟩, ⟨Ne.symm c3, h3⟩, ⟨Ne.symm c4, h4⟩,
      ⟨Ne.symm c5, h5⟩, ⟨Ne.symm c6, h6⟩, p1, p2, p3, p4, p5⟩
  · rintro ⟨⟨c1, h1⟩, ⟨c2, h2⟩, ⟨c3, h3⟩, ⟨c4, h4⟩, ⟨c5, h5⟩, ⟨c6, h6⟩, p1, p2, p3, p4, p5⟩
    exact ⟨⟨h1, h2, h3, h4, h5, h6, p1, p2, p3, p4, p5⟩, Ne.symm c1, Ne.symm c2, Ne.symm c3,
      Ne.symm c4, Ne.symm c5, Ne.symm c6⟩

/-! ### Pattern orbits and weights -/

/-- The reflection orbit of the equality pattern of a proper column, read off the ten
non-consecutive equalities (numbering in the module docstring). -/
def orb (t : T6) : Fin 32 :=
  if r1 t = r3 t then
    if r2 t = r4 t then
      if r3 t = r5 t then
        if r4 t = r6 t then
          0
        else
          1
      else
        if r4 t = r6 t then
          3
        else
          if r3 t = r6 t then
            2
          else
            4
    else
      if r3 t = r5 t then
        if r4 t = r6 t then
          3
        else
          if r2 t = r6 t then
            5
          else
            6
      else
        if r4 t = r6 t then
          if r2 t = r5 t then
            8
          else
            12
        else
          if r2 t = r5 t then
            if r3 t = r6 t then
              7
            else
              9
          else
            if r3 t = r6 t then
              10
            else
              if r2 t = r6 t then
                11
              else
                13
  else
    if r2 t = r4 t then
      if r3 t = r5 t then
        if r4 t = r6 t then
          1
        else
          if r1 t = r6 t then
            22
          else
            23
      else
        if r4 t = r6 t then
          if r1 t = r5 t then
            5
          else
            6
        else
          if r3 t = r6 t then
            if r1 t = r5 t then
              16
            else
              17
          else
            if r1 t = r5 t then
              21
            else
              if r1 t = r6 t then
                24
              else
                25
    else
      if r3 t = r5 t then
        if r4 t = r6 t then
          if r1 t = r4 t then
            2
          else
            4
        else
          if r1 t = r4 t then
            if r2 t = r6 t then
              16
            else
              17
          else
            if r2 t = r6 t then
              21
            else
              if r1 t = r6 t then
                24
              else
                25
      else
        if r4 t = r6 t then
          if r1 t = r4 t then
            if r2 t = r5 t then
              7
            else
              10
          else
            if r2 t = r5 t then
              9
            else
              if r1 t = r5 t then
                11
              else
                13
        else
          if r1 t = r4 t then
            if r2 t = r5 t then
              if r3 t = r6 t then
                14
              else
                15
            else
              if r3 t = r6 t then
                19
              else
                if r2 t = r6 t then
                  18
                else
                  20
          else
            if r2 t = r5 t then
              if r3 t = r6 t then
                15
              else
                if r1 t = r6 t then
                  28
                else
                  29
            else
              if r3 t = r6 t then
                if r1 t = r5 t then
                  18
                else
                  20
              else
                if r1 t = r5 t then
                  if r2 t = r6 t then
                    26
                  else
                    27
                else
                  if r2 t = r6 t then
                    27
                  else
                    if r1 t = r6 t then
                      30
                    else
                      31

/-- Pattern weights: one real number per reflection orbit. -/
abbrev Wt6 := Fin 32 → ℝ

/-- The pattern weight of a proper column. -/
def gw (w : Wt6) (t : T6) : ℝ := w (orb t)

/-- The pattern-weighted number of proper colourings. -/
noncomputable def G (w : Wt6) (A B C D E F : Finset ℕ) : ℝ := ∑ t ∈ sts A B C D E F, gw w t

/-! ### The canonical realisation and the uniform successors -/

/-- The canonical realisation of the equality pattern of a column: each row is replaced by the
first row (numbered from `0`) of the same colour, reading only non-consecutive equalities. -/
def canon (s : T6) : T6 :=
  (0, 1, if r3 s = r1 s then 0 else 2,
    if r4 s = r1 s then 0 else if r4 s = r2 s then 1 else 3,
    if r5 s = r1 s then 0 else if r5 s = r2 s then 1 else if r5 s = r3 s then 2 else 4,
    if r6 s = r1 s then 0 else if r6 s = r2 s then 1 else if r6 s = r3 s then 2
    else if r6 s = r4 s then 3 else 5)

/-- The pattern-weighted number of uniform successors of `s`. -/
noncomputable def GU (k : ℕ) (w : Wt6) (s : T6) : ℝ :=
  G w ((range k).erase (r1 (canon s))) ((range k).erase (r2 (canon s)))
    ((range k).erase (r3 (canon s))) ((range k).erase (r4 (canon s)))
    ((range k).erase (r5 (canon s))) ((range k).erase (r6 (canon s)))

/-- The pattern-weighted number of successors of `s` in a column with lists `B₁, …, B₆`. -/
noncomputable def GB (w : Wt6) (B₁ B₂ B₃ B₄ B₅ B₆ : Finset ℕ) (s : T6) : ℝ :=
  G w (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s)) (B₄.erase (r4 s)) (B₅.erase (r5 s))
    (B₆.erase (r6 s))

end GridGen.Six
