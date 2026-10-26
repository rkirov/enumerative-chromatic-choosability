/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.Bridge

/-!
# Height four at `k = 4`: class vectors and the one-column seam vector

The argument of `GridGen/Four/K4/` is Codex's (OpenAI), `ai_research_notes/cx/h4k4/NOTE.md` and
`ai_research_notes/cx/h4k4b/NOTE.md` (2026-10-25), reviewed in
`ai_research_notes/H4_K4_REVIEW_2026-10-26.md`. This file sets up its integer data.

A proper four-row column has one of four classes: `A = 0101`, `B = 0102/0121`, `C = 0120`,
`D = 0123`. A *class vector* `Q = ℤ⁴` is indexed by them, `ce t` is the unit vector of the class of
`t`, and a weight `w : Q` weighs a column by `cw w t = ⟪ce t, w⟫`. The uniform transfer at `k = 4`
is the matrix `H` (rows `hrow`), and `Hm w = H w`.

For lists `Y` of a column and `B` of the next one, the **seam vector**

  `dvec Y B = ∑_{s ∈ sts Y} (cnt (B ∖ s) - H_{class s})`

collects, over the proper states `s` of `Y`, the class counts of the actual successors minus the
uniform ones. Its value at a weight is `Sw w Y B = ⟪dvec Y B, w⟫` (`Sw_eq`).
-/

namespace GridGen.Four.K4

open Finset

/-- A vector indexed by the four classes `A, B, C, D`. -/
abbrev Q := ℤ × ℤ × ℤ × ℤ

/-- The dot product. -/
def dot (d w : Q) : ℤ := d.1 * w.1 + d.2.1 * w.2.1 + d.2.2.1 * w.2.2.1 + d.2.2.2 * w.2.2.2

theorem dot_add (d e w : Q) : dot (d + e) w = dot d w + dot e w := by
  obtain ⟨d1, d2, d3, d4⟩ := d; obtain ⟨e1, e2, e3, e4⟩ := e
  simp only [dot, Prod.mk_add_mk]; ring

theorem dot_sub (d e w : Q) : dot (d - e) w = dot d w - dot e w := by
  obtain ⟨d1, d2, d3, d4⟩ := d; obtain ⟨e1, e2, e3, e4⟩ := e
  simp only [dot, Prod.mk_sub_mk]; ring

theorem dot_zero (w : Q) : dot 0 w = 0 := by
  simp [dot]

/-- The dot product against `w`, as an additive map. -/
def dotHom (w : Q) : Q →+ ℤ where
  toFun d := dot d w
  map_zero' := dot_zero w
  map_add' d e := dot_add d e w

theorem dot_sum {ι : Type*} (I : Finset ι) (f : ι → Q) (w : Q) :
    dot (∑ i ∈ I, f i) w = ∑ i ∈ I, dot (f i) w :=
  map_sum (dotHom w) f I

/-- The class of a column, as a unit vector. -/
def ce (t : T4) : Q :=
  if r1 t = r3 t ∧ r2 t = r4 t then (1, 0, 0, 0)
  else if r1 t = r3 t ∨ r2 t = r4 t then (0, 1, 0, 0)
  else if r1 t = r4 t then (0, 0, 1, 0) else (0, 0, 0, 1)

/-- The weight of a column. -/
def cw (w : Q) (t : T4) : ℤ := dot (ce t) w

/-- The row of the uniform transfer `H` for the class of a column. -/
def hrow (s : T4) : Q :=
  if r1 s = r3 s ∧ r2 s = r4 s then (7, 20, 6, 8)
  else if r1 s = r3 s ∨ r2 s = r4 s then (5, 19, 7, 8)
  else if r1 s = r4 s then (3, 14, 11, 8) else (4, 16, 8, 9)

/-- The uniform transfer at `k = 4`. -/
def Hm (w : Q) : Q := (dot (7, 20, 6, 8) w, dot (5, 19, 7, 8) w, dot (3, 14, 11, 8) w,
  dot (4, 16, 8, 9) w)

theorem cw_Hm (w : Q) (s : T4) : cw (Hm w) s = dot (hrow s) w := by
  unfold cw ce hrow Hm
  split_ifs <;> simp [dot]

/-! ### Lists of a column -/

/-- The four lists of a column. -/
abbrev Col := Finset ℕ × Finset ℕ × Finset ℕ × Finset ℕ

/-- The proper states of a column. -/
def stsC (Y : Col) : Finset T4 := sts Y.1 Y.2.1 Y.2.2.1 Y.2.2.2

/-- The lists punctured by a state of the previous (or next) column. -/
def ers (A : Col) (u : T4) : Col :=
  (A.1.erase (r1 u), A.2.1.erase (r2 u), A.2.2.1.erase (r3 u), A.2.2.2.erase (r4 u))

/-- The class counts of a column. -/
def cnt (Y : Col) : Q := ∑ t ∈ stsC Y, ce t

/-- **The seam vector.** -/
def dvec (Y B : Col) : Q := ∑ s ∈ stsC Y, (cnt (ers B s) - hrow s)

/-- **The seam value** at a weight. -/
def Sw (w : Q) (Y B : Col) : ℤ := dot (dvec Y B) w

theorem dot_cnt (Y : Col) (w : Q) : dot (cnt Y) w = ∑ t ∈ stsC Y, cw w t := by
  unfold cnt cw; exact dot_sum _ _ _

/-- The seam value, unfolded: actual successors weighed by `w`, minus the uniform successors. -/
theorem Sw_eq (w : Q) (Y B : Col) :
    Sw w Y B = ∑ s ∈ stsC Y, (∑ t ∈ stsC (ers B s), cw w t - cw (Hm w) s) := by
  unfold Sw dvec
  rw [dot_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [dot_sub, dot_cnt, cw_Hm]

/-- The successors of `s` in a column with lists `B` are the proper states of `B ∖ s`. -/
theorem filter_compat_stsC (B : Col) (s : T4) :
    (stsC B).filter (compat s) = stsC (ers B s) :=
  filter_compat_sts s _ _ _ _

/-! ### The cone `K` -/

/-- The twelve rays of the cone `K`: the uniform futures `F₀, …, F₃` and the eight corners of the
tail box `T`. -/
def rays : List Q :=
  [(1, 1, 1, 1), (41, 39, 36, 37), (1579, 1494, 1361, 1409), (60371, 57080, 51896, 53789),
    (10000, 9453, 8592, 8907), (10000, 9453, 8592, 8909), (10000, 9453, 8594, 8907),
    (10000, 9453, 8594, 8909), (10000, 9454, 8592, 8907), (10000, 9454, 8592, 8909),
    (10000, 9454, 8594, 8907), (10000, 9454, 8594, 8909)]

/-- A class vector is nonnegative on the cone `K`: at its twelve rays. -/
def RaysOK (d : Q) : Prop := ∀ r ∈ rays, 0 ≤ dot d r

instance (d : Q) : Decidable (RaysOK d) := by unfold RaysOK; infer_instance

theorem RaysOK_add {d e : Q} (hd : RaysOK d) (he : RaysOK e) : RaysOK (d + e) :=
  fun r hr => by rw [dot_add]; exact add_nonneg (hd r hr) (he r hr)

end GridGen.Four.K4
