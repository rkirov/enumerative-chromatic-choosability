/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.K4.Relabel

/-!
# Height four at `k = 4`: the four bad patterns, and the classification as a statement

Codex's (OpenAI) classification (`ai_research_notes/cx/h4k4b/NOTE.md`, reviewed in
`ai_research_notes/H4_K4_REVIEW_2026-10-26.md` Part 1(c)): for lists `Y` of three or four colours
and next lists `B` of four colours, the seam vector `dvec Y B` is nonnegative on the cone `K`
unless `(Y, B)` is, up to renaming the colours and reversing the rows, one of four families. With
`C = {x, y, z}` and `a, b ∉ C` distinct, `C + a = C ∪ {a}`:

| family | `B` | `Y` |
|---|---|---|
| E1 | `(C+a, C+a, C+a, C+b)` | `(C−c+a, C, C−c+a, C−c+b)` |
| E2 | same | `(C−c+a, C, C−d+a, C−d+b)`, `c ≠ d` |
| E3 | same | `(C+a, C, C−d+a, C−d+b)` |
| M  | `(C+a, C+a, C+b, C+b)` | `(C, C−c+a, C−c+b, C)` |

Naming the colours so that `d = z` (and `c = z` in M), E1–E3 are `BadF` (the first list is
`C−z+a`, `C−x+a`, `C−y+a` or `C+a`), their reversals `BadR`, and M is `BadM` (closed under
reversal: it swaps `a` and `b`). The existential quantifiers over the colours are the renaming.

`Classify4` is the classification, stated at the twelve rays of `K` (a linear form is nonnegative
on `K` iff it is at its rays). It is **not proved here**: it is the hypothesis of
`GridGen/Four/K4/Main.lean`.

The structural facts used by the endpoint-fibre argument: the three kinds have incompatible next
columns (`badF_shape`, `badR_shape`, `badM_shape`); each has a three-list at its endpoint row,
determined by `B` and the neighbouring list (`badF_target`, `badR_target`, `badM_target`).
-/

namespace GridGen.Four.K4

open Finset

/-- Five distinct colours `x, y, z, a, b`. -/
def Dist5 (x y z a b : ℕ) : Prop :=
  x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ a ≠ x ∧ a ≠ y ∧ a ≠ z ∧ b ≠ x ∧ b ≠ y ∧ b ≠ z ∧ a ≠ b

/-- The edge next column `(C+a, C+a, C+a, C+b)`, `C = {x, y, z}`. -/
def edgeB (x y z a b : ℕ) : Col := ({x, y, z, a}, {x, y, z, a}, {x, y, z, a}, {x, y, z, b})

/-- The central next column `(C+a, C+a, C+b, C+b)`. -/
def centB (x y z a b : ℕ) : Col := ({x, y, z, a}, {x, y, z, a}, {x, y, z, b}, {x, y, z, b})

/-- **E1, E2, E3**, forward orientation, with `d = z`: `B` is the edge column, `Y₁ = C`,
`Y₂ = C−z+a`, `Y₃ = C−z+b`, and `Y₀` is `C−z+a` (E1), `C−x+a` or `C−y+a` (E2), or `C+a` (E3). -/
def BadF (Y B : Col) : Prop :=
  ∃ x y z a b : ℕ, Dist5 x y z a b ∧ B = edgeB x y z a b ∧ Y.2.1 = {x, y, z} ∧
    Y.2.2.1 = {x, y, a} ∧ Y.2.2.2 = {x, y, b} ∧
    (Y.1 = {x, y, a} ∨ Y.1 = {y, z, a} ∨ Y.1 = {x, z, a} ∨ Y.1 = {x, y, z, a})

/-- E1, E2, E3 reversed. -/
def BadR (Y B : Col) : Prop := BadF (revC Y) (revC B)

/-- **M**, with `c = z`: `B` is the central column and `Y = (C, C−z+a, C−z+b, C)`. -/
def BadM (Y B : Col) : Prop :=
  ∃ x y z a b : ℕ, Dist5 x y z a b ∧ B = centB x y z a b ∧
    Y = ({x, y, z}, {x, y, a}, {x, y, b}, {x, y, z})

/-- The four bad patterns, up to renaming and reversal. -/
def Bad (Y B : Col) : Prop := BadF Y B ∨ BadR Y B ∨ BadM Y B

/-- Every list has between `lo` and `hi` colours. -/
def CardsIn (lo hi : ℕ) (Y : Col) : Prop :=
  (lo ≤ Y.1.card ∧ Y.1.card ≤ hi) ∧ (lo ≤ Y.2.1.card ∧ Y.2.1.card ≤ hi) ∧
    (lo ≤ Y.2.2.1.card ∧ Y.2.2.1.card ≤ hi) ∧ (lo ≤ Y.2.2.2.card ∧ Y.2.2.2.card ≤ hi)

/-- **The four-bad-pattern classification** (Codex, `cx/h4k4b`). For lists `Y` of three or four
colours and next lists `B` of four colours, outside the four bad patterns the seam vector is
nonnegative at the twelve rays of `K`. -/
def Classify4 : Prop :=
  ∀ Y B : Col, CardsIn 3 4 Y → CardsIn 4 4 B → ¬ Bad Y B → RaysOK (dvec Y B)

/-! ### Small set facts -/

theorem card3 {x y z : ℕ} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ({x, y, z} : Finset ℕ).card = 3 := by
  rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]), Finset.card_pair hyz]

theorem ne4 {x y z a b : ℕ} (h : Dist5 x y z a b) :
    ({x, y, z, a} : Finset ℕ) ≠ {x, y, z, b} := by
  obtain ⟨-, -, -, -, -, -, h7, h8, h9, h10⟩ := h
  intro e
  have hb : b ∈ ({x, y, z, b} : Finset ℕ) := by simp
  rw [← e] at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  omega

/-! ### Shapes of the next column -/

theorem badF_shape {Y B : Col} (h : BadF Y B) : B.1 = B.2.1 ∧ B.2.1 = B.2.2.1 := by
  obtain ⟨x, y, z, a, b, -, rfl, -⟩ := h
  exact ⟨rfl, rfl⟩

theorem badR_shape {Y B : Col} (h : BadR Y B) : B.2.1 = B.2.2.1 ∧ B.1 ≠ B.2.1 := by
  obtain ⟨x, y, z, a, b, hd, hB, -⟩ := h
  obtain ⟨B1, B2, B3, B4⟩ := B
  simp only [revC, edgeB, Prod.mk.injEq] at hB
  obtain ⟨e4, e3, e2, e1⟩ := hB
  refine ⟨by rw [e3, e2], ?_⟩
  rw [e1, e2]
  exact (ne4 hd).symm

theorem badM_shape {Y B : Col} (h : BadM Y B) : B.2.1 ≠ B.2.2.1 := by
  obtain ⟨x, y, z, a, b, hd, rfl, -⟩ := h
  exact ne4 hd

/-- On an edge-shaped next column, a bad pattern is forward. -/
theorem bad_fwd {Y B : Col} (hB : B.1 = B.2.1 ∧ B.2.1 = B.2.2.1) (h : Bad Y B) : BadF Y B := by
  rcases h with h | h | h
  · exact h
  · exact absurd hB.1 (badR_shape h).2
  · exact absurd hB.2 (badM_shape h)

/-- Otherwise it is reversed or central. -/
theorem bad_nfwd {Y B : Col} (hB : ¬ (B.1 = B.2.1 ∧ B.2.1 = B.2.2.1)) (h : Bad Y B) :
    BadR Y B ∨ BadM Y B := by
  rcases h with h | h | h
  · exact absurd (badF_shape h) hB
  · exact Or.inl h
  · exact Or.inr h

theorem not_badR_badM {Y Y' B : Col} (h : BadR Y B) (h' : BadM Y' B) : False :=
  badM_shape h' (badR_shape h).1

/-! ### The endpoint list -/

/-- Forward: the last list is `(Y₂ ∩ B₃) ∪ (B₃ ∖ B₀)` and has three colours. -/
theorem badF_target {Y B : Col} (h : BadF Y B) :
    Y.2.2.2 = (Y.2.2.1 ∩ B.2.2.2) ∪ (B.2.2.2 \ B.1) ∧ Y.2.2.2.card = 3 := by
  obtain ⟨x, y, z, a, b, hd, rfl, -, h2, h3, -⟩ := h
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ := hd
  refine ⟨?_, by rw [h3]; exact card3 (by omega) (by omega) (by omega)⟩
  rw [h2, h3]
  ext c
  simp only [edgeB, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff, Finset.mem_insert,
    Finset.mem_singleton]
  constructor <;> intro hc <;> omega

/-- Reversed: the first list is `(Y₁ ∩ B₀) ∪ (B₀ ∖ B₃)` and has three colours. -/
theorem badR_target {Y B : Col} (h : BadR Y B) :
    Y.1 = (Y.2.1 ∩ B.1) ∪ (B.1 \ B.2.2.2) ∧ Y.1.card = 3 := by
  have := badF_target h
  simpa [revC] using this

/-- Central: the first list is `B₀ ∩ B₃` and has three colours. -/
theorem badM_target {Y B : Col} (h : BadM Y B) : Y.1 = B.1 ∩ B.2.2.2 ∧ Y.1.card = 3 := by
  obtain ⟨x, y, z, a, b, hd, rfl, rfl⟩ := h
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ := hd
  refine ⟨?_, card3 (by omega) (by omega) (by omega)⟩
  ext c
  simp only [centB, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
  constructor <;> intro hc <;> omega

/-- A bad pattern has a list of three colours, so a column of four-lists is never bad. -/
theorem not_bad_of_four {Y B : Col} (hY : CardsIn 4 4 Y) : ¬ Bad Y B := by
  obtain ⟨⟨h1, -⟩, -, -, ⟨h4, -⟩⟩ := hY
  rintro (h | h | h)
  · have := (badF_target h).2; omega
  · have := (badR_target h).2; omega
  · have := (badM_target h).2; omega

end GridGen.Four.K4
