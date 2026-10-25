/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Seven.Chordless

/-!
# Short chordless crossing paths are vertical

A crossing path of two cells, and a chordless one of three cells, runs straight down the first
future column: any step into the next column must come back to the first column next to an
earlier cell, which is a chord (or a repeated cell).
-/

open Finset

set_option linter.unusedSectionVars false

namespace GridGen.Gauge

variable {c m : ℕ}

theorem adj_iff_coords {a b : Cell c m} : slabAdj a b ↔
    (a.1.val = b.1.val ∧ (a.2.val + 1 = b.2.val ∨ b.2.val + 1 = a.2.val)) ∨
      (a.2.val = b.2.val ∧ (a.1.val + 1 = b.1.val ∨ b.1.val + 1 = a.1.val)) := by
  unfold slabAdj
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨by rw [h1], h2⟩
    · exact Or.inr ⟨by rw [h1], h2⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨Fin.ext h1, h2⟩
    · exact Or.inr ⟨Fin.ext h1, h2⟩

theorem cell_ext' {a b : Cell c m} (h1 : a.1.val = b.1.val) (h2 : a.2.val = b.2.val) : a = b :=
  Prod.ext (Fin.ext h1) (Fin.ext h2)

theorem ne_coords {a b : Cell c m} (h : a ≠ b) : ¬ (a.1.val = b.1.val ∧ a.2.val = b.2.val) :=
  fun e => h (cell_ext' e.1 e.2)

/-- The vertical two-cell path from row `w + 1` down to row `w`. -/
def vert2 (hc : 1 ≤ c) (w : ℕ) (hw : w + 1 < m) : List (Cell c m) :=
  [(fut0 hc, ⟨w + 1, hw⟩), (fut0 hc, ⟨w, by omega⟩)]

/-- The vertical three-cell path from row `v + 2` down to row `v`. -/
def vert3 (hc : 1 ≤ c) (v : ℕ) (hv : v + 2 < m) : List (Cell c m) :=
  [(fut0 hc, ⟨v + 2, hv⟩), (fut0 hc, ⟨v + 1, by omega⟩), (fut0 hc, ⟨v, by omega⟩)]

/-- A crossing path has at least two cells. -/
theorem two_le_length {hc : 1 ≤ c} {w : ℕ} {l : List (Cell c m)} (hl : CrossPath hc w l) :
    2 ≤ l.length := by
  obtain ⟨-, -, -, ⟨v₁, hw₁, h1⟩, ⟨v₂, hw₂, h2⟩⟩ := hl
  match l, h1, h2 with
  | [a], h1, h2 =>
    simp only [List.head?_cons, Option.some.injEq, List.getLast?_singleton] at h1 h2
    rw [h1] at h2
    have := congrArg (fun z : Cell c m => z.2.val) h2
    simp at this; omega
  | _ :: _ :: _, _, _ => simp

/-- **Two cells: vertical**, across the cut. -/
theorem vert_two {hc : 1 ≤ c} {w : ℕ} {l : List (Cell c m)} (hl : CrossPath hc w l)
    (hL : l.length = 2) :
    ∃ hw : w + 1 < m, l = vert2 hc w hw := by
  obtain ⟨-, hchain, -, ⟨v₁, hw₁, h1⟩, ⟨v₂, hw₂, h2⟩⟩ := hl
  obtain ⟨a, d, rfl⟩ : ∃ a d, l = [a, d] := by
    match l, hL with
    | [a, d], _ => exact ⟨a, d, rfl⟩
  simp only [List.head?_cons, Option.some.injEq] at h1
  simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at h2
  subst h1 h2
  rw [List.isChain_cons_cons] at hchain
  have hab := adj_iff_coords.mp hchain.1
  simp only [fut0] at hab
  have hv : v₁.val = w + 1 ∧ v₂.val = w := by omega
  refine ⟨by omega, ?_⟩
  simp only [vert2, vert3, List.cons.injEq, and_true]
  exact ⟨cell_ext' rfl (by simp [hv.1]), cell_ext' rfl (by simp [hv.2])⟩

/-- **Three cells: vertical.** -/
theorem vert_three {hc : 1 ≤ c} {w : ℕ} {l : List (Cell c m)} (hl : CrossPath hc w l)
    (hch : Chordless l) (hL : l.length = 3) :
    ∃ (v : ℕ) (hv : v + 2 < m), l = vert3 hc v hv := by
  obtain ⟨hnd, hchain, hfut, ⟨v₁, hw₁, h1⟩, ⟨v₂, hw₂, h2⟩⟩ := hl
  obtain ⟨a, b, d, rfl⟩ : ∃ a b d, l = [a, b, d] := by
    match l, hL with
    | [a, b, d], _ => exact ⟨a, b, d, rfl⟩
  simp only [List.head?_cons, Option.some.injEq] at h1
  simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at h2
  have ha1 : a.1.val = 2 := by rw [h1]; rfl
  have ha2 : a.2.val = v₁.val := by rw [h1]
  have hd1 : d.1.val = 2 := by rw [h2]; rfl
  have hd2 : d.2.val = v₂.val := by rw [h2]
  rw [List.isChain_cons_cons, List.isChain_cons_cons] at hchain
  have hab := adj_iff_coords.mp hchain.1
  have hbd := adj_iff_coords.mp hchain.2.1
  have hnad := hch 0 2 (by simp) (by simp) (by omega)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hnad
  rw [adj_iff_coords] at hnad
  have hb2 := hfut b (by simp)
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_true] at hnd
  have nad := ne_coords hnd.1.2
  have hrow : b.1.val = 2 ∧ b.2.val = v₂.val + 1 ∧ v₁.val = v₂.val + 2 := by omega
  refine ⟨v₂.val, by omega, ?_⟩
  simp only [vert2, vert3, List.cons.injEq, and_true]
  exact ⟨cell_ext' ha1 (by simp; omega), cell_ext' (by simp [hrow.1]; rfl) (by simp; omega),
    cell_ext' hd1 (by simp; omega)⟩

end GridGen.Gauge
