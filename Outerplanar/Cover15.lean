/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.Close15

/-!
# Every square term of the fifteen-face centroid closes

**`cover15`** (`decide +kernel`, ten theorems, one per code of the first side): for every
assignment of the ten codes of `Outerplanar/Code15.lean` to the four sides of a square with at
most fourteen marks in all, some root `r` and one of the laws of `Outerplanar/Close15.lean` have
their conditions satisfied (3426 assignments; the Python model
`ai_research_notes/outerplanar/t4b_m5/cover.py` reproduces the count with 0 unsettled).
**`term_close_sq15`**: so every term of a square centroid with at most fourteen active marks has
the ordinary count.

This replaces the enumeration `fm_centroid_full.py` of the fifteen-face note (48,272 terms over
branch multisets): in the formal proof every side of the centroid is one class (branches at a
vertex are merged by the vertex rule), so a term is four codes; the rules are the same
(matching, `[B, M, M]`, `[H, M, M]` at `K = 59/56` in place of `K_sq`, `[B, B, B]`, `[B, 1, B]`,
`three_heavy`, and the closings U1a, U1b, U2, U3).

Formalized by Claude (milestone M5 of `ai_research_notes/OUTERPLANAR_13_15_LEAN_PLAN.md`).
-/

namespace Outerplanar.F15

open Finset Outerplanar C15

/-- All codes. -/
def allC15 : List C15 := [I, L1, L2, T3, T4, B5, B6, H6, B7, H7]

theorem mem_allC15 (c : C15) : c ∈ allC15 := by cases c <;> decide

/-- The three path positions. -/
def l3 : List (Fin (2 + 1)) := [0, 1, 2]

/-- The four roots. -/
def l4 : List (Fin (2 + 2)) := [0, 1, 2, 3]

theorem mem_l3 (j : Fin (2 + 1)) : j ∈ l3 := by fin_cases j <;> decide

section Plan

variable (cd : Fin (2 + 2) → C15) (r : Fin (2 + 2))

/-- `[M, M, M]` at `r`. -/
def mmmB15 : Bool := l3.all fun j => (cd (pos r j)).isM

/-- `[B, M, M]` at `r`, the ball side at `q`. -/
def bmmB15 (q : Fin (2 + 1)) : Bool :=
  (cd (pos r q)).hasB && l3.all fun j => decide (j = q) || (cd (pos r j)).isM

/-- `[H, M, M]` at `r`, the hexagon side at `q`. -/
def hmmB15 (q : Fin (2 + 1)) : Bool :=
  (l3.all fun j => decide (j = q) || (cd (pos r j)).isM) &&
    ((cd r).hV.add ((hmS cd r q 0).add ((hmS cd r q 1).add ((hmS cd r q 2).add Sc.kInv)))).ge1

/-- `[B, B, B]` at `r`. -/
def bbbB15 : Bool :=
  (l3.all fun j => (cd (pos r j)).hasB) &&
    ((cd r).hV.add ((cd (pos r 0)).bV.add ((cd (pos r 1)).bV.add
      ((cd (pos r 2)).bV.add (Sc.aInv.add Sc.aInv))))).ge1

/-- `[B, 1, B]` at `r`. -/
def b1bB15 : Bool :=
  decide (cd (pos r 1) = I) && (cd (pos r 0)).hasB && (cd (pos r 2)).hasB &&
    ((cd r).hV.add ((cd (pos r 0)).bV.add ((cd (pos r 2)).bV.add Sc.aInv))).ge1

/-- `three_heavy` at `r`. -/
def hhhcB15 : Bool :=
  decide (cd r = I) &&
    ((cd (pos r 0)).hV.add ((cd (pos r 1)).hV.add ((cd (pos r 2)).hV.add
      (Sc.aInv.add (Sc.aInv.add Sc.aInv))))).ge1

/-- The closings at `r`. -/
def uuB15 : Bool := decide (cd r = I) && uB cd r

/-- Some law closes at `r`. -/
def planB15 : Bool :=
  mmmB15 cd r || (l3.any fun q => bmmB15 cd r q || hmmB15 cd r q) || bbbB15 cd r || b1bB15 cd r ||
    hhhcB15 cd r || uuB15 cd r

end Plan

/-- Some root and law close the square. -/
def sqOK15 (cd : Fin (2 + 2) → C15) : Bool := l4.any (planB15 cd)

/-- The check over all codes, with the first side fixed. -/
def coverB15 (a : C15) : Bool :=
  allC15.all fun b => allC15.all fun c => allC15.all fun d =>
    decide (14 < a.marks + b.marks + c.marks + d.marks) || sqOK15 ![a, b, c, d]

theorem cover15_I : coverB15 I = true := by decide +kernel

theorem cover15_L1 : coverB15 L1 = true := by decide +kernel

theorem cover15_L2 : coverB15 L2 = true := by decide +kernel

theorem cover15_T3 : coverB15 T3 = true := by decide +kernel

theorem cover15_T4 : coverB15 T4 = true := by decide +kernel

theorem cover15_B5 : coverB15 B5 = true := by decide +kernel

theorem cover15_B6 : coverB15 B6 = true := by decide +kernel

theorem cover15_H6 : coverB15 H6 = true := by decide +kernel

theorem cover15_B7 : coverB15 B7 = true := by decide +kernel

theorem cover15_H7 : coverB15 H7 = true := by decide +kernel

/-- **Every square with at most fourteen marks closes** (ten kernel checks). -/
theorem cover15 (a : C15) : coverB15 a = true := by
  cases a
  · exact cover15_I
  · exact cover15_L1
  · exact cover15_L2
  · exact cover15_T3
  · exact cover15_T4
  · exact cover15_B5
  · exact cover15_B6
  · exact cover15_H6
  · exact cover15_B7
  · exact cover15_H7

theorem sqOK15_of_marks (cd : Fin (2 + 2) → C15)
    (h : (cd 0).marks + (cd 1).marks + (cd 2).marks + (cd 3).marks ≤ 14) : sqOK15 cd = true := by
  have key : coverB15 (cd 0) = true := cover15 (cd 0)
  simp only [coverB15, List.all_eq_true] at key
  have k := key _ (mem_allC15 (cd 1)) _ (mem_allC15 (cd 2)) _ (mem_allC15 (cd 3))
  have e : (![cd 0, cd 1, cd 2, cd 3] : Fin (2 + 2) → C15) = cd := by
    funext i; fin_cases i <;> rfl
  rw [e] at k
  simpa [show ¬ (14 < (cd 0).marks + (cd 1).marks + (cd 2).marks + (cd 3).marks) by omega]
    using k

/-- **A term of a square centroid closes**: at most fourteen active marks. -/
theorem term_close_sq15 (C : Fin (2 + 2) → Finset ℕ) (hC : ∀ i, (C i).card = 3)
    (G : Fin (2 + 2) → ℕ → ℕ → ℝ) (hG0 : ∀ i c d, 0 ≤ G i c d) (w : Fin (2 + 2) → ℝ)
    (hw : ∀ i, 0 < w i) (τ : Fin (2 + 2) → ℕ) (ρ : Fin (2 + 2) → Fin 3)
    (hpt : ∀ i, PT (τ i) (ρ i) (C i) (C (i + 1)) (G i) (w i)) (hτ7 : ∀ i, τ i ≤ 7)
    (hm : (code15 (τ 0) (ρ 0)).marks + (code15 (τ 1) (ρ 1)).marks + (code15 (τ 2) (ρ 2)).marks
      + (code15 (τ 3) (ρ 3)).marks ≤ 14) :
    6 * (faceConst3 2 * ∏ i, w i) ≤ cycSum C G := by
  have hok := sqOK15_of_marks (cdOf τ ρ) hm
  unfold sqOK15 at hok
  obtain ⟨r, -, hr⟩ := List.any_eq_true.mp hok
  unfold planB15 at hr
  simp only [Bool.or_eq_true] at hr
  rcases hr with ((((hr | hr) | hr) | hr) | hr) | hr
  · exact sq_MMM15 C hC G hG0 w hw τ ρ hpt r fun j => List.all_eq_true.mp hr j (mem_l3 j)
  · obtain ⟨q, -, hq⟩ := List.any_eq_true.mp hr
    rcases Bool.or_eq_true _ _ ▸ hq with hq | hq
    · unfold bmmB15 at hq
      simp only [Bool.and_eq_true] at hq
      refine sq_BMM15 C hC G hG0 w hw τ ρ hpt r q hq.1 fun j hj => ?_
      have := List.all_eq_true.mp hq.2 j (mem_l3 j)
      simpa [hj] using this
    · unfold hmmB15 at hq
      simp only [Bool.and_eq_true] at hq
      refine sq_HMM15 C hC G hG0 w hw τ ρ hpt r q (fun j hj => ?_) hq.2
      have := List.all_eq_true.mp hq.1 j (mem_l3 j)
      simpa [hj] using this
  · unfold bbbB15 at hr
    simp only [Bool.and_eq_true] at hr
    exact sq_BBB15 C hC G hG0 w hw τ ρ hpt r (fun j => List.all_eq_true.mp hr.1 j (mem_l3 j)) hr.2
  · unfold b1bB15 at hr
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
    exact sq_B1B15 C hC G hG0 w hw τ ρ hpt r hr.1.1.1 hr.1.1.2 hr.1.2 hr.2
  · unfold hhhcB15 at hr
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
    exact sq_HHHc15 C hC G hG0 w hw τ ρ hpt r hr.1 hr.2
  · unfold uuB15 at hr
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
    exact sq_U15 C hC G hG0 w hw τ ρ hpt hτ7 r hr.1 hr.2

end Outerplanar.F15
