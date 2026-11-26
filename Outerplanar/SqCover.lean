/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.SqClose

/-!
# Every square term of the centroid closes

**`sqCloseCover`** (`decide`): for every assignment of the nine codes to the four sides of a square with
at most twelve marks in all, some root `r` and one of the six laws of `Outerplanar/SqClose.lean`
have their conditions satisfied. **`term_close_sq`**: so every term of a square centroid with at
most twelve active marks has the ordinary count.

Formalized by Claude (milestone M3 of `ai_research_notes/OUTERPLANAR_13_15_LEAN_PLAN.md`).
-/

namespace Outerplanar

open Finset Code

/-- All codes. -/
def allCodes : List Code := [I, L1, L2, T3, T4, B5, B6, H5, H6]

theorem mem_allCodes (c : Code) : c ∈ allCodes := by cases c <;> decide

/-- The three path positions. -/
def fin3 : List (Fin (2 + 1)) := [0, 1, 2]

/-- The four roots. -/
def fin4 : List (Fin (2 + 2)) := [0, 1, 2, 3]

theorem mem_fin3 (j : Fin (2 + 1)) : j ∈ fin3 := by fin_cases j <;> decide

theorem mem_fin4 (r : Fin (2 + 2)) : r ∈ fin4 := by fin_cases r <;> decide

/-- `[M, M, M]` at `r`. -/
def mmmB (cd : Fin (2 + 2) → Code) (r : Fin (2 + 2)) : Bool := fin3.all fun j => (cd (pos r j)).isM

/-- `[B, M, M]` at `r`, the ball side at `q`. -/
def bmmB (cd : Fin (2 + 2) → Code) (r : Fin (2 + 2)) (q : Fin (2 + 1)) : Bool :=
  (cd (pos r q)).hasB && fin3.all fun j => decide (j = q) || (cd (pos r j)).isM

/-- `[H, M, M]` at `r`, the hexagon side at `q`. -/
def hmmB (cd : Fin (2 + 2) → Code) (r : Fin (2 + 2)) (q : Fin (2 + 1)) : Bool :=
  (cd r).hbig && (cd (pos r q)).hbig && fin3.all fun j => decide (j = q) || (cd (pos r j)).isM

/-- The flag count of a code. -/
def flag (b : Bool) : ℕ := if b then 1 else 0

/-- `[B, B, B]` at `r`. -/
def bbbB (cd : Fin (2 + 2) → Code) (r : Fin (2 + 2)) : Bool :=
  (fin3.all fun j => (cd (pos r j)).hasB) &&
    decide (2 ≤ flag (cd r).hA + (flag (cd (pos r 0)).bA + flag (cd (pos r 1)).bA
      + flag (cd (pos r 2)).bA))

/-- `[H, H, H]` at `r`. -/
def hhhB (cd : Fin (2 + 2) → Code) (r : Fin (2 + 2)) : Bool :=
  (cd r).hA && fin3.all fun j => (cd (pos r j)).hA

/-- `three_heavy` at `r`. -/
def hhhcB (cd : Fin (2 + 2) → Code) (r : Fin (2 + 2)) : Bool :=
  decide (cd r = I) && fin3.all fun j => (cd (pos r j)).hA

/-- Some law closes at `r`. -/
def planB (cd : Fin (2 + 2) → Code) (r : Fin (2 + 2)) : Bool :=
  mmmB cd r || (fin3.any fun q => bmmB cd r q || hmmB cd r q) || bbbB cd r || hhhB cd r ||
    hhhcB cd r

/-- Some root and law close the square. -/
def sqOK (cd : Fin (2 + 2) → Code) : Bool := fin4.any (planB cd)

/-- The check over all codes, with the first side fixed. -/
def coverB (a : Code) : Bool :=
  allCodes.all fun b => allCodes.all fun c => allCodes.all fun d =>
    decide (12 < a.marks + b.marks + c.marks + d.marks) || sqOK ![a, b, c, d]

theorem sqCloseCover_I : coverB I = true := by decide

theorem sqCloseCover_L1 : coverB L1 = true := by decide

theorem sqCloseCover_L2 : coverB L2 = true := by decide

theorem sqCloseCover_T3 : coverB T3 = true := by decide

theorem sqCloseCover_T4 : coverB T4 = true := by decide

theorem sqCloseCover_B5 : coverB B5 = true := by decide

theorem sqCloseCover_B6 : coverB B6 = true := by decide

theorem sqCloseCover_H5 : coverB H5 = true := by decide

theorem sqCloseCover_H6 : coverB H6 = true := by decide

/-- **Every square with at most twelve marks closes** (2198 cases, nine kernel checks). -/
theorem sqCloseCover (a : Code) : coverB a = true := by
  cases a
  · exact sqCloseCover_I
  · exact sqCloseCover_L1
  · exact sqCloseCover_L2
  · exact sqCloseCover_T3
  · exact sqCloseCover_T4
  · exact sqCloseCover_B5
  · exact sqCloseCover_B6
  · exact sqCloseCover_H5
  · exact sqCloseCover_H6

theorem sqOK_of_marks (cd : Fin (2 + 2) → Code)
    (h : (cd 0).marks + (cd 1).marks + (cd 2).marks + (cd 3).marks ≤ 12) : sqOK cd = true := by
  have key : coverB (cd 0) = true := sqCloseCover (cd 0)
  simp only [coverB, List.all_eq_true] at key
  have k := key _ (mem_allCodes (cd 1)) _ (mem_allCodes (cd 2)) _ (mem_allCodes (cd 3))
  have e : (![cd 0, cd 1, cd 2, cd 3] : Fin (2 + 2) → Code) = cd := by
    funext i; fin_cases i <;> rfl
  rw [e] at k
  simpa [show ¬ (12 < (cd 0).marks + (cd 1).marks + (cd 2).marks + (cd 3).marks) by omega]
    using k

/-- **A term of a square centroid closes**: at most twelve active marks. -/
theorem term_close_sq (C : Fin (2 + 2) → Finset ℕ) (hC : ∀ i, (C i).card = 3)
    (G : Fin (2 + 2) → ℕ → ℕ → ℝ) (hG0 : ∀ i c d, 0 ≤ G i c d) (w : Fin (2 + 2) → ℝ)
    (hw : ∀ i, 0 < w i) (τ : Fin (2 + 2) → ℕ) (ρ : Fin (2 + 2) → Fin 3)
    (hpt : ∀ i, PT (τ i) (ρ i) (C i) (C (i + 1)) (G i) (w i))
    (hm : (code (τ 0) (ρ 0)).marks + (code (τ 1) (ρ 1)).marks + (code (τ 2) (ρ 2)).marks
      + (code (τ 3) (ρ 3)).marks ≤ 12) :
    6 * (faceConst3 2 * ∏ i, w i) ≤ cycSum C G := by
  set cd : Fin (2 + 2) → Code := fun i => code (τ i) (ρ i) with hcd
  have hok := sqOK_of_marks cd hm
  unfold sqOK at hok
  obtain ⟨r, -, hr⟩ := List.any_eq_true.mp hok
  unfold planB at hr
  simp only [Bool.or_eq_true] at hr
  rcases hr with (((hr | hr) | hr) | hr) | hr
  · refine sq_MMM C hC G hG0 w hw τ ρ hpt r fun j => ?_
    unfold mmmB at hr
    exact List.all_eq_true.mp hr j (mem_fin3 j)
  · obtain ⟨q, -, hq⟩ := List.any_eq_true.mp hr
    rcases Bool.or_eq_true _ _ ▸ hq with hq | hq
    · unfold bmmB at hq
      simp only [Bool.and_eq_true] at hq
      refine sq_BMM C hC G hG0 w hw τ ρ hpt r q hq.1 fun j hj => ?_
      have := List.all_eq_true.mp hq.2 j (mem_fin3 j)
      simpa [hj] using this
    · unfold hmmB at hq
      simp only [Bool.and_eq_true] at hq
      refine sq_HMM C hC G hG0 w hw τ ρ hpt r q hq.1.1 hq.1.2 fun j hj => ?_
      have := List.all_eq_true.mp hq.2 j (mem_fin3 j)
      simpa [hj] using this
  · unfold bbbB at hr
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
    refine sq_BBB C hC G hG0 w hw τ ρ hpt r (fun j => List.all_eq_true.mp hr.1 j (mem_fin3 j)) ?_
    have e : ∑ j : Fin (2 + 1), (if (code (τ (pos r j)) (ρ (pos r j))).bA then 1 else 0)
        = flag (cd (pos r 0)).bA + flag (cd (pos r 1)).bA + flag (cd (pos r 2)).bA := by
      rw [Fin.sum_univ_three]; rfl
    rw [e]
    have := hr.2
    unfold flag at this
    simp only [flag]
    omega
  · unfold hhhB at hr
    simp only [Bool.and_eq_true] at hr
    exact sq_HHH C hC G hG0 w hw τ ρ hpt r hr.1 fun j => List.all_eq_true.mp hr.2 j (mem_fin3 j)
  · unfold hhhcB at hr
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
    exact sq_HHHc C hC G hG0 w hw τ ρ hpt r hr.1 fun j => List.all_eq_true.mp hr.2 j (mem_fin3 j)

end Outerplanar
