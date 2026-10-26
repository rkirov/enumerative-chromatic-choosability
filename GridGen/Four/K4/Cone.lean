/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.K4.Defs

/-!
# Height four at `k = 4`: the twelve-ray cone `K` contains every uniform future

Codex's (OpenAI) invariant cone (`ai_research_notes/cx/h4k4/NOTE.md`, "The uniform transfer and
cones are not the obstruction"; reproduced in `ai_research_notes/H4_K4_REVIEW_2026-10-26.md`
Part 1(a)). The uniform futures by class are `fv i = Hⁱ 1` (`fv`). The first four are the rays
`F₀, …, F₃` of `K`. The tail box

  `T = [0.9453, 0.9454] × [0.8592, 0.8594] × [0.8907, 0.8909]`

of normalised weights, as a cone `InT`, is mapped into itself by `H` (`InT_Hm`: each image
constraint is a nonnegative combination of the box constraints), and `fv 4` lies in it
(`InT_fv_four`). A linear form nonnegative at the eight corners `(1, t)` is nonnegative on that
cone (`dot_nonneg_of_InT`). Hence a class vector nonnegative at the twelve rays is nonnegative at
every uniform future (`cone_fv`): checking a seam on the twelve rays covers every horizon.
-/

namespace GridGen.Four.K4

/-- The uniform futures by class: `fv i = Hⁱ (1, 1, 1, 1)`. -/
def fv : ℕ → Q
  | 0 => (1, 1, 1, 1)
  | i + 1 => Hm (fv i)

theorem fv_succ (i : ℕ) : fv (i + 1) = Hm (fv i) := rfl

theorem fv_one : fv 1 = (41, 39, 36, 37) := by decide

theorem fv_two : fv 2 = (1579, 1494, 1361, 1409) := by decide

theorem fv_three : fv 3 = (60371, 57080, 51896, 53789) := by decide

theorem fv_four : fv 4 = (2305885, 2179959, 1981401, 2054033) := by decide

/-- The tail box `T` of normalised weights, as a cone. -/
def InT (w : Q) : Prop :=
  0 < w.1 ∧ 9453 * w.1 ≤ 10000 * w.2.1 ∧ 10000 * w.2.1 ≤ 9454 * w.1 ∧
    8592 * w.1 ≤ 10000 * w.2.2.1 ∧ 10000 * w.2.2.1 ≤ 8594 * w.1 ∧
    8907 * w.1 ≤ 10000 * w.2.2.2 ∧ 10000 * w.2.2.2 ≤ 8909 * w.1

/-- **The tail box is invariant** under the uniform transfer. -/
theorem InT_Hm {w : Q} (h : InT w) : InT (Hm w) := by
  obtain ⟨w1, w2, w3, w4⟩ := w
  simp only [InT, Hm, dot] at h ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith⟩

theorem InT_fv_four : InT (fv 4) := by
  rw [fv_four]; unfold InT; norm_num

theorem InT_fv : ∀ i, InT (fv (i + 4))
  | 0 => InT_fv_four
  | i + 1 => by
      rw [show i + 1 + 4 = (i + 4) + 1 by omega, fv_succ]
      exact InT_Hm (InT_fv i)

/-- A class vector nonnegative at the eight corner rays is nonnegative on the tail cone. -/
theorem dot_nonneg_of_InT {d w : Q} (hd : RaysOK d) (hw : InT w) : 0 ≤ dot d w := by
  obtain ⟨d1, d2, d3, d4⟩ := d
  obtain ⟨W, X, Y, Z⟩ := w
  simp only [InT] at hw
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hw
  have c : ∀ a b c : ℤ, ((10000, a, b, c) : Q) ∈ rays → 0 ≤ d1 * 10000 + d2 * a + d3 * b + d4 * c :=
    fun a b c hr => by have := hd _ hr; simpa [dot] using this
  have c1 := c 9453 8592 8907 (by simp [rays])
  have c2 := c 9453 8592 8909 (by simp [rays])
  have c3 := c 9453 8594 8907 (by simp [rays])
  have c4 := c 9453 8594 8909 (by simp [rays])
  have c5 := c 9454 8592 8907 (by simp [rays])
  have c6 := c 9454 8592 8909 (by simp [rays])
  have c7 := c 9454 8594 8907 (by simp [rays])
  have c8 := c 9454 8594 8909 (by simp [rays])
  have hW : (0 : ℤ) ≤ W := h0.le
  have hx : d2 * (9453 * W) ≤ d2 * (10000 * X) ∨ d2 * (9454 * W) ≤ d2 * (10000 * X) := by
    rcases le_total 0 d2 with h | h
    · exact Or.inl (mul_le_mul_of_nonneg_left h1 h)
    · exact Or.inr (mul_le_mul_of_nonpos_left h2 h)
  have hy : d3 * (8592 * W) ≤ d3 * (10000 * Y) ∨ d3 * (8594 * W) ≤ d3 * (10000 * Y) := by
    rcases le_total 0 d3 with h | h
    · exact Or.inl (mul_le_mul_of_nonneg_left h3 h)
    · exact Or.inr (mul_le_mul_of_nonpos_left h4 h)
  have hz : d4 * (8907 * W) ≤ d4 * (10000 * Z) ∨ d4 * (8909 * W) ≤ d4 * (10000 * Z) := by
    rcases le_total 0 d4 with h | h
    · exact Or.inl (mul_le_mul_of_nonneg_left h5 h)
    · exact Or.inr (mul_le_mul_of_nonpos_left h6 h)
  simp only [dot]
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hz with hz | hz <;>
    nlinarith [mul_nonneg hW c1, mul_nonneg hW c2, mul_nonneg hW c3, mul_nonneg hW c4,
      mul_nonneg hW c5, mul_nonneg hW c6, mul_nonneg hW c7, mul_nonneg hW c8]

/-- **Every uniform future lies in `K`**: a class vector nonnegative at the twelve rays is
nonnegative at `fv i` for every horizon `i`. -/
theorem cone_fv {d : Q} (hd : RaysOK d) : ∀ i, 0 ≤ dot d (fv i)
  | 0 => hd _ (by simp [rays, fv])
  | 1 => by rw [fv_one]; exact hd _ (by simp [rays])
  | 2 => by rw [fv_two]; exact hd _ (by simp [rays])
  | 3 => by rw [fv_three]; exact hd _ (by simp [rays])
  | i + 4 => dot_nonneg_of_InT hd (InT_fv i)

end GridGen.Four.K4
