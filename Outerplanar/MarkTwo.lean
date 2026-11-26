/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.MarkOne
import Outerplanar.SqHull17

/-!
# The two-mark class

Research note `ai_research_notes/OUTERPLANAR_ELEVEN_AND_CENTRAL_SQUARE_2026-11-23.md`, "Two marks":
*a branch with at most two marks dominates a mixture of the constant alternative and tables each
having floor `4/9`, bijection product at least `17/16`, `T ≥ 17/32`, and `AB`.*

* `P2 S T Y v` — floor `4/9 v`, `BijGe` with surplus `17/16`, `TB` with `17/32`, the ball with
  constant `v · 17/16`; `cone2`; `p1_p2` (one-mark tables are two-mark tables). The class is
  **`K2 = Mx P2`**.
* `p2_odd` — transport of `P2` through an odd face with one loaded edge. At a triangle Hall's
  condition may fail; then the bijection product is `2 T = 17/16`, exactly enough (`bij_one`).
* `p2_odd_two` — an odd face with two loaded one-mark edges: floor `(2/3)²`, bijection product
  `q²` (`(17/16)` at a Hall-failing triangle, from `2 (3/4)² = 9/8`), four-cell bound
  `(3/4)² = 9/16` (lossless, `tb_tri` and `tb_transport2` of `Outerplanar/Transport2.lean`; the
  note's rotation loss `324/343` is not needed), ball gain `A²`.
* `p2_even_one` — an even face with one loaded one-mark edge: floor `(2/3)²`, bijection `q`,
  four-cell `17/32` from `tb_square_hull17` at squares and `(3/4)(10/11)³` at longer faces, gain
  `A` by one-load closure.
* `mx2_odd_one`, `mx2_odd_two`, `mx2_even_one` — the face rules; `mx2_mul` (two one-mark factors),
  `p2_lift`, `p2_swap`.

The theorem of the note is due to another AI session of this repository's collaboration; audited
and formalized by Claude.
-/

namespace Outerplanar

open Finset

/-! ### The class -/

/-- The tables of the two-mark class, with constant `v`. -/
def P2 (S T : Finset ℕ) (Y : ℕ → ℕ → ℝ) (v : ℝ) : Prop :=
  Dominant S T Y (4 / 9 * v) ∧ BijGe S T Y v (17 / 16) ∧ TB S T Y v (17 / 32) ∧
    InBall S T Y (v * (17 / 16))

theorem cone2 : ConeP P2 where
  zero S T := ⟨fun _ _ _ _ _ => by simp, fun _ _ _ _ _ _ _ => by simp,
    fun _ _ _ _ _ _ _ _ _ _ _ _ => by simp, by rw [zero_mul]; exact InBall.zero fun _ _ => le_rfl⟩
  add := by
    intro S T Y Y' v v' hv hv' h0 h0' h h'
    refine ⟨?_, h.2.1.add (by norm_num) hv hv' h0 h0' h'.2.1,
      h.2.2.1.add (by norm_num) hv hv' h0 h0' h'.2.2.1, ?_⟩
    · have := h.1.add h'.1
      rwa [show 4 / 9 * v + 4 / 9 * v' = 4 / 9 * (v + v') by ring] at this
    · have := InBall.add (by positivity) (by positivity) h0 h0' h.2.2.2 h'.2.2.2
      rwa [show v * (17 / 16) + v' * (17 / 16) = (v + v') * (17 / 16) by ring] at this
  smul := by
    intro S T Y v l hl hv h0 h
    refine ⟨?_, h.2.1.smul hl, h.2.2.1.smul hl, ?_⟩
    · have := h.1.smul hl
      rwa [show l * (4 / 9 * v) = 4 / 9 * (l * v) by ring] at this
    · have := InBall.smul hl (by positivity) h.2.2.2
      rwa [show l * (v * (17 / 16)) = l * v * (17 / 16) by ring] at this
  mono := by
    intro S T Y Y' v h0 hle h
    exact ⟨h.1.mono hle, h.2.1.mono h0 hle, h.2.2.1.mono h0 hle, h.2.2.2.mono h0 hle⟩
  weaken := by
    intro S T Y v v' hv' hle _ h
    exact ⟨h.1.le (by linarith), h.2.1.weaken (by norm_num) hv' hle, h.2.2.1.weaken hv' hle,
      h.2.2.2.weaken (by positivity) (by linarith)⟩

theorem p1_p2 {S T : Finset ℕ} {Y : ℕ → ℕ → ℝ} {v : ℝ} (hv : 0 ≤ v) (h : P1 S T Y v) :
    P2 S T Y v :=
  ⟨h.1.le (by linarith), h.2.1.weakenQ hv (by norm_num), h.2.2.1.anti (by norm_num) (by norm_num),
    h.2.2.2.1⟩

theorem p2_swap {S T : Finset ℕ} {Y : ℕ → ℕ → ℝ} {v : ℝ} (h : P2 S T Y v) :
    P2 T S (fun d c => Y c d) v :=
  ⟨h.1.swap, h.2.1.swap, h.2.2.1.swap, h.2.2.2.swap⟩

theorem p2_lift {S T U : Finset ℕ} (hS : S.card = 3) (hT : T.card = 3) (hU : U.card = 3)
    {Y : ℕ → ℕ → ℝ} {v : ℝ} (hv : 0 ≤ v) (h0 : ∀ c d, 0 ≤ Y c d) (h : P2 S T Y v) :
    P2 S U (fun c _ => liftV T Y c) (2 * v) := by
  refine ⟨?_, h.2.1.lift hS hT h0 (by norm_num) hv, lift_tb hT h0 h.2.2.1, ?_⟩
  · have := lift_dom (U := U) (by positivity) hT h.1
    rwa [show 2 * (4 / 9 * v) = 4 / 9 * (2 * v) by ring] at this
  · have := lift_ball (U := U) hS hT hU h0 (by positivity) h.2.2.2
    rwa [show 2 * (v * (17 / 16)) = 2 * v * (17 / 16) by ring] at this

/-- **Two one-mark factors give a two-mark table.** -/
theorem p11_p2 {S T : Finset ℕ} {Y Y' : ℕ → ℕ → ℝ} {v v' : ℝ} (hv : 0 ≤ v) (hv' : 0 ≤ v')
    (h0 : ∀ c d, 0 ≤ Y c d) (h0' : ∀ c d, 0 ≤ Y' c d) (h : P1 S T Y v) (h' : P1 S T Y' v') :
    P2 S T (fun c d => Y c d * Y' c d) (v * v') := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := Dominant.mul (by positivity) (by positivity) h.1 h'.1
    rwa [show 2 / 3 * v * (2 / 3 * v') = 4 / 9 * (v * v') by ring] at this
  · exact (h.2.1.mul (by norm_num) hv (by norm_num) hv' h'.2.1).weakenQ (by positivity)
      (by norm_num)
  · exact (h.2.2.1.mul h'.2.2.1).anti (by norm_num) (by norm_num)
  · have := h.2.2.2.1.mul (by positivity) (by positivity) h'.2.2.2.1
    exact this.weaken (by positivity) (by nlinarith [mul_nonneg hv hv'])

/-- Products of two one-mark profiles. -/
theorem mx2_mul {S T : Finset ℕ} {W W' : ℕ → ℕ → ℝ} {N N' : ℝ} (hN' : 0 ≤ N')
    (h : Mx P1 S T W N) (h' : Mx P1 S T W' N') :
    Mx P2 S T (fun c d => W c d * W' c d) (N * N') :=
  Mx.mul cone2 hN' (fun hv _ h => p1_p2 hv h) (fun hv _ h => p1_p2 hv h)
    (fun hv hv' h0 h0' h h' => p11_p2 hv hv' h0 h0' h h') h h'

/-! ### Faces -/

section Faces

variable {m : ℕ} {Lu Lv : Finset ℕ} {Li : Fin m → Finset ℕ} {E : Fin (m + 1) → ℕ → ℕ → ℝ}
  {A : Fin (m + 1) → ℝ}

/-- **Transport of the two-mark tables through an odd face with one loaded edge.** -/
theorem p2_odd (hm : Odd m) (hLu : Lu.card = 3) (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3)
    (hE0 : ∀ j c d, 0 ≤ E j c d) (hA : ∀ j, 0 < A j) {j₀ : Fin (m + 1)}
    (hP : P2 (pathList Lu Lv Li j₀.castSucc) (pathList Lu Lv Li j₀.succ) (E j₀) (A j₀))
    (hD : ∀ j, j ≠ j₀ →
      Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    P2 Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j) := by
  obtain ⟨hF, hB, hT, hBall⟩ := hP
  have hα : oddB m = faceConst3 m := by
    have := oddB_div_odd hm
    rwa [div_eq_one_iff_eq (faceConst3_pos m).ne'] at this
  refine ⟨?_, ?_, ?_, ball_one hLu hLv hLi hE0 hA (by norm_num) hBall hD⟩
  · have := floor_one hLi hE0 hA (by norm_num) hF hD
    rwa [hα, show faceConst3 m * (4 / 9 * ∏ j, A j) = 4 / 9 * (faceConst3 m * ∏ j, A j) by ring]
      at this
  · exact bij_one hLu hLv hLi hE0 hA hm.pos (by norm_num) (by norm_num : (0 : ℝ) < 4 / 9)
      (fun _ => by norm_num) hF hB hT hD
  · have := tb_transport m Lu Lv Li hLv hLi j₀ E hE0 A hA hT hD
    rwa [faceConst3_odd_dd hm, one_pow, mul_one] at this

/-- The floor through a face with two loaded edges. -/
theorem floor_two (hLi : ∀ j, (Li j).card = 3) (hE0 : ∀ j c d, 0 ≤ E j c d) (hA : ∀ j, 0 < A j)
    {j₁ j₂ : Fin (m + 1)} (h12 : j₁ ≠ j₂) {l₁ l₂ : ℝ} (hl₁ : 0 ≤ l₁) (hl₂ : 0 ≤ l₂)
    (hF₁ : Dominant (pathList Lu Lv Li j₁.castSucc) (pathList Lu Lv Li j₁.succ) (E j₁) (l₁ * A j₁))
    (hF₂ : Dominant (pathList Lu Lv Li j₂.castSucc) (pathList Lu Lv Li j₂.succ) (E j₂) (l₂ * A j₂))
    (hD : ∀ j, j ≠ j₁ → j ≠ j₂ →
      Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    Dominant Lu Lv (faceSum Li (fun _ _ => 1) E) (oddB m * (l₁ * (l₂ * ∏ j, A j))) := by
  set B : Fin (m + 1) → ℝ := fun j => if j = j₂ then l₂ * A j else A j with hBdef
  have hB0 : ∀ j, 0 ≤ B j := fun j => by
    simp only [hBdef]
    split_ifs
    · exact mul_nonneg hl₂ (hA j).le
    · exact (hA j).le
  have h := dom_face_bare Lu Lv Li hLi E hE0 (fun j => if j = j₁ then l₁ * B j else B j)
    (fun j => by
      split_ifs
      · exact mul_nonneg hl₁ (hB0 j)
      · exact hB0 j) fun j => by
      by_cases hj1 : j = j₁
      · subst hj1; simpa [hBdef, h12] using hF₁
      · by_cases hj2 : j = j₂
        · subst hj2; simpa [hBdef, hj1] using hF₂
        · simpa [hBdef, hj1, hj2] using hD j hj1 hj2
  rwa [prod_ite_scale, hBdef, prod_ite_scale] at h

/-- **An odd face with two loaded one-mark edges gives a two-mark table.** -/
theorem p2_odd_two (hm : Odd m) (hLu : Lu.card = 3) (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3)
    (hE0 : ∀ j c d, 0 ≤ E j c d) (hA : ∀ j, 0 < A j) {j₁ j₂ : Fin (m + 1)} (h12 : j₁ < j₂)
    (hP₁ : P1 (pathList Lu Lv Li j₁.castSucc) (pathList Lu Lv Li j₁.succ) (E j₁) (A j₁))
    (hP₂ : P1 (pathList Lu Lv Li j₂.castSucc) (pathList Lu Lv Li j₂.succ) (E j₂) (A j₂))
    (hD : ∀ j, j ≠ j₁ → j ≠ j₂ →
      Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    P2 Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j) := by
  have hne : j₁ ≠ j₂ := ne_of_lt h12
  have hα : oddB m = faceConst3 m := by
    have := oddB_div_odd hm
    rwa [div_eq_one_iff_eq (faceConst3_pos m).ne'] at this
  have hαpos := faceConst3_pos m
  have hP0 : 0 < ∏ j, A j := Finset.prod_pos fun j _ => hA j
  have hpos : ∀ j, ∀ c ∈ pathList Lu Lv Li j.castSucc, ∀ d ∈ pathList Lu Lv Li j.succ, c ≠ d →
      0 < E j c d := fun j c hc d hd hcd => by
    by_cases h1 : j = j₁
    · subst h1; exact lt_of_lt_of_le (by have := hA j; positivity) (hP₁.1 c hc d hd hcd)
    · by_cases h2 : j = j₂
      · subst h2; exact lt_of_lt_of_le (by have := hA j; positivity) (hP₂.1 c hc d hd hcd)
      · exact lt_of_lt_of_le (hA j) (hD j h1 h2 c hc d hd hcd)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- floor
    have := floor_two hLi hE0 hA hne (by norm_num) (by norm_num) hP₁.1 hP₂.1 hD
    rwa [hα, show faceConst3 m * (2 / 3 * (2 / 3 * ∏ j, A j))
      = 4 / 9 * (faceConst3 m * ∏ j, A j) by ring] at this
  · -- bijections
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · obtain rfl : m = 1 := by obtain ⟨k, hk⟩ := hm; omega
      have e1 : j₁.val < j₂.val := h12
      have e2 := j₂.isLt
      obtain rfl : j₁ = 0 := Fin.ext (by simp; omega)
      obtain rfl : j₂ = 1 := Fin.ext (by simp; omega)
      have key := bijGe_tri hLu hLv hLi E hE0 A ![17 / 16, 1] ![3 / 4, 3 / 4] hA
        (fun j => by fin_cases j <;> norm_num) hpos
        (fun j => by
          fin_cases j
          · exact hP₁.2.1.weakenQ (hA 0).le (by norm_num)
          · exact hP₂.2.1.weakenQ (hA 1).le (by norm_num))
        (fun j => by
          fin_cases j
          · exact hP₁.2.2.1
          · exact hP₂.2.2.1)
        (by norm_num)
      rw [faceConst3_one, one_mul]
      simpa [Fin.prod_univ_two] using key
    · have hQ : ∀ j, BijGe (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)
          (if j = j₁ then 32 / 27 else if j = j₂ then 32 / 27 else 1) := fun j => by
        by_cases h1 : j = j₁
        · subst h1; simpa using hP₁.2.1
        · by_cases h2 : j = j₂
          · subst h2; simpa [h1] using hP₂.2.1
          · simpa [h1, h2] using (hD j h1 h2).bijGe (hA j).le
      have key := bijGe_face hm2 Lu Lv Li hLu hLv hLi E hE0 A _ hA
        (fun j => by split_ifs <;> norm_num) hpos hQ
      have hprod : ∏ j, (if j = j₁ then (32 / 27 : ℝ) else if j = j₂ then 32 / 27 else 1)
          = (32 / 27) * (32 / 27) := by
        have e : ∀ j, (if j = j₁ then (32 / 27 : ℝ) else if j = j₂ then 32 / 27 else 1)
            = (if j = j₁ then 32 / 27 * (if j = j₂ then 32 / 27 else 1)
              else if j = j₂ then 32 / 27 else 1) := fun j => by
          by_cases h1 : j = j₁
          · subst h1; simp [hne]
          · simp [h1]
        simp only [e]
        rw [prod_ite_scale, prod_ite_one]
      rw [hprod] at key
      exact key.weakenQ (by positivity) (by norm_num)
  · -- four cells
    rcases Nat.lt_or_ge m 3 with hm3 | hm3
    · obtain rfl : m = 1 := by obtain ⟨k, hk⟩ := hm; omega
      have e1 : j₁.val < j₂.val := h12
      have e2 := j₂.isLt
      obtain rfl : j₁ = 0 := Fin.ext (by simp; omega)
      obtain rfl : j₂ = 1 := Fin.ext (by simp; omega)
      have key := tb_tri hLi hE0 (τ := ![3 / 4, 3 / 4]) fun j => by
        fin_cases j
        · exact hP₁.2.2.1
        · exact hP₂.2.2.1
      rw [faceConst3_one, one_mul]
      exact key.anti (by norm_num) (by simp; norm_num)
    · have key := tb_transport2 m hm hm3 Lu Lv Li hLv hLi j₁ j₂ h12 E hE0 A hA hP₁.2.2.1
        hP₂.2.2.1 hD
      exact key.anti (by norm_num) (by norm_num)
  · -- ball
    have hB : ∀ j, InBall (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j)
        (if j = j₁ then 17 / 16 * A j else if j = j₂ then 17 / 16 * A j else A j) := fun j => by
      by_cases h1 : j = j₁
      · subst h1; simpa [mul_comm] using hP₁.2.2.2.1
      · by_cases h2 : j = j₂
        · subst h2; simpa [h1, mul_comm] using hP₂.2.2.2.1
        · simpa [h1, h2] using (hD j h1 h2).inBall (hA j).le
    have hBpos : ∀ j, 0 < (if j = j₁ then 17 / 16 * A j else if j = j₂ then 17 / 16 * A j
        else A j) := fun j => by
      split_ifs <;> first | exact hA j | exact mul_pos (by norm_num) (hA j)
    have hprod : ∏ j, (if j = j₁ then 17 / 16 * A j else if j = j₂ then 17 / 16 * A j else A j)
        = 17 / 16 * (17 / 16 * ∏ j, A j) := by
      have e : ∀ j, (if j = j₁ then 17 / 16 * A j else if j = j₂ then 17 / 16 * A j else A j)
          = (if j = j₁ then 17 / 16 * (if j = j₂ then 17 / 16 * A j else A j)
            else if j = j₂ then 17 / 16 * A j else A j) := fun j => by
        by_cases h1 : j = j₁
        · subst h1; simp [hne]
        · simp [h1]
      simp only [e]
      rw [prod_ite_scale, prod_ite_scale]
    have key : InBall Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * (17 / 16 * (17 / 16 *
        ∏ j, A j))) := by
      rw [← hprod]
      rcases Nat.lt_or_ge m 3 with hm3 | hm3
      · obtain rfl : m = 1 := by obtain ⟨k, hk⟩ := hm; omega
        rw [faceConst3_one, one_mul]
        exact ballTriClosed Lu Lv Li hLu hLv hLi E hE0 _ hBpos hB
      · exact ballOddClosed m hm hm3 Lu Lv Li hLu hLv hLi E hE0 _ hBpos hB
    exact key.weaken (by positivity) (by nlinarith)

/-- **An even face with one loaded one-mark edge gives a two-mark table.** -/
theorem p2_even_one (hm : Even m) (hm2 : 2 ≤ m) (hLu : Lu.card = 3) (hLv : Lv.card = 3)
    (hLi : ∀ j, (Li j).card = 3) (hE0 : ∀ j c d, 0 ≤ E j c d) (hA : ∀ j, 0 < A j)
    {j₀ : Fin (m + 1)}
    (hP : P1 (pathList Lu Lv Li j₀.castSucc) (pathList Lu Lv Li j₀.succ) (E j₀) (A j₀))
    (hD : ∀ j, j ≠ j₀ →
      Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    P2 Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j) := by
  obtain ⟨hF, hB, hT, hBall, hH⟩ := hP
  have hαpos := faceConst3_pos m
  have hP0 : 0 < ∏ j, A j := Finset.prod_pos fun j _ => hA j
  have hα3 : (3 : ℝ) ≤ faceConst3 m := by
    obtain ⟨k, hk⟩ := hm
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [hk, show k' + 1 + (k' + 1) = 2 * k' + 2 by ring]
    exact faceConst3_even_ge_three k'
  have hoddB : oddB m = faceConst3 m - 1 := by
    obtain ⟨k, hk⟩ := hm
    rw [hk, ← two_mul, oddB_even]
  refine ⟨?_, ?_, ?_, ball_one hLu hLv hLi hE0 hA (by norm_num) hBall hD⟩
  · have := floor_one hLi hE0 hA (by norm_num) hF hD
    rw [hoddB] at this
    refine this.le ?_
    nlinarith
  · exact (bij_one hLu hLv hLi hE0 hA (by omega) (by norm_num) (by norm_num : (0 : ℝ) < 2 / 3)
      (fun h => by omega) hF hB hT hD).weakenQ (by positivity) (by norm_num)
  · rcases Nat.lt_or_ge m 4 with hm4 | hm4
    · obtain rfl : m = 2 := by obtain ⟨k, hk⟩ := hm; omega
      exact tb_square_hull17 Lu Lv Li hLu hLv hLi j₀ E hE0 A hA hH hD
    · have key := tb_transport m Lu Lv Li hLv hLi j₀ E hE0 A hA hT hD
      have hdd : 10 / 11 ≤ dd j₀ (m - j₀) / faceConst3 m := by
        rw [dd_face]
        simp only [hm, ↓reduceIte]
        rw [← hoddB]
        exact oddB_div_even hm hm4
      refine key.anti (by norm_num) ?_
      have h3 : (10 / 11 : ℝ) ^ 3 ≤ (dd j₀ (m - j₀) / faceConst3 m) ^ 3 :=
        pow_le_pow_left₀ (by norm_num) hdd 3
      nlinarith

end Faces

/-! ### The face rules -/

section Rules

variable {m : ℕ} (Lu Lv : Finset ℕ) (Li : Fin m → Finset ℕ) (E : Fin (m + 1) → ℕ → ℕ → ℝ)
  (A : Fin (m + 1) → ℝ)

theorem wT_prod_pos {u v : Fin (m + 1) → ℝ} {ρ : Fin (m + 1) → Fin 2}
    (hρ : ∀ j, 0 < wT u v j (ρ j)) : 0 ≤ faceConst3 m * ∏ j, wT u v j (ρ j) :=
  (mul_pos (faceConst3_pos m) (Finset.prod_pos fun j _ => hρ j)).le

/-- **An odd face with one side in the two-mark class and greedy other sides.** -/
theorem mx2_odd_one (hm : Odd m) (hLu : Lu.card = 3) (hLv : Lv.card = 3)
    (hLi : ∀ j, (Li j).card = 3) (j₀ : Fin (m + 1)) (hE0 : ∀ j c d, 0 ≤ E j c d)
    (hA : ∀ j, 0 < A j)
    (hK : Mx P2 (pathList Lu Lv Li j₀.castSucc) (pathList Lu Lv Li j₀.succ) (E j₀) (A j₀))
    (hD : ∀ j, j ≠ j₀ →
      Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    Mx P2 Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j) := by
  have hE : ∀ j, Mx P2 (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j) :=
    fun j => by
      by_cases hj : j = j₀
      · subst hj; exact hK
      · exact Mx.of_dom cone2 (hA j).le (hD j hj)
  obtain ⟨u, v, Y, hu, hv, huv, hY0, hY, hEY, hDv⟩ :=
    mx_data (Pc := fun _ => P2) (fun _ => cone2) hA hE (fun j => j ≠ j₀) hD
  refine mx_expand cone2 Lu Lv Li E hE0 A hA hu hv huv hY0 hEY fun ρ hρ => ?_
  have h0 : ∀ j, j ≠ j₀ → ρ j = 0 := term_D hDv hρ
  have hG0 := gT_nonneg hu hY0
  have hdom : ∀ j, j ≠ j₀ → Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ)
      (gT u Y j (ρ j)) (wT u v j (ρ j)) := fun j hj => gT_dom _ _ j (h0 j hj)
  by_cases hr : ρ j₀ = 0
  · refine Mx.of_dom cone2 (wT_prod_pos hρ) (domFaceClosed_odd m hm Lu Lv Li hLi _
      (fun j c d => hG0 j (ρ j) c d) _ hρ fun j => ?_)
    by_cases hj : j = j₀
    · subst hj; exact gT_dom _ _ _ hr
    · exact hdom j hj
  · exact Mx.of_P (wT_prod_pos hρ) (faceSum_nonneg _ _ _ (fun _ _ _ => zero_le_one)
      (fun j c d => hG0 j (ρ j) c d)) (p2_odd hm hLu hLv hLi (fun j c d => hG0 j (ρ j) c d) hρ
        (gT_P cone2 j₀ hr (hY0 j₀) (hY j₀)) hdom)

/-- **An odd face with two sides in the one-mark class and greedy other sides.** -/
theorem mx2_odd_two (hm : Odd m) (hLu : Lu.card = 3) (hLv : Lv.card = 3)
    (hLi : ∀ j, (Li j).card = 3) (j₁ j₂ : Fin (m + 1)) (h12 : j₁ ≠ j₂)
    (hE0 : ∀ j c d, 0 ≤ E j c d) (hA : ∀ j, 0 < A j)
    (hK₁ : Mx P1 (pathList Lu Lv Li j₁.castSucc) (pathList Lu Lv Li j₁.succ) (E j₁) (A j₁))
    (hK₂ : Mx P1 (pathList Lu Lv Li j₂.castSucc) (pathList Lu Lv Li j₂.succ) (E j₂) (A j₂))
    (hD : ∀ j, j ≠ j₁ → j ≠ j₂ →
      Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    Mx P2 Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j) := by
  have hE : ∀ j, Mx P1 (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j) :=
    fun j => by
      by_cases h1 : j = j₁
      · subst h1; exact hK₁
      · by_cases h2 : j = j₂
        · subst h2; exact hK₂
        · exact Mx.of_dom cone1 (hA j).le (hD j h1 h2)
  obtain ⟨u, v, Y, hu, hv, huv, hY0, hY, hEY, hDv⟩ :=
    mx_data (Pc := fun _ => P1) (fun _ => cone1) hA hE (fun j => j ≠ j₁ ∧ j ≠ j₂)
      fun j hj => hD j hj.1 hj.2
  refine mx_expand cone2 Lu Lv Li E hE0 A hA hu hv huv hY0 hEY fun ρ hρ => ?_
  have h0 : ∀ j, j ≠ j₁ → j ≠ j₂ → ρ j = 0 := fun j h1 h2 => term_D hDv hρ j ⟨h1, h2⟩
  have hG0 := gT_nonneg hu hY0
  have hG0' : ∀ j c d, 0 ≤ gT u Y j (ρ j) c d := fun j c d => hG0 j (ρ j) c d
  have hFn := faceSum_nonneg Li (fun _ _ => 1) _ (fun _ _ _ => zero_le_one) hG0'
  have hdomj : ∀ j, ρ j = 0 → Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ)
      (gT u Y j (ρ j)) (wT u v j (ρ j)) := fun j hj => gT_dom _ _ j hj
  have hPj : ∀ j, ρ j ≠ 0 → P1 (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ)
      (gT u Y j (ρ j)) (wT u v j (ρ j)) := fun j hj => gT_P cone1 j hj (hY0 j) (hY j)
  by_cases r1 : ρ j₁ = 0 <;> by_cases r2 : ρ j₂ = 0
  · refine Mx.of_dom cone2 (wT_prod_pos hρ) (domFaceClosed_odd m hm Lu Lv Li hLi _ hG0' _ hρ
      fun j => hdomj j ?_)
    by_cases h1 : j = j₁
    · rwa [h1]
    · by_cases h2 : j = j₂
      · rwa [h2]
      · exact h0 j h1 h2
  · refine Mx.of_P (wT_prod_pos hρ) hFn (p1_p2 (wT_prod_pos hρ) (p1_odd hm hLu hLv hLi hG0' hρ
      (hPj j₂ r2) fun j hj => hdomj j ?_))
    by_cases h1 : j = j₁
    · rwa [h1]
    · exact h0 j h1 hj
  · refine Mx.of_P (wT_prod_pos hρ) hFn (p1_p2 (wT_prod_pos hρ) (p1_odd hm hLu hLv hLi hG0' hρ
      (hPj j₁ r1) fun j hj => hdomj j ?_))
    by_cases h2 : j = j₂
    · rwa [h2]
    · exact h0 j hj h2
  · refine Mx.of_P (wT_prod_pos hρ) hFn ?_
    rcases lt_or_gt_of_ne h12 with hlt | hgt
    · exact p2_odd_two hm hLu hLv hLi hG0' hρ hlt (hPj j₁ r1) (hPj j₂ r2)
        fun j h1 h2 => hdomj j (h0 j h1 h2)
    · exact p2_odd_two hm hLu hLv hLi hG0' hρ hgt (hPj j₂ r2) (hPj j₁ r1)
        fun j h2 h1 => hdomj j (h0 j h1 h2)

/-- **An even face with one side in the one-mark class and greedy other sides.** -/
theorem mx2_even_one (hm : Even m) (hm2 : 2 ≤ m) (hLu : Lu.card = 3) (hLv : Lv.card = 3)
    (hLi : ∀ j, (Li j).card = 3) (j₀ : Fin (m + 1)) (hE0 : ∀ j c d, 0 ≤ E j c d)
    (hA : ∀ j, 0 < A j)
    (hK : Mx P1 (pathList Lu Lv Li j₀.castSucc) (pathList Lu Lv Li j₀.succ) (E j₀) (A j₀))
    (hD : ∀ j, j ≠ j₀ →
      Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    Mx P2 Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j) := by
  have hE : ∀ j, Mx P1 (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j) :=
    fun j => by
      by_cases hj : j = j₀
      · subst hj; exact hK
      · exact Mx.of_dom cone1 (hA j).le (hD j hj)
  obtain ⟨u, v, Y, hu, hv, huv, hY0, hY, hEY, hDv⟩ :=
    mx_data (Pc := fun _ => P1) (fun _ => cone1) hA hE (fun j => j ≠ j₀) hD
  refine mx_expand cone2 Lu Lv Li E hE0 A hA hu hv huv hY0 hEY fun ρ hρ => ?_
  have h0 : ∀ j, j ≠ j₀ → ρ j = 0 := term_D hDv hρ
  have hG0 := gT_nonneg hu hY0
  have hdom : ∀ j, j ≠ j₀ → Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ)
      (gT u Y j (ρ j)) (wT u v j (ρ j)) := fun j hj => gT_dom _ _ j (h0 j hj)
  by_cases hr : ρ j₀ = 0
  · refine Mx.imp (fun hv _ h => p1_p2 hv h) (mx1_even_bare hm hm2 Lu Lv Li hLu hLv hLi _
      (fun j c d => hG0 j (ρ j) c d) _ (fun j => (hρ j).le) fun j => ?_)
    by_cases hj : j = j₀
    · subst hj; exact gT_dom _ _ _ hr
    · exact hdom j hj
  · exact Mx.of_P (wT_prod_pos hρ) (faceSum_nonneg _ _ _ (fun _ _ _ => zero_le_one)
      (fun j c d => hG0 j (ρ j) c d)) (p2_even_one hm hm2 hLu hLv hLi
        (fun j c d => hG0 j (ρ j) c d) hρ (gT_P cone1 j₀ hr (hY0 j₀) (hY j₀)) hdom)

end Rules

end Outerplanar
