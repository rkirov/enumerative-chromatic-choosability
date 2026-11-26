/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.FifteenEven
import Outerplanar.Sq15Runs

/-!
# Five marks give the ball class

Research note `ai_research_notes/OUTERPLANAR_FIFTEEN_EVEN_2026-11-25.md`, step 2, and
`ai_research_notes/outerplanar/fivemarks/results.md` §1: **a branch with five marks is in `B`**
(with the floor `(2/3)⁵` of Lemma F). The only new step is an even face whose active sides carry
four marks (`term_even5`):

* one active side: one-load closure;
* faces of length at least six, at least two active sides (each with at most three marks, in
  `A B`): the ball design, `(16/17) A² ≥ 1`;
* squares: `(3|1)` by **L31** in all six placements, `(2|2)` by **L22** in all three, and
  `(2|1|1)` by the cap `(A q²)^{191} (2/3)^{135} ≥ 1` (here with `7/5 ≤ A q²`).

The square lemmas are the kernel-checked runs of `Outerplanar/Sq15Runs.lean` (milestone M4).
The list classes of the runs are read off the pure types (`cls0`, `clsZ`, `clsW`, `clsABf`,
`clsBAHf`, `clsBf5`, ...).

Formalized by Claude (milestone M5 of `ai_research_notes/OUTERPLANAR_13_15_LEAN_PLAN.md`).
-/

namespace Outerplanar.F15

open Finset Outerplanar Outerplanar.SqMulti

/-! ### The list classes of a pure type -/

theorem d6_le_A' : d6 ≤ 17 / 16 :=
  le_of_cube_le d6_pos.le (by norm_num) (by rw [d6_cube]; norm_num)

section Cls

variable {S T : Finset ℕ} {Y : ℕ → ℕ → ℝ} {v : ℝ} {k : ℕ} {r : Fin 3}

theorem act_val (hv : 0 < v) (h : PT k r S T Y v) {x : ℕ} (hx : (if r = 0 then 0 else k) = x)
    (hx0 : 1 ≤ x) : r ≠ 0 ∧ k = x := by
  by_cases hr : r = 0
  · simp [hr] at hx; omega
  · simp only [hr, ↓reduceIte] at hx
    exact ⟨hr, hx⟩

theorem cls0 (h : PT k r S T Y v) (hx : (if r = 0 then 0 else k) = 0) (hv : 0 < v) :
    Dominant S T Y v := by
  by_cases hr : r = 0
  · exact h.1 hr
  · simp only [hr, ↓reduceIte] at hx
    exact absurd (pt_ge1 hv hr h) (by omega)

theorem clsZ (h : PT k r S T Y v) (hx : (if r = 0 then 0 else k) = 1) (hv : 0 < v) :
    ClsZ S T Y v := by
  obtain ⟨hr, rfl⟩ := act_val hv h hx le_rfl
  have h1 := (h.2.1 (pt_one hv hr (by norm_num) h))
  exact ⟨h1.1, h1.2.1, by rw [mul_comm]; exact h1.2.2.2.1⟩

theorem clsW (h : PT k r S T Y v) (hx : (if r = 0 then 0 else k) = 2) (hv : 0 < v) :
    ClsW S T Y v := by
  obtain ⟨hr, rfl⟩ := act_val hv h hx (by norm_num)
  have h1 := (h.2.1 (pt_one hv hr (by norm_num) h))
  exact ⟨h1.1, h1.2.1, by rw [mul_comm]; exact h1.2.2.2⟩

theorem clsABf' (h : PT k r S T Y v) (hr : r = 1) (hk : k ≤ 3) (hv : 0 < v) :
    ClsABf S T Y v := by
  have hk1 := pt_ge1 hv (by rw [hr]; decide) h
  refine ⟨?_, by rw [mul_comm]; exact pt_ballA hv hr hk h⟩
  have := PA_floor hv.le hk1 (h.2.1 hr)
  exact this.le (mul_le_mul_of_nonneg_right ((fl_anti hk).trans' (by unfold fl; norm_num)) hv.le)

theorem clsABf (h : PT k r S T Y v) (hx : (if r = 0 then 0 else k) = 3) (hv : 0 < v) :
    ClsABf S T Y v := by
  obtain ⟨hr, rfl⟩ := act_val hv h hx (by norm_num)
  exact clsABf' h (pt_one hv hr (by norm_num) h) le_rfl hv

theorem clsBAHf' (h : PT k r S T Y v) (hr : r = 1) (hk : k ≤ 4) (hv : 0 < v)
    (h0 : ∀ c d, 0 ≤ Y c d) : ClsBAHf S T Y v := by
  have hk1 := pt_ge1 hv (by rw [hr]; decide) h
  refine ⟨?_, pt_ball hv (by rw [hr]; decide) h, by rw [mul_comm]; exact pt_hexA hv h0 hr hk h⟩
  have := PA_floor hv.le hk1 (h.2.1 hr)
  exact this.le (mul_le_mul_of_nonneg_right ((fl_anti hk).trans' (by unfold fl; norm_num)) hv.le)

theorem clsBAHf (h : PT k r S T Y v) (hx : (if r = 0 then 0 else k) = 4) (hv : 0 < v)
    (h0 : ∀ c d, 0 ≤ Y c d) : ClsBAHf S T Y v := by
  obtain ⟨hr, rfl⟩ := act_val hv h hx (by norm_num)
  exact clsBAHf' h (pt_one hv hr (by norm_num) h) le_rfl hv h0

theorem clsBf' (h : PT k r S T Y v) (hr : r = 1) {n : ℕ} (hk : k ≤ n) (hv : 0 < v) :
    InBall S T Y v ∧ Dominant S T Y (fl n * v) := by
  have hk1 := pt_ge1 hv (by rw [hr]; decide) h
  refine ⟨pt_ball hv (by rw [hr]; decide) h, ?_⟩
  exact (PA_floor hv.le hk1 (h.2.1 hr)).le (mul_le_mul_of_nonneg_right (fl_anti hk) hv.le)

theorem clsBf5' (h : PT k r S T Y v) (hr : r = 1) (hk : k ≤ 5) (hv : 0 < v) :
    ClsBf5 S T Y v := by
  obtain ⟨h1, h2⟩ := clsBf' h hr hk hv
  exact ⟨h2.le (by unfold fl; norm_num), h1⟩

theorem clsBf6' (h : PT k r S T Y v) (hr : r = 1) (hk : k ≤ 6) (hv : 0 < v) :
    ClsBf6 S T Y v := by
  obtain ⟨h1, h2⟩ := clsBf' h hr hk hv
  exact ⟨h2.le (by unfold fl; norm_num), h1⟩

theorem clsBf5 (h : PT k r S T Y v) (hx : (if r = 0 then 0 else k) = 5) (hv : 0 < v) :
    ClsBf5 S T Y v := by
  obtain ⟨hr, rfl⟩ := act_val hv h hx (by norm_num)
  exact clsBf5' h (pt_one hv hr le_rfl h) le_rfl hv

theorem clsH7f' (h : PT k r S T Y v) (hk : k ≤ 7) (hr : r = 2 ∨ (r = 1 ∧ k ≤ 4)) (hv : 0 < v)
    (h0 : ∀ c d, 0 ≤ Y c d) : ClsH7f S T Y v := by
  have hr0 : r ≠ 0 := by rcases hr with rfl | ⟨rfl, -⟩ <;> decide
  have hk1 := pt_ge1 hv hr0 h
  refine ⟨?_, ?_⟩
  · have := pt_floor hv h0 h
    simp only [hr0, ↓reduceIte] at this
    exact this.le (mul_le_mul_of_nonneg_right ((fl_anti hk).trans' (by unfold fl; norm_num)) hv.le)
  · rcases hr with hr | ⟨hr, hk4⟩
    · rw [mul_comm]; exact pt_hexD hv hr h
    · rw [mul_comm]
      exact (pt_hexA hv h0 hr hk4 h).weaken (by have := d6_pos; positivity)
        (mul_le_mul_of_nonneg_left d6_le_A' hv.le)

end Cls

/-! ### The square with four active marks -/

section Square

variable {Lu Lv : Finset ℕ} {Li : Fin 2 → Finset ℕ}

theorem sq_three (w : Fin 3 → ℝ) : faceConst3 2 * ∏ j, w j = 3 * (w 0 * w 1 * w 2) := by
  rw [faceConst3_two, Fin.prod_univ_three]

/-- The pure types of a square, read on the lists. -/
theorem sq_pt {G : Fin 3 → ℕ → ℕ → ℝ} {w : Fin 3 → ℝ} {τ : Fin 3 → ℕ} {ρ : Fin 3 → Fin 3}
    (hpt : ∀ j, PT (τ j) (ρ j) (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (G j)
      (w j)) :
    PT (τ 0) (ρ 0) Lu (Li 0) (G 0) (w 0) ∧ PT (τ 1) (ρ 1) (Li 0) (Li 1) (G 1) (w 1) ∧
      PT (τ 2) (ρ 2) (Li 1) Lv (G 2) (w 2) := by
  obtain ⟨l0, l1, l2, l3, l4, l5⟩ := pathList_two Lu Lv Li
  have h0 := hpt 0; have h1 := hpt 1; have h2 := hpt 2
  rw [l0, l1] at h0; rw [l2, l3] at h1; rw [l4, l5] at h2
  exact ⟨h0, h1, h2⟩

/-- **The square with four active marks on at most two path edges.** -/
theorem sq_five_two (hLu : Lu.card = 3) (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3)
    (G : Fin 3 → ℕ → ℕ → ℝ) (hG0 : ∀ j c d, 0 ≤ G j c d) (w : Fin 3 → ℝ) (hw : ∀ j, 0 < w j)
    (τ : Fin 3 → ℕ) (ρ : Fin 3 → Fin 3)
    (hpt : ∀ j, PT (τ j) (ρ j) (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (G j)
      (w j)) (ha : ∑ j, actM τ ρ j = 4) (hz : ∃ j, ρ j = 0)
    (h2 : ∃ j₁ j₂, j₁ ≠ j₂ ∧ ρ j₁ ≠ 0 ∧ ρ j₂ ≠ 0) :
    InBall Lu Lv (faceSum Li (fun _ _ => 1) G) (faceConst3 2 * ∏ j, w j) := by
  rw [sq_three]
  obtain ⟨p0, p1, p2⟩ := sq_pt hpt
  obtain ⟨a, ea⟩ : ∃ a, actM τ ρ 0 = a := ⟨_, rfl⟩
  obtain ⟨b, eb⟩ : ∃ b, actM τ ρ 1 = b := ⟨_, rfl⟩
  obtain ⟨c, ec⟩ : ∃ c, actM τ ρ 2 = c := ⟨_, rfl⟩
  have hs : a + b + c = 4 := by
    rw [← ea, ← eb, ← ec, ← Fin.sum_univ_three (f := actM τ ρ)]; exact ha
  have hzero : a = 0 ∨ b = 0 ∨ c = 0 := by
    obtain ⟨j, hj⟩ := hz
    fin_cases j
    · exact Or.inl (ea ▸ actM_inact hj)
    · exact Or.inr (Or.inl (eb ▸ actM_inact hj))
    · exact Or.inr (Or.inr (ec ▸ actM_inact hj))
  have hpos : ∀ j, ρ j ≠ 0 → 1 ≤ actM τ ρ j := fun j hj => by
    rw [actM_act hj]; exact pt_ge1 (hw j) hj (hpt j)
  have htwo : (1 ≤ a ∧ 1 ≤ b) ∨ (1 ≤ a ∧ 1 ≤ c) ∨ (1 ≤ b ∧ 1 ≤ c) := by
    obtain ⟨j₁, j₂, h12, h1, h2⟩ := h2
    have q1 := hpos j₁ h1; have q2 := hpos j₂ h2
    fin_cases j₁ <;> fin_cases j₂ <;> simp_all <;> omega
  unfold actM at ea eb ec
  have w0 := hw 0; have w1 := hw 1; have w2 := hw 2
  rcases (show a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 by omega) with rfl | rfl | rfl | rfl <;>
  rcases (show b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 by omega) with rfl | rfl | rfl | rfl <;>
  rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega) with rfl | rfl | rfl | rfl
  all_goals first
    | omega
    | exact sq_L31a_ball hLu hLv hLi hG0 hw (clsABf p0 ea w0) (clsZ p1 eb w1) (cls0 p2 ec w2)
    | exact sq_L31b_ball hLu hLv hLi hG0 hw (clsZ p0 ea w0) (clsABf p1 eb w1) (cls0 p2 ec w2)
    | exact sq_L31c_ball hLu hLv hLi hG0 hw (clsABf p0 ea w0) (cls0 p1 eb w1) (clsZ p2 ec w2)
    | exact sq_L31a_ball_rev hLu hLv hLi hG0 hw (cls0 p0 ea w0) (clsZ p1 eb w1) (clsABf p2 ec w2)
    | exact sq_L31b_ball_rev hLu hLv hLi hG0 hw (cls0 p0 ea w0) (clsABf p1 eb w1) (clsZ p2 ec w2)
    | exact sq_L31c_ball_rev hLu hLv hLi hG0 hw (clsZ p0 ea w0) (cls0 p1 eb w1) (clsABf p2 ec w2)
    | exact sq_L22a_ball hLu hLv hLi hG0 hw (clsW p0 ea w0) (clsW p1 eb w1) (cls0 p2 ec w2)
    | exact sq_L22a_ball_rev hLu hLv hLi hG0 hw (cls0 p0 ea w0) (clsW p1 eb w1) (clsW p2 ec w2)
    | exact sq_L22b_ball hLu hLv hLi hG0 hw (clsW p0 ea w0) (cls0 p1 eb w1) (clsW p2 ec w2)

/-- **The cap `(2|1|1)`.** -/
theorem sq_five_cap (hLu : Lu.card = 3) (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3)
    (G : Fin 3 → ℕ → ℕ → ℝ) (hG0 : ∀ j c d, 0 ≤ G j c d) (w : Fin 3 → ℝ) (hw : ∀ j, 0 < w j)
    (τ : Fin 3 → ℕ) (ρ : Fin 3 → Fin 3)
    (hpt : ∀ j, PT (τ j) (ρ j) (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (G j)
      (w j)) (ha : ∑ j, actM τ ρ j = 4) (hall : ∀ j, ρ j ≠ 0) :
    InBall Lu Lv (faceSum Li (fun _ _ => 1) G) (faceConst3 2 * ∏ j, w j) := by
  have hfl := term_floor hLi G hG0 w hw τ ρ hpt (by norm_num)
  have ht : tmarks 2 τ ρ = 5 := by unfold tmarks; simp [ha]
  rw [ht] at hfl
  have hFn := faceSum_nonneg Li (fun _ _ => 1) G (fun _ _ _ => zero_le_one) hG0
  have hN : 0 < faceConst3 2 * ∏ j, w j :=
    mul_pos (faceConst3_pos 2) (Finset.prod_pos fun j _ => hw j)
  have h2 : ∀ j, ρ j ≠ 0 → τ j ≤ 2 := fun j hj => by
    have hsum : ∑ i, actM τ ρ i = actM τ ρ 0 + actM τ ρ 1 + actM τ ρ 2 := Fin.sum_univ_three _
    have q0 := pt_ge1 (hw 0) (hall 0) (hpt 0)
    have q1 := pt_ge1 (hw 1) (hall 1) (hpt 1)
    have q2 := pt_ge1 (hw 2) (hall 2) (hpt 2)
    rw [actM_act (hall 0), actM_act (hall 1), actM_act (hall 2)] at hsum
    fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> omega
  have hbij := face_bijQ le_rfl hLu hLv hLi G hG0 w hw τ ρ hpt h2
  have hcard : (univ.filter fun j => ρ j ≠ 0).card = 3 := by
    rw [Finset.filter_true_of_mem fun j _ => hall j]; rfl
  rw [hcard, ha] at hbij
  have hQ : (7 / 5 : ℝ) ≤ capA ^ 3 * capB ^ 4 := by unfold capA capB; norm_num
  exact cap_ball (l := fl 5) (Q := 7 / 5) hN (fl_pos 5) (fl_le_one 5) (by norm_num)
    (by unfold fl; norm_num) hFn hfl (hbij.weakenQ hN.le hQ)

end Square

/-! ### Five marks -/

section Five

variable {m : ℕ} {Lu Lv : Finset ℕ} {Li : Fin m → Finset ℕ}

/-- **An even face with four active marks is in the ball class** (with the floor `(2/3)⁵`). -/
theorem term_even5 (hm : Even m) (hm2 : 2 ≤ m) (hLu : Lu.card = 3) (hLv : Lv.card = 3)
    (hLi : ∀ j, (Li j).card = 3) (G : Fin (m + 1) → ℕ → ℕ → ℝ) (hG0 : ∀ j c d, 0 ≤ G j c d)
    (w : Fin (m + 1) → ℝ) (hw : ∀ j, 0 < w j) (τ : Fin (m + 1) → ℕ) (ρ : Fin (m + 1) → Fin 3)
    (hpt : ∀ j, PT (τ j) (ρ j) (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (G j)
      (w j)) (ha : ∑ j, actM τ ρ j = 4) :
    Kc15 5 Lu Lv (faceSum Li (fun _ _ => 1) G) (faceConst3 m * ∏ j, w j) := by
  have hm1 : 1 ≤ m := by omega
  have hfl := term_floor hLi G hG0 w hw τ ρ hpt hm1
  have ht : tmarks m τ ρ = 5 := by unfold tmarks; simp [hm, ha]
  rw [ht] at hfl
  have hFn := faceSum_nonneg Li (fun _ _ => 1) G (fun _ _ _ => zero_le_one) hG0
  have hP : 0 < ∏ j, w j := Finset.prod_pos fun j _ => hw j
  have hN : 0 < faceConst3 m * ∏ j, w j := mul_pos (faceConst3_pos m) hP
  have hτa : ∀ j, ρ j ≠ 0 → τ j ≤ 4 := fun j hj => by
    have := actM_le_sum (τ := τ) (ρ := ρ) j; rw [actM_act hj] at this; omega
  refine kc15_of_PA (by norm_num) hN.le hFn ⟨?_, hfl⟩
  rcases one_or_two ρ (exists_active (τ := τ) (by omega)) with
    ⟨j₀, hj₀, hrest⟩ | ⟨j₁, j₂, h12, h1, h2⟩
  · have hr1 := pt_one (hw j₀) hj₀ (by have := hτa j₀ hj₀; omega) (hpt j₀)
    have hB := pt_ball (hw j₀) (by rw [hr1]; decide) (hpt j₀)
    have := one_active hLu hLv hLi G hG0 w hw τ ρ hpt hrest one_pos (by rwa [mul_one])
    rwa [mul_one] at this
  -- at least two active sides: each carries at most three marks
  have h3 : ∀ j, ρ j ≠ 0 → τ j ≤ 3 := fun j hj => by
    obtain ⟨j', hne, hj'0⟩ : ∃ j', j' ≠ j ∧ ρ j' ≠ 0 := by
      by_cases e : j = j₁
      · exact ⟨j₂, fun h => h12 (e ▸ h.symm), h2⟩
      · exact ⟨j₁, fun h => e h.symm, h1⟩
    have := actM_two (τ := τ) (ρ := ρ) hne
    rw [actM_act hj'0, actM_act hj] at this
    have := pt_ge1 (hw j') hj'0 (hpt j')
    omega
  rcases Nat.lt_or_ge m 4 with hm4 | hm4
  · obtain rfl : m = 2 := by obtain ⟨k, hk⟩ := hm; omega
    by_cases hall : ∀ j, ρ j ≠ 0
    · exact sq_five_cap hLu hLv hLi G hG0 w hw τ ρ hpt ha hall
    · push Not at hall
      exact sq_five_two hLu hLv hLi G hG0 w hw τ ρ hpt ha hall ⟨j₁, j₂, h12, h1, h2⟩
  · have key := long_ball hm hm4 hLu hLv hLi G hG0 w
      (fun j => if ρ j = 0 then 1 else 17 / 16) hw (fun j => by split_ifs <;> norm_num)
      fun j => by
        by_cases hj : ρ j = 0
        · simp only [hj, ↓reduceIte, mul_one]; exact pt_ball (hw j) (by rw [hj]; decide) (hpt j)
        · simp only [hj, ↓reduceIte]
          exact pt_ballA (hw j) (pt_one (hw j) hj (by have := h3 j hj; omega) (hpt j))
            (h3 j hj) (hpt j)
    refine key.weaken hN.le ?_
    have h2s := prod_scale_two h12 (fun j => if ρ j = 0 then (1 : ℝ) else 17 / 16)
      (fun j => by split_ifs <;> norm_num)
    simp only [h1, h2, ↓reduceIte] at h2s
    have := mul_le_mul_of_nonneg_left h2s (show (0 : ℝ) ≤ 16 / 17 by norm_num)
    have := mul_le_mul_of_nonneg_left this hN.le
    nlinarith

end Five

end Outerplanar.F15
