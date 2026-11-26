/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.FifteenTerm

/-!
# Even faces with two or three active marks, with floors

The terms of an even face whose active sides carry two or three marks in all, with the floors of
Lemma F (`term_floor`): the three-mark alternative `Q3f` (`term_even3`) and the four-mark
alternative `Q4f` (`term_even4`). The arguments are those of the eleven-face note
(`ai_research_notes/OUTERPLANAR_ELEVEN_AND_CENTRAL_SQUARE_2026-11-23.md`, formalized in
`Outerplanar/MarkThreeFour.lean` and `Outerplanar/MarkSquare.lean`), applied term by term so that
every alternative keeps its floor:

* one active side: one-load closure (`ball_one`) with the gain `A` of its table;
* two single marks: `p3_square_two` at squares, the ball design `ballEvenSix` at longer faces;
* at least two active sides carrying three marks: the cap `p4_cap`.

Also the helpers used by the five- to seven-mark faces: `one_active`, `long_ball`, `side_bij`,
`face_bijQ` (the bijection surplus of a face, `a^s b^t`).

Formalized by Claude (milestone M5 of `ai_research_notes/OUTERPLANAR_13_15_LEAN_PLAN.md`).
-/

namespace Outerplanar.F15

open Finset Outerplanar

section Even

variable {m : ℕ} {Lu Lv : Finset ℕ} {Li : Fin m → Finset ℕ}

/-- Exactly one active side, or at least two. -/
theorem one_or_two {n : ℕ} (ρ : Fin n → Fin 3) (h : ∃ j, ρ j ≠ 0) :
    (∃ j₀, ρ j₀ ≠ 0 ∧ ∀ j, j ≠ j₀ → ρ j = 0) ∨ ∃ j₁ j₂, j₁ ≠ j₂ ∧ ρ j₁ ≠ 0 ∧ ρ j₂ ≠ 0 := by
  by_cases h2 : ∃ j₁ j₂, j₁ ≠ j₂ ∧ ρ j₁ ≠ 0 ∧ ρ j₂ ≠ 0
  · exact Or.inr h2
  · push Not at h2
    obtain ⟨j₀, hj₀⟩ := h
    exact Or.inl ⟨j₀, hj₀, fun j hj => h2 j₀ j (Ne.symm hj) hj₀⟩

theorem exists_active {n : ℕ} {τ : Fin n → ℕ} {ρ : Fin n → Fin 3} (h : 1 ≤ ∑ j, actM τ ρ j) :
    ∃ j, ρ j ≠ 0 := by
  by_contra hc; push Not at hc
  have : ∑ i, actM τ ρ i = 0 := Finset.sum_eq_zero fun i _ => actM_inact (hc i)
  omega

theorem actM_single {n : ℕ} {τ : Fin n → ℕ} {ρ : Fin n → Fin 3} {j₀ : Fin n} (hj₀ : ρ j₀ ≠ 0)
    (hrest : ∀ j, j ≠ j₀ → ρ j = 0) : ∑ j, actM τ ρ j = τ j₀ := by
  rw [Finset.sum_eq_single j₀ (fun j _ hj => actM_inact (hrest j hj))
    (fun h => (h (mem_univ _)).elim), actM_act hj₀]

/-- **One active side**: one-load closure. -/
theorem one_active (hLu : Lu.card = 3) (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3)
    (G : Fin (m + 1) → ℕ → ℕ → ℝ) (hG0 : ∀ j c d, 0 ≤ G j c d) (w : Fin (m + 1) → ℝ)
    (hw : ∀ j, 0 < w j) (τ : Fin (m + 1) → ℕ) (ρ : Fin (m + 1) → Fin 3)
    (hpt : ∀ j, PT (τ j) (ρ j) (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (G j)
      (w j)) {j₀ : Fin (m + 1)} (hrest : ∀ j, j ≠ j₀ → ρ j = 0) {g : ℝ} (hg : 0 < g)
    (hB : InBall (pathList Lu Lv Li j₀.castSucc) (pathList Lu Lv Li j₀.succ) (G j₀) (w j₀ * g)) :
    InBall Lu Lv (faceSum Li (fun _ _ => 1) G) (faceConst3 m * (∏ j, w j) * g) :=
  ball_one (j₀ := j₀) hLu hLv hLi hG0 hw hg hB fun j hj => (hpt j).1 (hrest j hj)

/-- **The ball design at faces of length at least six.** -/
theorem long_ball (hm : Even m) (hm4 : 4 ≤ m) (hLu : Lu.card = 3) (hLv : Lv.card = 3)
    (hLi : ∀ j, (Li j).card = 3) (G : Fin (m + 1) → ℕ → ℕ → ℝ) (hG0 : ∀ j c d, 0 ≤ G j c d)
    (w s : Fin (m + 1) → ℝ) (hw : ∀ j, 0 < w j) (hs : ∀ j, 0 < s j)
    (hB : ∀ j, InBall (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (G j)
      (w j * s j)) :
    InBall Lu Lv (faceSum Li (fun _ _ => 1) G)
      (faceConst3 m * (∏ j, w j) * (16 / 17 * ∏ j, s j)) := by
  have key := ballEvenSix m hm hm4 Lu Lv Li hLu hLv hLi G hG0 (fun j => w j * s j)
    (fun j => mul_pos (hw j) (hs j)) hB
  rw [Finset.prod_mul_distrib] at key
  convert key using 1
  ring

/-- Two scales of an index set, at two distinct indices. -/
theorem prod_scale_two {n : ℕ} {j₁ j₂ : Fin n} (h12 : j₁ ≠ j₂) (s : Fin n → ℝ)
    (hs : ∀ j, 1 ≤ s j) : s j₁ * s j₂ ≤ ∏ j, s j := by
  rw [← Finset.mul_prod_erase univ _ (mem_univ j₁),
    ← Finset.mul_prod_erase (univ.erase j₁) _ (mem_erase.mpr ⟨Ne.symm h12, mem_univ j₂⟩)]
  have h1 : 1 ≤ ∏ i ∈ (univ.erase j₁).erase j₂, s i := Finset.one_le_prod₀ fun i _ => hs i
  have h0 : 0 ≤ s j₁ * s j₂ := by nlinarith [hs j₁, hs j₂]
  have := mul_le_mul_of_nonneg_left h1 h0
  nlinarith [mul_assoc (s j₁) (s j₂) (∏ i ∈ (univ.erase j₁).erase j₂, s i)]

/-- The cap constants: `Q = capA · capB^k` for a side of `k ≤ 2` marks. -/
noncomputable def capA : ℝ := 1024 / 729 * (16 / 17)

noncomputable def capB : ℝ := 17 / 16 * (27 / 32)

/-- The bijection surplus of an active side with at most two marks. -/
theorem side_bij {S T : Finset ℕ} {Y : ℕ → ℕ → ℝ} {v : ℝ} {k : ℕ} {r : Fin 3} (hv : 0 < v)
    (hk : r = 0 ∨ k ≤ 2) (h : PT k r S T Y v) :
    BijGe S T Y v ((if r = 0 then 1 else capA) * capB ^ (if r = 0 then 0 else k)) := by
  by_cases hr : r = 0
  · simpa [hr] using (h.1 hr).bijGe hv.le
  have hk2 : k ≤ 2 := hk.resolve_left hr
  have hk1 := pt_ge1 hv hr h
  have hr1 := pt_one hv hr (by omega) h
  have h1 := h.2.1 hr1
  simp only [hr, ↓reduceIte]
  interval_cases k
  · have e : capA * capB ^ 1 = 32 / 27 := by unfold capA capB; norm_num
    rw [e]; exact h1.2.1
  · have e : capA * capB ^ 2 = 17 / 16 := by unfold capA capB; norm_num
    rw [e]; exact h1.2.1

/-- **The bijection surplus of a face whose active sides carry at most two marks each.** -/
theorem face_bijQ (hm2 : 2 ≤ m) (hLu : Lu.card = 3) (hLv : Lv.card = 3)
    (hLi : ∀ j, (Li j).card = 3) (G : Fin (m + 1) → ℕ → ℕ → ℝ) (hG0 : ∀ j c d, 0 ≤ G j c d)
    (w : Fin (m + 1) → ℝ) (hw : ∀ j, 0 < w j) (τ : Fin (m + 1) → ℕ) (ρ : Fin (m + 1) → Fin 3)
    (hpt : ∀ j, PT (τ j) (ρ j) (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (G j)
      (w j)) (h2 : ∀ j, ρ j ≠ 0 → τ j ≤ 2) :
    BijGe Lu Lv (faceSum Li (fun _ _ => 1) G) (faceConst3 m * ∏ j, w j)
      (capA ^ (univ.filter fun j => ρ j ≠ 0).card * capB ^ (∑ j, actM τ ρ j)) := by
  have hQpos : ∀ j, 0 < (if ρ j = 0 then 1 else capA) * capB ^ (actM τ ρ j) := fun j => by
    have : 0 < (if ρ j = 0 then (1 : ℝ) else capA) := by split_ifs <;> norm_num [capA]
    have : 0 < capB := by norm_num [capB]
    positivity
  have hpos : ∀ j, ∀ c ∈ pathList Lu Lv Li j.castSucc, ∀ d ∈ pathList Lu Lv Li j.succ, c ≠ d →
      0 < G j c d := fun j c hc d hd hcd =>
    lt_of_lt_of_le (mul_pos (fl_pos _) (hw j)) (pt_floor (hw j) (hG0 j) (hpt j) c hc d hd hcd)
  have h := bijGe_face hm2 Lu Lv Li hLu hLv hLi G hG0 w _ hw hQpos hpos fun j => by
    have := side_bij (hw j) (by
      by_cases hj : ρ j = 0
      · exact Or.inl hj
      · exact Or.inr (h2 j hj)) (hpt j)
    exact this
  convert h using 2
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_ite, Finset.prod_const_one,
    one_mul, Finset.prod_const]

theorem card_active_two {n : ℕ} {ρ : Fin n → Fin 3} {j₁ j₂ : Fin n} (h12 : j₁ ≠ j₂)
    (h1 : ρ j₁ ≠ 0) (h2 : ρ j₂ ≠ 0) : 2 ≤ (univ.filter fun j => ρ j ≠ 0).card := by
  have : ({j₁, j₂} : Finset (Fin n)) ⊆ univ.filter fun j => ρ j ≠ 0 := by
    intro j hj
    rcases mem_insert.mp hj with rfl | hj
    · exact mem_filter.mpr ⟨mem_univ _, h1⟩
    · rw [mem_singleton.mp hj]; exact mem_filter.mpr ⟨mem_univ _, h2⟩
  have := card_le_card this
  rwa [card_pair h12] at this

/-- **An even face with two active marks**: `Q3f`. -/
theorem term_even3 (hm : Even m) (hm2 : 2 ≤ m) (hLu : Lu.card = 3) (hLv : Lv.card = 3)
    (hLi : ∀ j, (Li j).card = 3) (G : Fin (m + 1) → ℕ → ℕ → ℝ) (hG0 : ∀ j c d, 0 ≤ G j c d)
    (w : Fin (m + 1) → ℝ) (hw : ∀ j, 0 < w j) (τ : Fin (m + 1) → ℕ) (ρ : Fin (m + 1) → Fin 3)
    (hpt : ∀ j, PT (τ j) (ρ j) (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (G j)
      (w j)) (ha : ∑ j, actM τ ρ j = 2) :
    Kc15 3 Lu Lv (faceSum Li (fun _ _ => 1) G) (faceConst3 m * ∏ j, w j) := by
  have hm1 : 1 ≤ m := by omega
  have hfl := term_floor hLi G hG0 w hw τ ρ hpt hm1
  have ht : tmarks m τ ρ = 3 := by unfold tmarks; simp [hm, ha]
  rw [ht] at hfl
  have hFn := faceSum_nonneg Li (fun _ _ => 1) G (fun _ _ _ => zero_le_one) hG0
  have hP : 0 < ∏ j, w j := Finset.prod_pos fun j _ => hw j
  have hN : 0 < faceConst3 m * ∏ j, w j := mul_pos (faceConst3_pos m) hP
  have hτa : ∀ j, ρ j ≠ 0 → τ j ≤ 2 := fun j hj => by
    have := actM_le_sum (τ := τ) (ρ := ρ) j; rw [actM_act hj] at this; omega
  refine kc15_of_PA (by norm_num) hN.le hFn ⟨?_, hfl⟩
  show InBall _ _ _ ((faceConst3 m * ∏ j, w j) * (17 / 16))
  rcases one_or_two ρ (exists_active (τ := τ) (by omega)) with
    ⟨j₀, hj₀, hrest⟩ | ⟨j₁, j₂, h12, h1, h2⟩
  · have hB := pt_ballA (hw j₀) (pt_one (hw j₀) hj₀ (by have := hτa j₀ hj₀; omega) (hpt j₀))
      (by have := hτa j₀ hj₀; omega) (hpt j₀)
    exact one_active hLu hLv hLi G hG0 w hw τ ρ hpt hrest (by norm_num) hB
  · -- two single marks
    have hsum := actM_two (τ := τ) (ρ := ρ) h12
    rw [actM_act h1, actM_act h2] at hsum
    have hge1 := pt_ge1 (hw j₁) h1 (hpt j₁)
    have hge2 := pt_ge1 (hw j₂) h2 (hpt j₂)
    have e1 : τ j₁ = 1 := by omega
    have e2 : τ j₂ = 1 := by omega
    have hrest : ∀ j, j ≠ j₁ → j ≠ j₂ → ρ j = 0 := fun j hj1 hj2 => by
      by_contra hj
      have s3 : actM τ ρ j₁ + actM τ ρ j₂ + actM τ ρ j ≤ ∑ i, actM τ ρ i := by
        have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun i => actM τ ρ i)
          (subset_univ ({j₁, j₂, j} : Finset (Fin (m + 1)))) fun _ _ _ => Nat.zero_le _
        rw [Finset.sum_insert (by simp [h12, Ne.symm hj1]), Finset.sum_pair (Ne.symm hj2)] at this
        omega
      rw [actM_act h1, actM_act h2, actM_act hj] at s3
      have := pt_ge1 (hw j) hj (hpt j)
      omega
    have hP1 : ∀ j, ρ j ≠ 0 → P1 (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (G j)
        (w j) := fun j hj => by
      have hr := pt_one (hw j) hj (by have := hτa j hj; omega) (hpt j)
      have h := (hpt j).2.1 hr
      have : τ j = 1 := by
        by_cases e : j = j₁
        · rw [e]; exact e1
        · by_cases e' : j = j₂
          · rw [e']; exact e2
          · exact absurd (hrest j e e') hj
      rw [this] at h
      exact h
    rcases Nat.lt_or_ge m 4 with hm4 | hm4
    · obtain rfl : m = 2 := by obtain ⟨k, hk⟩ := hm; omega
      exact p3_square_two Lu Lv Li hLu hLv hLi G hG0 w hw h12 (hP1 j₁ h1) (hP1 j₂ h2)
        fun j hj1 hj2 => (hpt j).1 (hrest j hj1 hj2)
    · have key := long_ball hm hm4 hLu hLv hLi G hG0 w
        (fun j => if ρ j = 0 then 1 else 17 / 16) hw (fun j => by split_ifs <;> norm_num)
        fun j => by
          by_cases hj : ρ j = 0
          · simp only [hj, ↓reduceIte, mul_one]; exact pt_ball (hw j) (by rw [hj]; decide) (hpt j)
          · simp only [hj, ↓reduceIte]
            exact pt_ballA (hw j) (pt_one (hw j) hj (by have := hτa j hj; omega) (hpt j))
              (by have := hτa j hj; omega) (hpt j)
      refine key.weaken (by positivity) ?_
      have h2s := prod_scale_two h12 (fun j => if ρ j = 0 then (1 : ℝ) else 17 / 16)
        (fun j => by split_ifs <;> norm_num)
      simp only [h1, h2, ↓reduceIte] at h2s
      have := mul_le_mul_of_nonneg_left h2s (show (0 : ℝ) ≤ 16 / 17 by norm_num)
      have := mul_le_mul_of_nonneg_left this hN.le
      nlinarith

/-- **An even face with three active marks**: `Q4f`. -/
theorem term_even4 (hm : Even m) (hm2 : 2 ≤ m) (hLu : Lu.card = 3) (hLv : Lv.card = 3)
    (hLi : ∀ j, (Li j).card = 3) (G : Fin (m + 1) → ℕ → ℕ → ℝ) (hG0 : ∀ j c d, 0 ≤ G j c d)
    (w : Fin (m + 1) → ℝ) (hw : ∀ j, 0 < w j) (τ : Fin (m + 1) → ℕ) (ρ : Fin (m + 1) → Fin 3)
    (hpt : ∀ j, PT (τ j) (ρ j) (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (G j)
      (w j)) (ha : ∑ j, actM τ ρ j = 3) :
    Kc15 4 Lu Lv (faceSum Li (fun _ _ => 1) G) (faceConst3 m * ∏ j, w j) := by
  have hm1 : 1 ≤ m := by omega
  have hfl := term_floor hLi G hG0 w hw τ ρ hpt hm1
  have ht : tmarks m τ ρ = 4 := by unfold tmarks; simp [hm, ha]
  rw [ht] at hfl
  have hFn := faceSum_nonneg Li (fun _ _ => 1) G (fun _ _ _ => zero_le_one) hG0
  have hP : 0 < ∏ j, w j := Finset.prod_pos fun j _ => hw j
  have hN : 0 < faceConst3 m * ∏ j, w j := mul_pos (faceConst3_pos m) hP
  have hτa : ∀ j, ρ j ≠ 0 → τ j ≤ 3 := fun j hj => by
    have := actM_le_sum (τ := τ) (ρ := ρ) j; rw [actM_act hj] at this; omega
  refine kc15_of_PA (by norm_num) hN.le hFn ⟨?_, hfl⟩
  rcases one_or_two ρ (exists_active (τ := τ) (by omega)) with
    ⟨j₀, hj₀, hrest⟩ | ⟨j₁, j₂, h12, h1, h2⟩
  · have hB := pt_ballA (hw j₀) (pt_one (hw j₀) hj₀ (by have := hτa j₀ hj₀; omega) (hpt j₀))
      (by have := hτa j₀ hj₀; omega) (hpt j₀)
    exact p3_p4 hN.le hFn (one_active hLu hLv hLi G hG0 w hw τ ρ hpt hrest (by norm_num) hB)
  · -- at least two active sides, each with at most two marks: the cap
    have h2' : ∀ j, ρ j ≠ 0 → τ j ≤ 2 := fun j hj => by
      by_contra hc; push Not at hc
      obtain ⟨j', hne, hj'0⟩ : ∃ j', j' ≠ j ∧ ρ j' ≠ 0 := by
        by_cases e : j = j₁
        · exact ⟨j₂, fun h => h12 (e ▸ h.symm), h2⟩
        · exact ⟨j₁, fun h => e h.symm, h1⟩
      have := actM_two (τ := τ) (ρ := ρ) hne
      rw [actM_act hj'0, actM_act hj] at this
      have := pt_ge1 (hw j') hj'0 (hpt j')
      omega
    have hbij := face_bijQ hm2 hLu hLv hLi G hG0 w hw τ ρ hpt h2'
    rw [ha] at hbij
    have hcard := card_active_two h12 h1 h2
    have hQ : 34 / 27 ≤ capA ^ (univ.filter fun j => ρ j ≠ 0).card * capB ^ 3 := by
      have ka : capA ^ 2 ≤ capA ^ (univ.filter fun j => ρ j ≠ 0).card :=
        pow_le_pow_right₀ (by unfold capA; norm_num) hcard
      have kab : (34 / 27 : ℝ) = capA ^ 2 * capB ^ 3 := by unfold capA capB; norm_num
      rw [kab]
      exact mul_le_mul_of_nonneg_right ka (by unfold capB; positivity)
    refine ⟨cap_ball (l := 16 / 81) (Q := 34 / 27) hN (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hFn (hfl.le (by unfold fl; norm_num)) (hbij.weakenQ hN.le hQ), ?_⟩
    exact (hbij.weakenQ (Q' := (17 / 16) ^ 3) hN.le (le_trans (by norm_num) hQ)).hex
      (by norm_num) hN.le hFn

end Even

end Outerplanar.F15
