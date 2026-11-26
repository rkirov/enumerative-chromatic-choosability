/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.FiveB
import Outerplanar.Sq15RunF41

/-!
# Six and seven marks, and the face rule of the fifteen-face theorem

Research note `ai_research_notes/OUTERPLANAR_FIFTEEN_EVEN_2026-11-25.md`, steps 3 and 4 (and
`ai_research_notes/outerplanar/fivemarks/results.md` §3):

* **six marks** (`term_even6`): an even face whose active sides carry five marks is in
  `conv(B, A^{4/3} H)`: one side by one-load closure, longer faces by the ball design, squares by
  `[B, M, M]` (`A κ_A = A^{4/3}`) except `(4|1)`, which the note proves by the two-distinguished
  law at `K_sq = 43/42`; here it is the kernel-checked run **F41** (`[BAH_f, Z, 1] → A^{4/3} H`, all
  six placements, `Outerplanar/Sq15RunF41.lean`), since the law is in Lean only at `K = 59/56`;
* **seven marks** (`term_even7`): six active marks give `conv(B, D₆ H)`: one side by one-load
  closure or, for the hexagon part of six marks, the two-distinguished law (`A^{4/3}/K = D₆`);
  squares by `[B, M, M]`, `(4|2)` by `[H, M, M]` (`A κ_A / K = D₆`), `(3|3)` by **N1** on adjacent
  sides and `[B, 1, B]` on opposite ones;
* **`markRule15`** and **`markRule15_sound`** — the face rule through seven marks.

Formalized by Claude (milestone M5 of `ai_research_notes/OUTERPLANAR_13_15_LEAN_PLAN.md`).
-/

namespace Outerplanar.F15

open Finset Outerplanar Outerplanar.SqMulti

/-! ### Square laws on pure types -/

section Square

variable {Lu Lv : Finset ℕ} {Li : Fin 2 → Finset ℕ}

theorem pt_bij15 {S T : Finset ℕ} {Y : ℕ → ℕ → ℝ} {v : ℝ} {k : ℕ} {r : Fin 3} (hv : 0 < v)
    (hl : r = 0 ∨ k ≤ 2) (h : PT k r S T Y v) : BijGe S T Y (v * msc k r) 1 := by
  by_cases hr : r = 0
  · simpa [msc, hr] using (h.1 hr).bijGe hv.le
  have hk := hl.resolve_left hr
  have hr1 := pt_one hv hr (by omega) h
  have hk1 := pt_ge1 hv hr h
  have h1 := h.2.1 hr1
  subst hr1
  interval_cases k
  · have := (bijGe_cube (by norm_num : (0 : ℝ) ≤ 32 / 27)).mp h1.2.1
    simpa [msc, κq] using this
  · have := (bijGe_cube (by norm_num : (0 : ℝ) ≤ 17 / 16)).mp h1.2.1
    simpa [msc, κA] using this

/-- **`[B, M, M]` on a term**: the side `jB` in `B` with the scale `b`, the others in `M`. -/
theorem sq_bmm15 (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3)
    (G : Fin 3 → ℕ → ℕ → ℝ) (hG0 : ∀ j c d, 0 ≤ G j c d) (w : Fin 3 → ℝ) (hw : ∀ j, 0 < w j)
    (τ : Fin 3 → ℕ) (ρ : Fin 3 → Fin 3)
    (hpt : ∀ j, PT (τ j) (ρ j) (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (G j)
      (w j)) (jB : Fin 3) {b : ℝ} (hb : 0 < b)
    (hB : InBall (pathList Lu Lv Li jB.castSucc) (pathList Lu Lv Li jB.succ) (G jB) (w jB * b))
    (hM : ∀ j, j ≠ jB → ρ j = 0 ∨ τ j ≤ 2) :
    Hex Lu Lv (faceSum Li (fun _ _ => 1) G)
      (faceConst3 2 * (∏ j, w j) * (b * ∏ j, (if j = jB then 1 else msc (τ j) (ρ j)))) := by
  set N : Fin 3 → ℝ := fun j => w j * (if j = jB then b else msc (τ j) (ρ j)) with hN
  have hNpos : ∀ j, 0 < N j := fun j => by
    simp only [hN]; split_ifs
    · exact mul_pos (hw j) hb
    · exact mul_pos (hw j) (msc_pos _ _)
  have key := sqLawB hLv hLi G hG0 N hNpos jB (by simpa [hN] using hB) fun j hj => by
    simpa [hN, hj] using pt_bij15 (hw j) (hM j hj) (hpt j)
  have e : ∏ j, N j = (∏ j, w j) * (b * ∏ j, (if j = jB then 1 else msc (τ j) (ρ j))) := by
    rw [hN, Finset.prod_mul_distrib]
    congr 1
    rw [← prod_ite_scale jB b]
    exact Finset.prod_congr rfl fun j _ => by split_ifs <;> simp
  rwa [e, ← mul_assoc] at key

/-- **`[H, M, M]` on a term**, at the scale `56/59`. -/
theorem sq_hmm15 (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3)
    (G : Fin 3 → ℕ → ℕ → ℝ) (hG0 : ∀ j c d, 0 ≤ G j c d) (w : Fin 3 → ℝ) (hw : ∀ j, 0 < w j)
    (τ : Fin 3 → ℕ) (ρ : Fin 3 → Fin 3)
    (hpt : ∀ j, PT (τ j) (ρ j) (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (G j)
      (w j)) (jH : Fin 3) {b : ℝ} (hb : 0 < b)
    (hH : Hex (pathList Lu Lv Li jH.castSucc) (pathList Lu Lv Li jH.succ) (G jH) (w jH * b))
    (hM : ∀ j, j ≠ jH → ρ j = 0 ∨ τ j ≤ 2) :
    Hex Lu Lv (faceSum Li (fun _ _ => 1) G)
      (faceConst3 2 * (∏ j, w j) *
        (56 / 59 * (b * ∏ j, (if j = jH then 1 else msc (τ j) (ρ j))))) := by
  set N : Fin 3 → ℝ := fun j => w j * (if j = jH then b else msc (τ j) (ρ j)) with hN
  have hNpos : ∀ j, 0 < N j := fun j => by
    simp only [hN]; split_ifs
    · exact mul_pos (hw j) hb
    · exact mul_pos (hw j) (msc_pos _ _)
  have key := sqLawH hLv hLi G hG0 N hNpos jH (by simpa [hN] using hH) fun j hj => by
    simpa [hN, hj] using pt_bij15 (hw j) (hM j hj) (hpt j)
  have e : ∏ j, N j = (∏ j, w j) * (b * ∏ j, (if j = jH then 1 else msc (τ j) (ρ j))) := by
    rw [hN, Finset.prod_mul_distrib]
    congr 1
    rw [← prod_ite_scale jH b]
    exact Finset.prod_congr rfl fun j _ => by split_ifs <;> simp
  rw [e] at key
  convert key using 1
  ring

theorem msc_prod_ge (τ : Fin 3 → ℕ) (ρ : Fin 3 → Fin 3) (jB : Fin 3) :
    1 ≤ ∏ j, (if j = jB then 1 else msc (τ j) (ρ j)) :=
  Finset.one_le_prod₀ fun j _ => by split_ifs; exacts [le_rfl, msc_ge _ _]

/-- Three path edges: given one, the other two. -/
theorem fin3_others (jB : Fin 3) : ∃ j₁ j₂, j₁ ≠ jB ∧ j₂ ≠ jB ∧ j₁ ≠ j₂ ∧
    ∀ j, j = jB ∨ j = j₁ ∨ j = j₂ := by
  fin_cases jB
  · exact ⟨1, 2, by decide, by decide, by decide, by decide⟩
  · exact ⟨0, 2, by decide, by decide, by decide, by decide⟩
  · exact ⟨0, 1, by decide, by decide, by decide, by decide⟩

end Square

/-! ### Six marks -/

section Six

variable {m : ℕ} {Lu Lv : Finset ℕ} {Li : Fin m → Finset ℕ}

/-- The square with five active marks on at least two path edges. -/
theorem sq_six (hLu : Lu.card = 3) (hLv : Lv.card = 3) {Li : Fin 2 → Finset ℕ}
    (hLi : ∀ j, (Li j).card = 3) (G : Fin 3 → ℕ → ℕ → ℝ) (hG0 : ∀ j c d, 0 ≤ G j c d)
    (w : Fin 3 → ℝ) (hw : ∀ j, 0 < w j) (τ : Fin 3 → ℕ) (ρ : Fin 3 → Fin 3)
    (hpt : ∀ j, PT (τ j) (ρ j) (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (G j)
      (w j)) (ha : ∑ j, actM τ ρ j = 5) {j₁ j₂ : Fin 3} (h12 : j₁ ≠ j₂) (h1 : ρ j₁ ≠ 0)
    (h2 : ρ j₂ ≠ 0) :
    Hex Lu Lv (faceSum Li (fun _ _ => 1) G) (faceConst3 2 * (∏ j, w j) * a5) := by
  have hP : 0 < ∏ j, w j := Finset.prod_pos fun j _ => hw j
  have hN : 0 < faceConst3 2 * ∏ j, w j := mul_pos (faceConst3_pos 2) hP
  obtain ⟨jB, hmax, h3B⟩ := actM_max3 τ ρ
  have hBact : ρ jB ≠ 0 := fun h => by rw [actM_inact h] at h3B; omega
  have hτB : 2 ≤ τ jB := by rw [actM_act hBact] at h3B; omega
  obtain ⟨j₁', hj₁', ha₁'⟩ : ∃ j', j' ≠ jB ∧ ρ j' ≠ 0 := by
    by_cases e : jB = j₁
    · exact ⟨j₂, fun h => h12 (e ▸ h.symm), h2⟩
    · exact ⟨j₁, fun h => e h.symm, h1⟩
  have hother := actM_two (τ := τ) (ρ := ρ) (Ne.symm hj₁')
  rw [actM_act hBact, actM_act ha₁'] at hother
  have hge1 := pt_ge1 (hw j₁') ha₁' (hpt j₁')
  have hτB4 : τ jB ≤ 4 := by omega
  have hrB := pt_one (hw jB) hBact (by omega) (hpt jB)
  rcases Nat.lt_or_ge (τ jB) 4 with hB3 | hB4
  · -- `[B, M, M]`, the largest side in `A B`
    have hM : ∀ j, j ≠ jB → ρ j = 0 ∨ τ j ≤ 2 := fun j hj => by
      by_cases hj0 : ρ j = 0
      · exact Or.inl hj0
      · refine Or.inr ?_
        have := actM_two (τ := τ) (ρ := ρ) hj
        have := hmax j
        rw [actM_act hj0, actM_act hBact] at *
        omega
    have key := sq_bmm15 hLv hLi G hG0 w hw τ ρ hpt jB (by norm_num)
      (pt_ballA (hw jB) hrB (by omega) (hpt jB)) hM
    refine key.weaken (by have := a5_pos; positivity) ?_
    have hp := (msc_prod τ ρ jB j₁' hj₁' ha₁').1
    have : a5 ≤ 17 / 16 * ∏ j, (if j = jB then 1 else msc (τ j) (ρ j)) := by
      unfold a5; nlinarith
    exact mul_le_mul_of_nonneg_left this hN.le
  · -- `(4|1)`: the run F41
    have e4 : τ jB = 4 := by omega
    have e1 : τ j₁' = 1 := by omega
    obtain ⟨k₁, k₂, hk₁, hk₂, hk12, hall⟩ := fin3_others jB
    -- the third side is inactive
    have hrest : ∀ j, j ≠ jB → j ≠ j₁' → ρ j = 0 := fun j hj1 hj2 => by
      by_contra hj
      have s3 : actM τ ρ jB + actM τ ρ j₁' + actM τ ρ j ≤ ∑ i, actM τ ρ i := by
        have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun i => actM τ ρ i)
          (subset_univ ({jB, j₁', j} : Finset (Fin 3))) fun _ _ _ => Nat.zero_le _
        rw [Finset.sum_insert (by simp [Ne.symm hj₁', Ne.symm hj1]),
          Finset.sum_pair (Ne.symm hj2)] at this
        omega
      rw [actM_act hBact, actM_act ha₁', actM_act hj] at s3
      have := pt_ge1 (hw j) hj (hpt j)
      omega
    obtain ⟨p0, p1, p2⟩ := sq_pt hpt
    have w0 := hw 0; have w1 := hw 1; have w2 := hw 2
    have hB4' : ∀ j, j = jB → (if ρ j = 0 then 0 else τ j) = 4 := fun j h => by
      subst h; simp [hBact, e4]
    have hZ1' : ∀ j, j = j₁' → (if ρ j = 0 then 0 else τ j) = 1 := fun j h => by
      subst h; simp [ha₁', e1]
    have hD' : ∀ j, j ≠ jB → j ≠ j₁' → (if ρ j = 0 then 0 else τ j) = 0 := fun j h1 h2 => by
      simp [hrest j h1 h2]
    rw [sq_three, show 3 * (w 0 * w 1 * w 2) * a5 = 3 * a5 * (w 0 * w 1 * w 2) by ring]
    fin_cases jB <;> fin_cases j₁' <;> simp at hj₁' ⊢
    · exact sq_F41a_hex hLv hLi hG0 hw (clsBAHf p0 (hB4' 0 rfl) w0 (hG0 0))
        (clsZ p1 (hZ1' 1 rfl) w1) (cls0 p2 (hD' 2 (by decide) (by decide)) w2)
    · exact sq_F41c_hex hLv hLi hG0 hw (clsBAHf p0 (hB4' 0 rfl) w0 (hG0 0))
        (cls0 p1 (hD' 1 (by decide) (by decide)) w1) (clsZ p2 (hZ1' 2 rfl) w2)
    · exact sq_F41b_hex hLv hLi hG0 hw (clsZ p0 (hZ1' 0 rfl) w0)
        (clsBAHf p1 (hB4' 1 rfl) w1 (hG0 1)) (cls0 p2 (hD' 2 (by decide) (by decide)) w2)
    · exact sq_F41b_hex_rev hLu hLi hG0 hw (cls0 p0 (hD' 0 (by decide) (by decide)) w0)
        (clsBAHf p1 (hB4' 1 rfl) w1 (hG0 1)) (clsZ p2 (hZ1' 2 rfl) w2)
    · exact sq_F41c_hex_rev hLu hLi hG0 hw (clsZ p0 (hZ1' 0 rfl) w0)
        (cls0 p1 (hD' 1 (by decide) (by decide)) w1) (clsBAHf p2 (hB4' 2 rfl) w2 (hG0 2))
    · exact sq_F41a_hex_rev hLu hLi hG0 hw (cls0 p0 (hD' 0 (by decide) (by decide)) w0)
        (clsZ p1 (hZ1' 1 rfl) w1) (clsBAHf p2 (hB4' 2 rfl) w2 (hG0 2))

/-- Some active side carries at most three marks, when at least two sides are active. -/
theorem exists_light {n : ℕ} {τ : Fin n → ℕ} {ρ : Fin n → Fin 3} {a : ℕ} (ha : ∑ j, actM τ ρ j = a)
    (ha7 : a ≤ 7) {j₁ j₂ : Fin n} (h12 : j₁ ≠ j₂) (h1 : ρ j₁ ≠ 0) (h2 : ρ j₂ ≠ 0) :
    ∃ j, ρ j ≠ 0 ∧ τ j ≤ 3 := by
  by_contra hc
  push Not at hc
  have := actM_two (τ := τ) (ρ := ρ) h12
  rw [actM_act h1, actM_act h2] at this
  have := hc j₁ h1
  have := hc j₂ h2
  omega

/-- The ball design at longer faces with at least two active sides. -/
theorem long_two (hm : Even m) (hm4 : 4 ≤ m) (hLu : Lu.card = 3) (hLv : Lv.card = 3)
    (hLi : ∀ j, (Li j).card = 3) (G : Fin (m + 1) → ℕ → ℕ → ℝ) (hG0 : ∀ j c d, 0 ≤ G j c d)
    (w : Fin (m + 1) → ℝ) (hw : ∀ j, 0 < w j) (τ : Fin (m + 1) → ℕ) (ρ : Fin (m + 1) → Fin 3)
    (hpt : ∀ j, PT (τ j) (ρ j) (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (G j)
      (w j)) (hB : ∀ j, ρ j ≠ 2) {j₃ : Fin (m + 1)} (hj₃ : ρ j₃ ≠ 0) (h3 : τ j₃ ≤ 3) :
    InBall Lu Lv (faceSum Li (fun _ _ => 1) G) (faceConst3 m * ∏ j, w j) := by
  have key := long_ball hm hm4 hLu hLv hLi G hG0 w (fun j => if j = j₃ then 17 / 16 else 1) hw
    (fun j => by split_ifs <;> norm_num) fun j => by
      by_cases hj : j = j₃
      · subst hj
        simp only [↓reduceIte]
        exact pt_ballA (hw j) (pt_one (hw j) hj₃ (by omega) (hpt j)) h3 (hpt j)
      · simp only [hj, ↓reduceIte, mul_one]; exact pt_ball (hw j) (hB j) (hpt j)
  have e : ∏ j, (if j = j₃ then (17 / 16 : ℝ) else 1) = 17 / 16 := by
    rw [Finset.prod_ite_eq' univ j₃ (fun _ => (17 / 16 : ℝ))]; simp
  rw [e, show (16 / 17 : ℝ) * (17 / 16) = 1 by norm_num, mul_one] at key
  exact key

/-- **Six marks: an even face whose active sides carry five marks.** -/
theorem term_even6 (hm : Even m) (hm2 : 2 ≤ m) (hLu : Lu.card = 3) (hLv : Lv.card = 3)
    (hLi : ∀ j, (Li j).card = 3) (G : Fin (m + 1) → ℕ → ℕ → ℝ) (hG0 : ∀ j c d, 0 ≤ G j c d)
    (w : Fin (m + 1) → ℝ) (hw : ∀ j, 0 < w j) (τ : Fin (m + 1) → ℕ) (ρ : Fin (m + 1) → Fin 3)
    (hpt : ∀ j, PT (τ j) (ρ j) (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (G j)
      (w j)) (ha : ∑ j, actM τ ρ j = 5) :
    Kc15 6 Lu Lv (faceSum Li (fun _ _ => 1) G) (faceConst3 m * ∏ j, w j) := by
  have hm1 : 1 ≤ m := by omega
  have hfl := term_floor hLi G hG0 w hw τ ρ hpt hm1
  have ht : tmarks m τ ρ = 6 := by unfold tmarks; simp [hm, ha]
  rw [ht] at hfl
  have hFn := faceSum_nonneg Li (fun _ _ => 1) G (fun _ _ _ => zero_le_one) hG0
  have hP : 0 < ∏ j, w j := Finset.prod_pos fun j _ => hw j
  have hN : 0 < faceConst3 m * ∏ j, w j := mul_pos (faceConst3_pos m) hP
  have hτa : ∀ j, ρ j ≠ 0 → τ j ≤ 5 := fun j hj => by
    have := actM_le_sum (τ := τ) (ρ := ρ) j; rw [actM_act hj] at this; omega
  have hB2 : ∀ j, ρ j ≠ 2 := fun j hj => by
    have := pt_ge6 (hw j) hj (hpt j)
    have := hτa j (by rw [hj]; decide)
    omega
  rcases one_or_two ρ (exists_active (τ := τ) (by omega)) with
    ⟨j₀, hj₀, hrest⟩ | ⟨j₁, j₂, h12, h1, h2⟩
  · have hB := pt_ball (hw j₀) (hB2 j₀) (hpt j₀)
    have := one_active hLu hLv hLi G hG0 w hw τ ρ hpt hrest one_pos (by rwa [mul_one])
    rw [mul_one] at this
    exact kc15_of_PA (by norm_num) hN.le hFn ⟨this, hfl⟩
  rcases Nat.lt_or_ge m 4 with hm4 | hm4
  · obtain rfl : m = 2 := by obtain ⟨k, hk⟩ := hm; omega
    exact kc15_of_PB (by norm_num) hN.le hFn
      ⟨sq_six hLu hLv hLi G hG0 w hw τ ρ hpt ha h12 h1 h2, hfl⟩
  · obtain ⟨j₃, hj₃, h3⟩ := exists_light ha (by norm_num) h12 h1 h2
    exact kc15_of_PA (by norm_num) hN.le hFn
      ⟨long_two hm hm4 hLu hLv hLi G hG0 w hw τ ρ hpt hB2 hj₃ h3, hfl⟩

theorem fin3_third {a b : Fin 3} (hab : a ≠ b) :
    ∃ t, t ≠ a ∧ t ≠ b ∧ ∀ j, j = a ∨ j = b ∨ j = t := by
  fin_cases a <;> fin_cases b <;> simp at hab
  · exact ⟨2, by decide, by decide, by decide⟩
  · exact ⟨1, by decide, by decide, by decide⟩
  · exact ⟨2, by decide, by decide, by decide⟩
  · exact ⟨0, by decide, by decide, by decide⟩
  · exact ⟨1, by decide, by decide, by decide⟩
  · exact ⟨0, by decide, by decide, by decide⟩

theorem fin3_sum (f : Fin 3 → ℕ) {a b t : Fin 3} (hab : a ≠ b) (hta : t ≠ a) (htb : t ≠ b) :
    ∑ j, f j = f a + f b + f t := by
  rw [Fin.sum_univ_three]
  fin_cases a <;> fin_cases b <;> fin_cases t <;> simp at hab hta htb ⊢ <;> omega

/-- The square with six active marks on at least two path edges. -/
theorem sq_seven (hLu : Lu.card = 3) (hLv : Lv.card = 3) {Li : Fin 2 → Finset ℕ}
    (hLi : ∀ j, (Li j).card = 3) (G : Fin 3 → ℕ → ℕ → ℝ) (hG0 : ∀ j c d, 0 ≤ G j c d)
    (w : Fin 3 → ℝ) (hw : ∀ j, 0 < w j) (τ : Fin 3 → ℕ) (ρ : Fin 3 → Fin 3)
    (hpt : ∀ j, PT (τ j) (ρ j) (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (G j)
      (w j)) (ha : ∑ j, actM τ ρ j = 6) {j₁ j₂ : Fin 3} (h12 : j₁ ≠ j₂) (h1 : ρ j₁ ≠ 0)
    (h2 : ρ j₂ ≠ 0) :
    Hex Lu Lv (faceSum Li (fun _ _ => 1) G) (faceConst3 2 * (∏ j, w j) * d6) := by
  have hP : 0 < ∏ j, w j := Finset.prod_pos fun j _ => hw j
  have hN : 0 < faceConst3 2 * ∏ j, w j := mul_pos (faceConst3_pos 2) hP
  have hd6 := d6_pos
  obtain ⟨jB, hmax, h3B⟩ := actM_max3 τ ρ
  have hBact : ρ jB ≠ 0 := fun h => by rw [actM_inact h] at h3B; omega
  obtain ⟨j₁', hj₁', ha₁'⟩ : ∃ j', j' ≠ jB ∧ ρ j' ≠ 0 := by
    by_cases e : jB = j₁
    · exact ⟨j₂, fun h => h12 (e ▸ h.symm), h2⟩
    · exact ⟨j₁, fun h => e h.symm, h1⟩
  obtain ⟨t, htB, ht1, hall⟩ := fin3_third (Ne.symm hj₁')
  have hsum := fin3_sum (actM τ ρ) (Ne.symm hj₁') htB ht1
  rw [ha, actM_act hBact, actM_act ha₁'] at hsum
  have hge1 := pt_ge1 (hw j₁') ha₁' (hpt j₁')
  have hmx : τ j₁' ≤ τ jB := by have := hmax j₁'; rwa [actM_act ha₁', actM_act hBact] at this
  have hmt : actM τ ρ t ≤ τ jB := by have := hmax t; rwa [actM_act hBact] at this
  have hrB := pt_one (hw jB) hBact (by omega) (hpt jB)
  have hM : ∀ j, j ≠ jB → τ jB ≥ 4 ∨ ¬ (τ j₁' = 3 ∨ actM τ ρ t = 3) → ρ j = 0 ∨ τ j ≤ 2 :=
    fun j hj hc => by
      by_cases hj0 : ρ j = 0
      · exact Or.inl hj0
      refine Or.inr ?_
      rcases hall j with rfl | rfl | rfl
      · exact absurd rfl hj
      · omega
      · rw [actM_act hj0] at hmt hsum; omega
  have hmsc := msc_prod τ ρ jB j₁' hj₁' ha₁'
  have hge := msc_prod_ge τ ρ jB
  rcases Nat.lt_or_ge (τ jB) 4 with hB3 | hB4
  · by_cases h33 : τ j₁' = 3 ∨ actM τ ρ t = 3
    · -- `(3|3)`: N1 on adjacent sides, `[B, 1, B]` on opposite ones
      have e3 : τ jB = 3 := by omega
      have e3' : τ j₁' = 3 := by omega
      have et : actM τ ρ t = 0 := by omega
      have hval : ∀ j, (if ρ j = 0 then 0 else τ j) = if j = t then 0 else 3 := fun j => by
        rcases hall j with rfl | rfl | rfl
        · simp [hBact, e3, htB.symm]
        · simp [ha₁', e3', ht1.symm]
        · simpa [actM] using et
      obtain ⟨p0, p1, p2⟩ := sq_pt hpt
      have w0 := hw 0; have w1 := hw 1; have w2 := hw 2
      rw [sq_three, show 3 * (w 0 * w 1 * w 2) * d6 = 3 * d6 * (w 0 * w 1 * w 2) by ring]
      fin_cases t
      · exact sq_N1_hex_rev hLu hLi hG0 hw (cls0 p0 (by simpa using hval 0) w0)
          (clsABf p1 (by simpa using hval 1) w1) (clsABf p2 (by simpa using hval 2) w2)
      · have b0 := clsABf p0 (by simpa using hval 0) w0
        have b2 := clsABf p2 (by simpa using hval 2) w2
        have key := sq_B1B_hex (N := fun j => if j = 1 then w j else 17 / 16 * w j) hLv hLi hG0
          (fun j => by split_ifs; exacts [hw j, mul_pos (by norm_num) (hw j)])
          (by simpa using b0.2) (by simpa using cls0 p1 (by simpa using hval 1) w1)
          (by simpa using b2.2)
        refine key.weaken (by positivity) ?_
        simp only [show (0 : Fin 3) ≠ 1 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte]
        have := d6_le_A'
        have hp : 0 < w 0 * w 1 * w 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left this hp.le]
      · exact sq_N1_hex hLv hLi hG0 hw (clsABf p0 (by simpa using hval 0) w0)
          (clsABf p1 (by simpa using hval 1) w1) (cls0 p2 (by simpa using hval 2) w2)
    · -- `[B, M, M]`, the largest side in `A B`
      have key := sq_bmm15 hLv hLi G hG0 w hw τ ρ hpt jB (by norm_num)
        (pt_ballA (hw jB) hrB (by omega) (hpt jB)) fun j hj => hM j hj (Or.inr h33)
      refine key.weaken (by positivity) (mul_le_mul_of_nonneg_left ?_ hN.le)
      have := d6_le_A'
      nlinarith
  rcases Nat.lt_or_ge (τ jB) 5 with hB4' | hB5
  · -- four marks on the largest side: `[H, M, M]`
    have key := sq_hmm15 hLv hLi G hG0 w hw τ ρ hpt jB (by norm_num)
      (pt_hexA (hw jB) (hG0 jB) hrB (by omega) (hpt jB)) fun j hj => hM j hj (Or.inl hB4)
    refine key.weaken (by positivity) (mul_le_mul_of_nonneg_left ?_ hN.le)
    have : d6 = 56 / 59 * (17 / 16 * κA) := by unfold d6 a5; ring
    rw [this]
    have := hmsc.1
    nlinarith
  · -- five marks on the largest side: `[B, M, M]` with a single
    have e1 : τ j₁' = 1 := by omega
    have key := sq_bmm15 hLv hLi G hG0 w hw τ ρ hpt jB one_pos
      (by rw [mul_one]; exact pt_ball (hw jB) (by rw [hrB]; decide) (hpt jB))
      fun j hj => hM j hj (Or.inl (by omega))
    refine key.weaken (by positivity) (mul_le_mul_of_nonneg_left ?_ hN.le)
    rw [one_mul]
    exact d6_le_κq.trans (hmsc.2 e1)

/-- **Seven marks: an even face whose active sides carry six marks.** -/
theorem term_even7 (hm : Even m) (hm2 : 2 ≤ m) (hLu : Lu.card = 3) (hLv : Lv.card = 3)
    (hLi : ∀ j, (Li j).card = 3) (G : Fin (m + 1) → ℕ → ℕ → ℝ) (hG0 : ∀ j c d, 0 ≤ G j c d)
    (w : Fin (m + 1) → ℝ) (hw : ∀ j, 0 < w j) (τ : Fin (m + 1) → ℕ) (ρ : Fin (m + 1) → Fin 3)
    (hpt : ∀ j, PT (τ j) (ρ j) (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (G j)
      (w j)) (ha : ∑ j, actM τ ρ j = 6) :
    Kc15 7 Lu Lv (faceSum Li (fun _ _ => 1) G) (faceConst3 m * ∏ j, w j) := by
  have hm1 : 1 ≤ m := by omega
  have hfl := term_floor hLi G hG0 w hw τ ρ hpt hm1
  have ht : tmarks m τ ρ = 7 := by unfold tmarks; simp [hm, ha]
  rw [ht] at hfl
  have hFn := faceSum_nonneg Li (fun _ _ => 1) G (fun _ _ _ => zero_le_one) hG0
  have hP : 0 < ∏ j, w j := Finset.prod_pos fun j _ => hw j
  have hN : 0 < faceConst3 m * ∏ j, w j := mul_pos (faceConst3_pos m) hP
  have hd6 := d6_pos
  have hτa : ∀ j, ρ j ≠ 0 → τ j ≤ 6 := fun j hj => by
    have := actM_le_sum (τ := τ) (ρ := ρ) j; rw [actM_act hj] at this; omega
  rcases one_or_two ρ (exists_active (τ := τ) (by omega)) with
    ⟨j₀, hj₀, hrest⟩ | ⟨j₁, j₂, h12, h1, h2⟩
  · have hτ6 : τ j₀ = 6 := by rw [← actM_single (τ := τ) hj₀ hrest]; exact ha
    have hD : ∀ j, j ≠ j₀ → Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ)
        (G j) (w j) := fun j hj => (hpt j).1 (hrest j hj)
    by_cases h2 : ρ j₀ = 2
    · -- the hexagon part of six marks: the two-distinguished law
      have hH := pt_hex6 h2 hτ6 (hpt j₀)
      refine kc15_of_PB (by norm_num) hN.le hFn ⟨?_, hfl⟩
      set N : Fin (m + 1) → ℝ := fun j => if j = j₀ then a5 * w j else w j with hNdef
      have hNpos : ∀ j, 0 < N j := fun j => by
        simp only [hNdef]; split_ifs
        · exact mul_pos a5_pos (hw j)
        · exact hw j
      rcases Nat.lt_or_ge m 4 with hm4 | hm4
      · obtain rfl : m = 2 := by obtain ⟨k, hk⟩ := hm; omega
        have key := sqLawH hLv hLi G hG0 N hNpos j₀ (by simpa [hNdef, mul_comm] using hH)
          fun j hj => by simpa [hNdef, hj] using (hD j hj).bijGe (hw j).le
        rw [hNdef, prod_ite_scale] at key
        refine key.weaken (by positivity) (le_of_eq ?_)
        unfold d6; ring
      · have key := hexEvenSix m hm hm4 Lu Lv Li hLv hLi G hG0 N hNpos fun j => by
          by_cases hj : j = j₀
          · subst hj; simpa [hNdef, mul_comm] using hH
          · simpa [hNdef, hj] using (hD j hj).hex (hw j).le
        rw [hNdef, prod_ite_scale] at key
        refine key.weaken (by positivity) (le_of_eq ?_)
        unfold d6; ring
    · -- the ball part: one-load closure
      have hB := pt_ball (hw j₀) h2 (hpt j₀)
      have := one_active hLu hLv hLi G hG0 w hw τ ρ hpt hrest one_pos (by rwa [mul_one])
      rw [mul_one] at this
      exact kc15_of_PA (by norm_num) hN.le hFn ⟨this, hfl⟩
  have hB2 : ∀ j, ρ j ≠ 2 := fun j hj => by
    have h6 := pt_ge6 (hw j) hj (hpt j)
    obtain ⟨j', hne, hj'0⟩ : ∃ j', j' ≠ j ∧ ρ j' ≠ 0 := by
      by_cases e : j = j₁
      · exact ⟨j₂, fun h => h12 (e ▸ h.symm), h2⟩
      · exact ⟨j₁, fun h => e h.symm, h1⟩
    have := actM_two (τ := τ) (ρ := ρ) hne
    rw [actM_act hj'0, actM_act (show ρ j ≠ 0 by rw [hj]; decide)] at this
    have := pt_ge1 (hw j') hj'0 (hpt j')
    omega
  rcases Nat.lt_or_ge m 4 with hm4 | hm4
  · obtain rfl : m = 2 := by obtain ⟨k, hk⟩ := hm; omega
    exact kc15_of_PB (by norm_num) hN.le hFn
      ⟨sq_seven hLu hLv hLi G hG0 w hw τ ρ hpt ha h12 h1 h2, hfl⟩
  · obtain ⟨j₃, hj₃, h3⟩ := exists_light ha (by norm_num) h12 h1 h2
    exact kc15_of_PA (by norm_num) hN.le hFn
      ⟨long_two hm hm4 hLu hLv hLi G hG0 w hw τ ρ hpt hB2 hj₃ h3, hfl⟩

end Six

/-! ### The face rule -/

section Rule

variable {m : ℕ} {Lu Lv : Finset ℕ} {Li : Fin m → Finset ℕ}

/-- **A term of a face with at most seven marks.** -/
theorem term15 (hm1 : 1 ≤ m) (hLu : Lu.card = 3) (hLv : Lv.card = 3)
    (hLi : ∀ j, (Li j).card = 3) (G : Fin (m + 1) → ℕ → ℕ → ℝ) (hG0 : ∀ j c d, 0 ≤ G j c d)
    (w : Fin (m + 1) → ℝ) (hw : ∀ j, 0 < w j) (τ : Fin (m + 1) → ℕ) (ρ : Fin (m + 1) → Fin 3)
    (hpt : ∀ j, PT (τ j) (ρ j) (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (G j)
      (w j)) (hn : tmarks m τ ρ ≤ 7) :
    Kc15 (tmarks m τ ρ) Lu Lv (faceSum Li (fun _ _ => 1) G) (faceConst3 m * ∏ j, w j) := by
  rcases Nat.lt_or_ge (tmarks m τ ρ) 3 with h2 | h3
  · exact term_low15 hm1 hLu hLv hLi G hG0 w hw τ ρ hpt (by omega)
  rcases Nat.even_or_odd m with hev | hodd
  · have hm2 : 2 ≤ m := by obtain ⟨r, hr⟩ := hev; omega
    have ht : tmarks m τ ρ = 1 + ∑ j, actM τ ρ j := by unfold tmarks; simp [hev]
    rw [ht] at hn h3 ⊢
    rcases (show ∑ j, actM τ ρ j = 2 ∨ ∑ j, actM τ ρ j = 3 ∨ ∑ j, actM τ ρ j = 4 ∨
        ∑ j, actM τ ρ j = 5 ∨ ∑ j, actM τ ρ j = 6 by omega) with e | e | e | e | e <;> rw [e]
    · exact term_even3 hev hm2 hLu hLv hLi G hG0 w hw τ ρ hpt e
    · exact term_even4 hev hm2 hLu hLv hLi G hG0 w hw τ ρ hpt e
    · exact term_even5 hev hm2 hLu hLv hLi G hG0 w hw τ ρ hpt e
    · exact term_even6 hev hm2 hLu hLv hLi G hG0 w hw τ ρ hpt e
    · exact term_even7 hev hm2 hLu hLv hLi G hG0 w hw τ ρ hpt e
  · exact term_odd15 hodd hLu hLv hLi G hG0 w hw τ ρ hpt h3 hn

/-- **The face rule through seven marks**: `k ≤ 7` is at least the number of marks of the face
(one if it is even) and of its sides. -/
def markRule15 (k m : ℕ) (τ : Fin (m + 1) → ℕ) : Prop :=
  1 ≤ m ∧ (if Even m then 1 else 0) + ∑ j, τ j ≤ k ∧ k ≤ 7

/-- **The face rule through seven marks is sound.** -/
theorem markRule15_sound {k : ℕ} {τ : Fin (m + 1) → ℕ} (hr : markRule15 k m τ)
    (Lu Lv : Finset ℕ) (Li : Fin m → Finset ℕ) (hLu : Lu.card = 3) (hLv : Lv.card = 3)
    (hLi : ∀ j, (Li j).card = 3) (E : Fin (m + 1) → ℕ → ℕ → ℝ) (hE0 : ∀ j c d, 0 ≤ E j c d)
    (A : Fin (m + 1) → ℝ) (hA : ∀ j, 0 < A j)
    (hE : ∀ j, Kc15 (τ j) (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    Kc15 k Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j) := by
  obtain ⟨hm1, hsum, hk7⟩ := hr
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- an odd face over sides without marks
    have hodd : ¬ Even m := fun h => by simp [h] at hsum
    have hall : ∀ j, τ j = 0 := fun j => by
      have := Finset.single_le_sum (f := τ) (fun _ _ => Nat.zero_le _) (mem_univ j)
      split_ifs at hsum <;> omega
    exact domFaceClosed_odd m (Nat.not_even_iff_odd.mp hodd) Lu Lv Li hLi E hE0 A hA fun j => by
      have := hE j; rw [hall j] at this; exact this
  obtain ⟨u, v₁, v₂, Y₁, Y₂, hu, hv₁, hv₂, huv, hY₁, hY₂, hP1, hP2, hEY⟩ :=
    face15_data τ _ _ E A (fun j => (hA j).le) hE
  have hG0 := gT3_nonneg hu hY₁ hY₂
  rw [Kc15_pos hk]
  refine mx_expand3 (coneAP k) Lu Lv Li E hE0 A hA hu hv₁ hv₂ huv hY₁ hY₂ hEY fun ρ hρ => ?_
  have hpt : ∀ j, PT (τ j) (ρ j) (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ)
      (gT3 u Y₁ Y₂ j (ρ j)) (wT3 u v₁ v₂ j (ρ j)) :=
    fun j => gT3_pt15 (k := τ j) j (ρ j) (hY₁ j) (hY₂ j) (hP1 j) (hP2 j)
  have hn : tmarks m τ ρ ≤ k := by
    unfold tmarks
    have := sum_actM_le (τ := τ) (ρ := ρ)
    omega
  have key := term15 hm1 hLu hLv hLi _ (fun j c d => hG0 j (ρ j) c d) _ hρ τ ρ hpt (by omega)
  have := Kc15_mono (fc_prod_nonneg hρ) hn key
  rwa [Kc15_pos hk] at this

end Rule

end Outerplanar.F15
