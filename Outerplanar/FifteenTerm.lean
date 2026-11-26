/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.FifteenClass
import Outerplanar.MarkFiveSixRule
import Outerplanar.Sq15Sound

/-!
# Terms of the fifteen-face classes

The expansion of the classes `Kc15 k` of `Outerplanar/FifteenClass.lean` into three alternatives
per side (the constant, `PA k`, `PB k`). A term of a face picks one per side; its tables have the
*pure types* `PT k r`. This file has

* `PT`, `kc15_data`, `face15_data`, `gT3_pt15`;
* the facts of a pure type used by the face laws (`pt_ball`, `pt_ballA`, `pt_hex`, `pt_hexA`,
  `pt_hexD`, `pt_kc`, and the list classes of `Outerplanar/Sq15Sound.lean`: `pt_Z`, `pt_W`,
  `pt_ABf`, `pt_BAHf`, `pt_Bf5`, `pt_Bf6`, `pt_H7f`);
* **`term_floor`** — Lemma F at a term: a face with `n` marks (its own, if even, and those of its
  active sides) has the floor `(2/3)^n`;
* the odd- and even-face closures used below: `odd_ball`, `odd_hex`, `even_one`.

Formalized by Claude (milestone M5 of `ai_research_notes/OUTERPLANAR_13_15_LEAN_PLAN.md`).
-/

namespace Outerplanar.F15

open Finset Outerplanar Outerplanar.SqMulti

/-! ### Pure types -/

/-- **The pure type** `(k, r)` of a term table. -/
def PT (k : ℕ) (r : Fin 3) (S T : Finset ℕ) (Y : ℕ → ℕ → ℝ) (v : ℝ) : Prop :=
  (r = 0 → Dominant S T Y v) ∧ (r = 1 → PA k S T Y v) ∧ (r = 2 → PB k S T Y v)

/-- **The alternatives of a class.** -/
theorem kc15_data {S T : Finset ℕ} {W : ℕ → ℕ → ℝ} {N : ℝ} {k : ℕ} (hN : 0 ≤ N)
    (h : Kc15 k S T W N) :
    ∃ (u v₁ v₂ : ℝ) (Y₁ Y₂ : ℕ → ℕ → ℝ), 0 ≤ u ∧ 0 ≤ v₁ ∧ 0 ≤ v₂ ∧ N ≤ u + v₁ + v₂ ∧
      (∀ c d, 0 ≤ Y₁ c d) ∧ (∀ c d, 0 ≤ Y₂ c d) ∧ PA k S T Y₁ v₁ ∧ PB k S T Y₂ v₂ ∧
      ∀ c ∈ S, ∀ d ∈ T, c ≠ d → u + Y₁ c d + Y₂ c d ≤ W c d := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨N, 0, 0, fun _ _ => 0, fun _ _ => 0, hN, le_rfl, le_rfl, by simp, fun _ _ => le_rfl,
      fun _ _ => le_rfl, rfl, rfl, fun c hc d hd hcd => by simpa using h c hc d hd hcd⟩
  rw [Kc15_pos hk] at h
  obtain ⟨u, v, Y, hu, hv, hNuv, hY0, hY, hW⟩ := h
  obtain ⟨Y₁, Y₂, v₁, v₂, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hY
  refine ⟨u, v₁, v₂, Y₁, Y₂, hu, h1, h2, by linarith, h4, h5, h7, h8, fun c hc d hd hcd => ?_⟩
  have := h6 c hc d hd hcd
  have := hW c hc d hd hcd
  linarith

/-- **The alternatives of all sides of a face.** -/
theorem face15_data {n : ℕ} (τ : Fin n → ℕ) (L R : Fin n → Finset ℕ) (E : Fin n → ℕ → ℕ → ℝ)
    (A : Fin n → ℝ) (hA : ∀ j, 0 ≤ A j) (hE : ∀ j, Kc15 (τ j) (L j) (R j) (E j) (A j)) :
    ∃ (u v₁ v₂ : Fin n → ℝ) (Y₁ Y₂ : Fin n → ℕ → ℕ → ℝ), (∀ j, 0 ≤ u j) ∧ (∀ j, 0 ≤ v₁ j) ∧
      (∀ j, 0 ≤ v₂ j) ∧ (∀ j, A j ≤ u j + v₁ j + v₂ j) ∧ (∀ j c d, 0 ≤ Y₁ j c d) ∧
      (∀ j c d, 0 ≤ Y₂ j c d) ∧ (∀ j, PA (τ j) (L j) (R j) (Y₁ j) (v₁ j)) ∧
      (∀ j, PB (τ j) (L j) (R j) (Y₂ j) (v₂ j)) ∧
      ∀ j, ∀ c ∈ L j, ∀ d ∈ R j, c ≠ d → u j + Y₁ j c d + Y₂ j c d ≤ E j c d := by
  choose u v₁ v₂ Y₁ Y₂ h1 h2 h3 h4 h5 h6 h7 h8 h9 using fun j => kc15_data (hA j) (hE j)
  exact ⟨u, v₁, v₂, Y₁, Y₂, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- **The pure type of a term table.** -/
theorem gT3_pt15 {n : ℕ} {u v₁ v₂ : Fin n → ℝ} {Y₁ Y₂ : Fin n → ℕ → ℕ → ℝ} {k : ℕ}
    {S T : Finset ℕ} (j : Fin n) (r : Fin 3) (hY₁ : ∀ c d, 0 ≤ Y₁ j c d)
    (hY₂ : ∀ c d, 0 ≤ Y₂ j c d) (h1 : PA k S T (Y₁ j) (v₁ j)) (h2 : PB k S T (Y₂ j) (v₂ j)) :
    PT k r S T (gT3 u Y₁ Y₂ j r) (wT3 u v₁ v₂ j r) := by
  refine ⟨fun hr => fun c _ d _ hcd => by simp [gT3, wT3, hr, hcd], fun hr => ?_, fun hr => ?_⟩
  · have e : wT3 u v₁ v₂ j r = v₁ j := by simp [wT3, hr]
    rw [e]
    exact (conePA k).mono hY₁ (fun c _ d _ hcd => by simp [gT3, hr, hcd]) h1
  · have e : wT3 u v₁ v₂ j r = v₂ j := by simp [wT3, hr]
    rw [e]
    exact (conePB k).mono hY₂ (fun c _ d _ hcd => by simp [gT3, hr, hcd]) h2

/-! ### Facts of a pure type -/

section Pure

variable {S T : Finset ℕ} {Y : ℕ → ℕ → ℝ} {v : ℝ} {k : ℕ} {r : Fin 3}

theorem r_cases3 (r : Fin 3) : r = 0 ∨ r = 1 ∨ r = 2 := by fin_cases r <;> simp

theorem pt_ge6 (hv : 0 < v) (hr : r = 2) (h : PT k r S T Y v) : 6 ≤ k := by
  by_contra hk
  exact hv.ne' ((PB_low (by omega)).mp (h.2.2 hr))

theorem pt_ge1 (hv : 0 < v) (hr : r ≠ 0) (h : PT k r S T Y v) : 1 ≤ k := by
  rcases r_cases3 r with rfl | rfl | rfl
  · exact absurd rfl hr
  · by_contra hk
    obtain rfl : k = 0 := by omega
    exact hv.ne' (h.2.1 rfl)
  · have := pt_ge6 hv rfl h; omega

theorem pt_one (hv : 0 < v) (hr : r ≠ 0) (hk : k ≤ 5) (h : PT k r S T Y v) : r = 1 := by
  rcases r_cases3 r with rfl | rfl | rfl
  · exact absurd rfl hr
  · rfl
  · have := pt_ge6 hv rfl h; omega

theorem pt_floor (hv : 0 < v) (h0 : ∀ c d, 0 ≤ Y c d) (h : PT k r S T Y v) :
    Dominant S T Y (fl (if r = 0 then 0 else k) * v) := by
  rcases r_cases3 r with rfl | rfl | rfl
  · simpa [fl] using h.1 rfl
  · simpa using PA_floor hv.le (pt_ge1 hv (by decide) h) (h.2.1 rfl)
  · simpa using PB_floor hv.le h0 (h.2.2 rfl)

theorem pt_ball (hv : 0 < v) (hr : r ≠ 2) (h : PT k r S T Y v) : InBall S T Y v := by
  rcases r_cases3 r with rfl | rfl | rfl
  · exact (h.1 rfl).inBall hv.le
  · exact PA_ball hv.le (pt_ge1 hv (by decide) h) (h.2.1 rfl)
  · exact absurd rfl hr

theorem pt_ballA (hv : 0 < v) (hr : r = 1) (hk : k ≤ 3) (h : PT k r S T Y v) :
    InBall S T Y (v * (17 / 16)) :=
  PA_ballA (pt_ge1 hv (by rw [hr]; decide) h) hk (h.2.1 hr)

theorem pt_hex (hv : 0 < v) (h0 : ∀ c d, 0 ≤ Y c d) (h : PT k r S T Y v) : Hex S T Y v := by
  rcases r_cases3 r with rfl | rfl | rfl
  · exact (h.1 rfl).hex hv.le
  · exact PA_hex hv.le h0 (pt_ge1 hv (by decide) h) (h.2.1 rfl)
  · exact PB_hex hv.le h0 (h.2.2 rfl)

theorem pt_hexA (hv : 0 < v) (h0 : ∀ c d, 0 ≤ Y c d) (hr : r = 1) (hk : k ≤ 4)
    (h : PT k r S T Y v) : Hex S T Y (v * (17 / 16)) :=
  PA_hexA hv.le h0 (pt_ge1 hv (by rw [hr]; decide) h) hk (h.2.1 hr)

theorem pt_hexD (hv : 0 < v) (hr : r = 2) (h : PT k r S T Y v) : Hex S T Y (v * d6) :=
  PB_hexD hv.le (pt_ge6 hv hr h) (h.2.2 hr)

theorem pt_hex6 (hr : r = 2) (hk : k = 6) (h : PT k r S T Y v) : Hex S T Y (v * a5) := by
  have := h.2.2 hr
  rw [hk] at this
  exact this.1

/-- The classes of `Outerplanar/MarkThreeFour.lean`, at most two marks. -/
theorem pt_kc (hv : 0 < v) (h0 : ∀ c d, 0 ≤ Y c d) (hk : r = 0 ∨ k ≤ 2) (h : PT k r S T Y v) :
    Kc (if r = 0 then 0 else k) S T Y v := by
  rcases r_cases3 r with rfl | rfl | rfl
  · exact h.1 rfl
  · have hk2 : k ≤ 2 := hk.resolve_left (by decide)
    have h1 := h.2.1 rfl
    have hk1 := pt_ge1 hv (by decide) h
    simp only [show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte]
    interval_cases k
    · exact Mx.of_P hv.le h0 h1
    · exact Mx.of_P hv.le h0 h1
  · have := pt_ge6 hv rfl h; omega

end Pure

/-! ### Faces -/

section Face

variable {m : ℕ} {Lu Lv : Finset ℕ} {Li : Fin m → Finset ℕ}

theorem fl_sum {n : ℕ} (x : Fin n → ℕ) : ∏ j, fl (x j) = fl (∑ j, x j) := by
  unfold fl; rw [Finset.prod_pow_eq_pow_sum]

/-- The marks of a term: the face's own (if even) and those of its active sides. -/
def tmarks (m : ℕ) (τ : Fin (m + 1) → ℕ) (ρ : Fin (m + 1) → Fin 3) : ℕ :=
  (if Even m then 1 else 0) + ∑ j, actM τ ρ j

/-- **Lemma F at a term.** -/
theorem term_floor (hLi : ∀ j, (Li j).card = 3) (G : Fin (m + 1) → ℕ → ℕ → ℝ)
    (hG0 : ∀ j c d, 0 ≤ G j c d) (w : Fin (m + 1) → ℝ) (hw : ∀ j, 0 < w j)
    (τ : Fin (m + 1) → ℕ) (ρ : Fin (m + 1) → Fin 3)
    (hpt : ∀ j, PT (τ j) (ρ j) (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (G j)
      (w j)) (hm1 : 1 ≤ m) :
    Dominant Lu Lv (faceSum Li (fun _ _ => 1) G)
      (fl (tmarks m τ ρ) * (faceConst3 m * ∏ j, w j)) := by
  have hD : ∀ j, Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (G j)
      (fl (actM τ ρ j) * w j) := fun j => pt_floor (hw j) (hG0 j) (hpt j)
  have h := dom_face_bare Lu Lv Li hLi G hG0 (fun j => fl (actM τ ρ j) * w j)
    (fun j => (mul_pos (fl_pos _) (hw j)).le) hD
  rw [Finset.prod_mul_distrib, fl_sum] at h
  have hP : 0 < ∏ j, w j := Finset.prod_pos fun j _ => hw j
  have hf := fl_pos (∑ j, actM τ ρ j)
  refine h.le ?_
  unfold tmarks
  rcases Nat.even_or_odd m with hev | hodd
  · simp only [hev, ↓reduceIte]
    obtain ⟨k, hk⟩ := hev
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have e : m = 2 * k' + 2 := by omega
    subst e
    have h3 := faceConst3_even_ge_three k'
    have hob : oddB (2 * k' + 2) = faceConst3 (2 * k' + 2) - 1 := by
      have := oddB_even (k' + 1)
      rwa [show 2 * (k' + 1) = 2 * k' + 2 by ring] at this
    rw [hob, fl_add, show fl 1 = 2 / 3 by unfold fl; norm_num]
    have : 2 / 3 * faceConst3 (2 * k' + 2) ≤ faceConst3 (2 * k' + 2) - 1 := by linarith
    have := mul_le_mul_of_nonneg_right this (mul_pos hf hP).le
    nlinarith
  · simp only [Nat.not_even_iff_odd.mpr hodd, ↓reduceIte, zero_add]
    have hob : oddB m = faceConst3 m := by
      have := oddB_div_odd hodd
      rwa [div_eq_one_iff_eq (faceConst3_pos m).ne'] at this
    rw [hob]
    exact le_of_eq (by ring)

theorem odd_ball (hm : Odd m) (hLu : Lu.card = 3) (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3)
    (G : Fin (m + 1) → ℕ → ℕ → ℝ) (hG0 : ∀ j c d, 0 ≤ G j c d) (B : Fin (m + 1) → ℝ)
    (hB : ∀ j, 0 < B j)
    (hE : ∀ j, InBall (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (G j) (B j)) :
    InBall Lu Lv (faceSum Li (fun _ _ => 1) G) (faceConst3 m * ∏ j, B j) := by
  rcases Nat.lt_or_ge m 3 with h3 | h3
  · obtain rfl : m = 1 := by obtain ⟨k, hk⟩ := hm; omega
    rw [faceConst3_one, one_mul]
    exact ballTriClosed Lu Lv Li hLu hLv hLi G hG0 B hB hE
  · exact ballOddClosed m hm h3 Lu Lv Li hLu hLv hLi G hG0 B hB hE

theorem odd_hex (hm : Odd m) (hLu : Lu.card = 3) (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3)
    (G : Fin (m + 1) → ℕ → ℕ → ℝ) (hG0 : ∀ j c d, 0 ≤ G j c d) (B : Fin (m + 1) → ℝ)
    (hB : ∀ j, 0 < B j)
    (hE : ∀ j, Hex (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (G j) (B j)) :
    Hex Lu Lv (faceSum Li (fun _ _ => 1) G) (faceConst3 m * ∏ j, B j) := by
  rcases Nat.lt_or_ge m 3 with h3 | h3
  · obtain rfl : m = 1 := by obtain ⟨k, hk⟩ := hm; omega
    rw [faceConst3_one, one_mul]
    exact hex_tri hLi hG0 (fun j => (hB j).le) hE
  · exact hexOddClosed m hm h3 Lu Lv Li hLu hLv hLi G hG0 B hB hE

theorem kc15_of_PA {S T : Finset ℕ} {Y : ℕ → ℕ → ℝ} {v : ℝ} {k : ℕ} (hk : 1 ≤ k) (hv : 0 ≤ v)
    (h0 : ∀ c d, 0 ≤ Y c d) (h : PA k S T Y v) : Kc15 k S T Y v := by
  rw [Kc15_pos hk]; exact Mx.of_P hv h0 (Alt2.of_left (conePB k) hv h0 h)

theorem kc15_of_PB {S T : Finset ℕ} {Y : ℕ → ℕ → ℝ} {v : ℝ} {k : ℕ} (hk : 1 ≤ k) (hv : 0 ≤ v)
    (h0 : ∀ c d, 0 ≤ Y c d) (h : PB k S T Y v) : Kc15 k S T Y v := by
  rw [Kc15_pos hk]; exact Mx.of_P hv h0 (Alt2.of_right (conePA k) hv h0 h)

/-- The product of scales, one active side scaled. -/
theorem prod_scale_one {n : ℕ} (j₀ : Fin n) (g : ℝ) (hg : 1 ≤ g) (s : Fin n → ℝ)
    (hs : ∀ j, 1 ≤ s j) (h₀ : g ≤ s j₀) : g ≤ ∏ j, s j := by
  rw [← Finset.mul_prod_erase univ s (mem_univ j₀)]
  have : 1 ≤ ∏ j ∈ univ.erase j₀, s j := Finset.one_le_prod₀ fun j _ => hs j
  nlinarith

/-- **The terms with at most two marks**: the rules of `Outerplanar/MarkThreeFour.lean`. -/
theorem term_low15 (hm1 : 1 ≤ m) (hLu : Lu.card = 3) (hLv : Lv.card = 3)
    (hLi : ∀ j, (Li j).card = 3) (G : Fin (m + 1) → ℕ → ℕ → ℝ) (hG0 : ∀ j c d, 0 ≤ G j c d)
    (w : Fin (m + 1) → ℝ) (hw : ∀ j, 0 < w j) (τ : Fin (m + 1) → ℕ) (ρ : Fin (m + 1) → Fin 3)
    (hpt : ∀ j, PT (τ j) (ρ j) (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (G j)
      (w j)) (hn : tmarks m τ ρ ≤ 2) :
    Kc15 (tmarks m τ ρ) Lu Lv (faceSum Li (fun _ _ => 1) G) (faceConst3 m * ∏ j, w j) := by
  unfold tmarks at hn ⊢
  refine Kc15_of_kc hn (markRule_sound ⟨hm1, le_rfl, by omega⟩ Lu Lv Li hLu hLv hLi G hG0 w hw
    fun j => ?_)
  have := pt_kc (hw j) (hG0 j) (by
    by_cases hj : ρ j = 0
    · exact Or.inl hj
    · refine Or.inr ?_
      have := actM_le_sum (τ := τ) (ρ := ρ) j
      rw [actM_act hj] at this
      split_ifs at hn <;> omega) (hpt j)
  exact this

/-- **Odd faces with at least three active marks.** -/
theorem term_odd15 (hm : Odd m) (hLu : Lu.card = 3) (hLv : Lv.card = 3)
    (hLi : ∀ j, (Li j).card = 3) (G : Fin (m + 1) → ℕ → ℕ → ℝ) (hG0 : ∀ j c d, 0 ≤ G j c d)
    (w : Fin (m + 1) → ℝ) (hw : ∀ j, 0 < w j) (τ : Fin (m + 1) → ℕ) (ρ : Fin (m + 1) → Fin 3)
    (hpt : ∀ j, PT (τ j) (ρ j) (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (G j)
      (w j)) (h3 : 3 ≤ tmarks m τ ρ) (h7 : tmarks m τ ρ ≤ 7) :
    Kc15 (tmarks m τ ρ) Lu Lv (faceSum Li (fun _ _ => 1) G) (faceConst3 m * ∏ j, w j) := by
  have hm1 : 1 ≤ m := by obtain ⟨k, hk⟩ := hm; omega
  have hfl := term_floor hLi G hG0 w hw τ ρ hpt hm1
  have hFn := faceSum_nonneg Li (fun _ _ => 1) G (fun _ _ _ => zero_le_one) hG0
  have hP : 0 < ∏ j, w j := Finset.prod_pos fun j _ => hw j
  have hN : 0 < faceConst3 m * ∏ j, w j := mul_pos (faceConst3_pos m) hP
  have ht : tmarks m τ ρ = ∑ j, actM τ ρ j := by
    unfold tmarks; simp [Nat.not_even_iff_odd.mpr hm]
  set a := tmarks m τ ρ with ha
  have hτa : ∀ j, ρ j ≠ 0 → τ j ≤ a := fun j hj => by
    have := actM_le_sum (τ := τ) (ρ := ρ) j; rw [actM_act hj] at this; omega
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, ρ j₀ ≠ 0 := by
    by_contra hc; push Not at hc
    have : ∑ i, actM τ ρ i = 0 := Finset.sum_eq_zero fun i _ => actM_inact (hc i)
    omega
  have hball : (∀ j, ρ j ≠ 2) → InBall Lu Lv (faceSum Li (fun _ _ => 1) G)
      (faceConst3 m * ∏ j, w j) := fun h2 => by
    have := odd_ball hm hLu hLv hLi G hG0 w hw fun j => pt_ball (hw j) (h2 j) (hpt j)
    exact this
  by_cases h2 : ∃ j, ρ j = 2
  · -- a hexagon alternative: six or seven marks
    obtain ⟨j₂, hj₂⟩ := h2
    have h6 := pt_ge6 (hw j₂) hj₂ (hpt j₂)
    have h6a := hτa j₂ (by rw [hj₂]; decide)
    set κ : ℝ := if τ j₂ = 6 then a5 else d6 with hκ
    have hκ1 : d6 ≤ κ := by simp only [hκ]; split_ifs; exacts [d6_le_a5, le_rfl]
    have hκpos : 0 < κ := lt_of_lt_of_le d6_pos hκ1
    have hX : ∀ j, Hex (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (G j)
        (if j = j₂ then κ * w j else w j) := fun j => by
      by_cases hj : j = j₂
      · subst hj
        simp only [ite_true]
        by_cases e : τ j = 6
        · simp only [hκ, e, ↓reduceIte]
          rw [mul_comm]; exact pt_hex6 hj₂ e (hpt j)
        · simp only [hκ, e, ↓reduceIte]
          rw [mul_comm]; exact pt_hexD (hw j) hj₂ (hpt j)
      · simp only [hj, ite_false]; exact pt_hex (hw j) (hG0 j) (hpt j)
    have key := odd_hex hm hLu hLv hLi G hG0 _ (fun j => by
      split_ifs; exacts [mul_pos hκpos (hw j), hw j]) hX
    rw [prod_ite_scale] at key
    have hB : PB a Lu Lv (faceSum Li (fun _ _ => 1) G) (faceConst3 m * ∏ j, w j) := by
      rcases (show a = 6 ∨ a = 7 by omega) with e | e
      · have e6 : τ j₂ = 6 := by omega
        rw [e]
        refine ⟨?_, by rw [← e]; exact hfl⟩
        simp only [hκ, e6, ↓reduceIte] at key
        rwa [show faceConst3 m * (a5 * ∏ j, w j) = faceConst3 m * (∏ j, w j) * a5 by ring] at key
      · rw [e]
        refine ⟨?_, by rw [← e]; exact hfl⟩
        refine key.weaken (by have := d6_pos; positivity) ?_
        have := mul_le_mul_of_nonneg_left hκ1 hN.le
        nlinarith
    exact kc15_of_PB (by omega) hN.le hFn hB
  push Not at h2
  have hB := hball h2
  refine kc15_of_PA (by omega) hN.le hFn ?_
  rcases (show a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 by omega) with e | e | e | e | e
  · -- three marks: the active sides are in `A B`
    rw [e] at hfl ⊢
    refine ⟨?_, hfl⟩
    have hs := odd_ball hm hLu hLv hLi G hG0 (fun j => if ρ j = 0 then w j else w j * (17 / 16))
      (fun j => by split_ifs; exacts [hw j, mul_pos (hw j) (by norm_num)]) fun j => by
        by_cases hj : ρ j = 0
        · simp only [hj, ↓reduceIte]; exact pt_ball (hw j) (by rw [hj]; decide) (hpt j)
        · simp only [hj, ↓reduceIte]
          exact pt_ballA (hw j) (pt_one (hw j) hj (by have := hτa j hj; omega) (hpt j))
            (by have := hτa j hj; omega) (hpt j)
    show InBall _ _ _ ((faceConst3 m * ∏ j, w j) * (17 / 16))
    refine hs.weaken (by positivity) ?_
    have e1 : ∏ j, (if ρ j = 0 then w j else w j * (17 / 16))
        = (∏ j, w j) * ∏ j, (if ρ j = 0 then (1 : ℝ) else 17 / 16) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun j _ => by split_ifs <;> ring
    have e2 : 17 / 16 ≤ ∏ j, (if ρ j = 0 then (1 : ℝ) else 17 / 16) :=
      prod_scale_one j₀ (17 / 16) (by norm_num) _ (fun j => by split_ifs <;> norm_num)
        (by simp [hj₀])
    rw [e1]
    have := faceConst3_pos m
    have := mul_le_mul_of_nonneg_left e2 hN.le
    nlinarith
  · -- four marks: `B` and `A H` (one active side scaled)
    rw [e] at hfl ⊢
    refine ⟨⟨hB, ?_⟩, hfl⟩
    have hX : ∀ j, Hex (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (G j)
        (if j = j₀ then 17 / 16 * w j else w j) := fun j => by
      by_cases hj : j = j₀
      · subst hj
        simp only [ite_true]
        rw [mul_comm]
        exact pt_hexA (hw j) (hG0 j) (pt_one (hw j) hj₀ (by have := hτa j hj₀; omega) (hpt j))
          (by have := hτa j hj₀; omega) (hpt j)
      · simp only [hj, ite_false]; exact pt_hex (hw j) (hG0 j) (hpt j)
    have key := odd_hex hm hLu hLv hLi G hG0 _ (fun j => by
      split_ifs; exacts [mul_pos (by norm_num) (hw j), hw j]) hX
    rw [prod_ite_scale] at key
    rwa [show faceConst3 m * (17 / 16 * ∏ j, w j) = faceConst3 m * (∏ j, w j) * (17 / 16) by ring]
      at key
  · rw [e] at hfl ⊢; exact ⟨hB, hfl⟩
  · rw [e] at hfl ⊢; exact ⟨hB, hfl⟩
  · rw [e] at hfl ⊢; exact ⟨hB, hfl⟩

end Face

end Outerplanar.F15
