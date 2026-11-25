/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.GainBare
import Outerplanar.SevenVertex

/-!
# Mixtures of the constant and the gain ball

The class of the branching-squares theorem (research note
`ai_research_notes/OUTERPLANAR_BRANCHING_SQUARES_2026-11-23.md`, "Keeping a gain in the boundary
table"): a profile **dominates a mixture of the constant one and a member of `A · B`**, where `B` is
the unit ball of `Outerplanar/Ball.lean` and `A = 17/16`. Since the ball class is closed under sums
(`InBall.add`), a convex combination of members of `A · B` is again one, and the mixture is kept
unnormalized:

`BMix S T W N` — `W ≥ u + Y` on proper pairs, with `u, v ≥ 0`, `u + v ≥ N` and
`Y ∈ InBall (v · 17/16)`.

* `BMix.inBall` — the class lies in the ball class with constant `N`;
* `BMix.of_dom`, `BMix.of_ball` — greedy profiles, and members of the ball class with constant
  `N · 17/16`;
* `BMix.mul_dom`, `BMix.mul`, `BMix.add`, `BMix.finsum`, `BMix.swap`, `BMix.mono`,
  `BMix.weaken` — closure;
* `lvZ_ball` — the table `(2 + [c ≠ a] + [d ≠ b]) / 3` of a deficient bare even face is in
  `InBall (17/16)`: a matched family has product at least `128/81`, the spread is at most `2`,
  and `(128/81)^100 (1/2)^9 ≥ (17/16)^600`;
* `bmix_even_bare` — every bare even face is in the class with its ordinary constant (the proofs
  of `gain1_square` and `gain1_even_long` with this table);
* `lift_bmix` — vertex lifts keep the class, with the constant doubled.

The theorem of the note is due to another AI session of this repository's collaboration; audited
and formalized by Claude.
-/

namespace Outerplanar

open Finset

variable {S T U : Finset ℕ} {W W' X : ℕ → ℕ → ℝ} {N N' A : ℝ}

/-- A scalar multiple of a member of the ball class. -/
theorem InBall.smul {l : ℝ} (hl : 0 ≤ l) (hA : 0 ≤ A) (h : InBall S T W A) :
    InBall S T (fun c d => l * W c d) (l * A) :=
  (Dominant.inBall hl (fun _ _ _ _ _ => le_refl l) : InBall S T (fun _ _ => l) l).mul hl hA h

/-! ### The class -/

/-- **The mixture class**: `W` dominates `u + Y` on proper pairs, with `u + v ≥ N` and `Y` in the
ball class with constant `v · 17/16`. -/
def BMix (S T : Finset ℕ) (W : ℕ → ℕ → ℝ) (N : ℝ) : Prop :=
  ∃ (u v : ℝ) (Y : ℕ → ℕ → ℝ), 0 ≤ u ∧ 0 ≤ v ∧ N ≤ u + v ∧ (∀ c d, 0 ≤ Y c d) ∧
    InBall S T Y (v * (17 / 16)) ∧ ∀ c ∈ S, ∀ d ∈ T, c ≠ d → u + Y c d ≤ W c d

theorem BMix.of_dom (hN : 0 ≤ N) (h : Dominant S T W N) : BMix S T W N :=
  ⟨N, 0, fun _ _ => 0, hN, le_refl 0, by simp, fun _ _ => le_refl 0,
    by rw [zero_mul]; exact InBall.zero fun _ _ => le_refl 0,
    fun c hc d hd hcd => by simpa using h c hc d hd hcd⟩

theorem BMix.of_ball (hN : 0 ≤ N) (h0 : ∀ c d, 0 ≤ W c d) (h : InBall S T W (N * (17 / 16))) :
    BMix S T W N :=
  ⟨0, N, W, le_refl 0, hN, by simp, h0, h, fun c _ d _ _ => by simp⟩

theorem BMix.zero (h0 : ∀ c d, 0 ≤ W c d) : BMix S T W 0 :=
  BMix.of_dom (le_refl 0) fun c _ d _ _ => h0 c d

theorem BMix.mono (h : BMix S T W N) (hle : ∀ c ∈ S, ∀ d ∈ T, c ≠ d → W c d ≤ W' c d) :
    BMix S T W' N := by
  obtain ⟨u, v, Y, hu, hv, hN, hY0, hY, hW⟩ := h
  exact ⟨u, v, Y, hu, hv, hN, hY0, hY, fun c hc d hd hcd =>
    (hW c hc d hd hcd).trans (hle c hc d hd hcd)⟩

theorem BMix.weaken (hle : N' ≤ N) (h : BMix S T W N) : BMix S T W N' := by
  obtain ⟨u, v, Y, hu, hv, hN, hY0, hY, hW⟩ := h
  exact ⟨u, v, Y, hu, hv, hle.trans hN, hY0, hY, hW⟩

theorem BMix.swap (h : BMix S T W N) : BMix T S (fun d c => W c d) N := by
  obtain ⟨u, v, Y, hu, hv, hN, hY0, hY, hW⟩ := h
  exact ⟨u, v, fun d c => Y c d, hu, hv, hN, fun _ _ => hY0 _ _, hY.swap,
    fun d hd c hc hdc => hW c hc d hd (Ne.symm hdc)⟩

/-- **The class lies in the ball class.** -/
theorem BMix.inBall (hN : 0 ≤ N) (h : BMix S T W N) :
    InBall S T W N := by
  obtain ⟨u, v, Y, hu, hv, hNuv, hY0, hY, hW⟩ := h
  have h1 : InBall S T (fun c d => u * (if c ≠ d then 1 else 0)) (u * 1) :=
    InBall.smul hu zero_le_one (inBall_ne S T)
  have h2 := InBall.add (by positivity) (by positivity)
    (fun c d => mul_nonneg hu (by split_ifs <;> norm_num)) hY0 h1 hY
  refine (h2.mono (fun c d => add_nonneg (mul_nonneg hu (by split_ifs <;> norm_num)) (hY0 c d))
    fun c hc d hd hcd => ?_).weaken hN (by nlinarith)
  simpa [hcd] using hW c hc d hd hcd

/-- A greedy factor. -/
theorem BMix.mul_dom (hN' : 0 ≤ N') (hW0 : ∀ c d, 0 ≤ W c d) (hd : Dominant S T W' N')
    (h : BMix S T W N) : BMix S T (fun c d => W' c d * W c d) (N' * N) := by
  obtain ⟨u, v, Y, hu, hv, hN, hY0, hY, hW⟩ := h
  refine ⟨N' * u, N' * v, fun c d => N' * Y c d, mul_nonneg hN' hu, mul_nonneg hN' hv,
    by nlinarith, fun c d => mul_nonneg hN' (hY0 c d), ?_, fun c hc d hd' hcd => ?_⟩
  · have := InBall.smul hN' (by positivity) hY
    rwa [← mul_assoc] at this
  · have h1 := hW c hc d hd' hcd
    have h2 := hd c hc d hd' hcd
    calc N' * u + N' * Y c d = N' * (u + Y c d) := by ring
      _ ≤ N' * W c d := mul_le_mul_of_nonneg_left h1 hN'
      _ ≤ W' c d * W c d := mul_le_mul_of_nonneg_right h2 (hW0 c d)

/-- **Products.** -/
theorem BMix.mul (hN' : 0 ≤ N') (h : BMix S T W N) (h' : BMix S T W' N') :
    BMix S T (fun c d => W c d * W' c d) (N * N') := by
  obtain ⟨u, v, Y, hu, hv, hNuv, hY0, hY, hW⟩ := h
  obtain ⟨u', v', Y', hu', hv', hNuv', hY0', hY', hW'⟩ := h'
  have a1 : InBall S T (fun c d => u * Y' c d) (u * (v' * (17 / 16))) :=
    InBall.smul hu (by positivity) hY'
  have a2 : InBall S T (fun c d => u' * Y c d) (u' * (v * (17 / 16))) :=
    InBall.smul hu' (by positivity) hY
  have a3 : InBall S T (fun c d => Y c d * Y' c d) (v * v' * (17 / 16)) :=
    (hY.mul (by positivity) (by positivity) hY').weaken (by positivity) (by nlinarith)
  have a12 := InBall.add (by positivity) (by positivity) (fun c d => mul_nonneg hu (hY0' c d))
    (fun c d => mul_nonneg hu' (hY0 c d)) a1 a2
  have a123 := InBall.add (by positivity) (by positivity)
    (fun c d => add_nonneg (mul_nonneg hu (hY0' c d)) (mul_nonneg hu' (hY0 c d)))
    (fun c d => mul_nonneg (hY0 c d) (hY0' c d)) a12 a3
  refine ⟨u * u', u * v' + u' * v + v * v',
    fun c d => u * Y' c d + u' * Y c d + Y c d * Y' c d, mul_nonneg hu hu', by positivity,
    ?_, fun c d => by have := hY0 c d; have := hY0' c d; positivity, ?_, ?_⟩
  · calc N * N' ≤ (u + v) * (u' + v') := mul_le_mul hNuv hNuv' hN' (by linarith)
      _ = _ := by ring
  · have e : (u * v' + u' * v + v * v') * (17 / 16)
        = u * (v' * (17 / 16)) + u' * (v * (17 / 16)) + v * v' * (17 / 16) := by ring
    rw [e]
    exact a123
  · intro c hc d hd hcd
    have h1 := hW c hc d hd hcd
    have h2 := hW' c hc d hd hcd
    have hy := hY0 c d
    have hy' := hY0' c d
    calc u * u' + (u * Y' c d + u' * Y c d + Y c d * Y' c d) = (u + Y c d) * (u' + Y' c d) := by
          ring
      _ ≤ W c d * W' c d := mul_le_mul h1 h2 (by positivity) (by linarith)

/-- **Sums.** -/
theorem BMix.add (h : BMix S T W N) (h' : BMix S T W' N') :
    BMix S T (fun c d => W c d + W' c d) (N + N') := by
  obtain ⟨u, v, Y, hu, hv, hNuv, hY0, hY, hW⟩ := h
  obtain ⟨u', v', Y', hu', hv', hNuv', hY0', hY', hW'⟩ := h'
  have hs := InBall.add (by positivity) (by positivity) hY0 hY0' hY hY'
  refine ⟨u + u', v + v', fun c d => Y c d + Y' c d, by positivity, by positivity, by linarith,
    fun c d => add_nonneg (hY0 c d) (hY0' c d), by rw [add_mul]; exact hs,
    fun c hc d hd hcd => ?_⟩
  have h1 := hW c hc d hd hcd
  have h2 := hW' c hc d hd hcd
  show u + u' + (Y c d + Y' c d) ≤ W c d + W' c d
  linarith

theorem BMix.finsum {ι : Type*} (s : Finset ι) (W : ι → ℕ → ℕ → ℝ) (N : ι → ℝ)
    (h0 : ∀ i ∈ s, ∀ c d, 0 ≤ W i c d) (h : ∀ i ∈ s, BMix S T (W i) (N i)) :
    BMix S T (fun c d => ∑ i ∈ s, W i c d) (∑ i ∈ s, N i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact BMix.zero fun _ _ => le_refl 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact BMix.add (h a (mem_insert_self a s))
      (ih (fun i hi => h0 i (mem_insert_of_mem hi)) fun i hi => h i (mem_insert_of_mem hi))

/-! ### The table of a deficient bare even face -/

/-- The six cells of a matched family: at most one in the row and one in the column of the
deficient pair. -/
theorem six_lv : ∀ r₀ r₁ r₂ s₀ s₁ s₂ : Bool,
    (r₀ && r₁) = false → (r₀ && r₂) = false → (r₁ && r₂) = false →
    (s₀ && s₁) = false → (s₀ && s₂) = false → (s₁ && s₂) = false →
    1152 ≤ lv r₀ s₁ * lv r₀ s₂ * lv r₁ s₀ * lv r₁ s₂ * lv r₂ s₀ * lv r₂ s₁ := by
  decide

/-- A matched family has `lvZ`-product at least `128/81`. -/
theorem lvZ_six {p q : Fin 6 → ℕ} (hm : Matched S T p q) (a b : ℕ) :
    (128 / 81 : ℝ) ≤ ∏ i, lvZ a b (p i) (q i) := by
  obtain ⟨α, β, hα, hβ, -, -, hab⟩ := hm
  obtain ⟨κ, hκb, hκ⟩ := matched_reindex hα hβ hab
  rw [← Fintype.prod_bijective κ hκb (fun j => lvZ a b (p (κ j)) (q (κ j))) _ fun _ => rfl]
  have hr : ∀ {x y : Fin 3}, x ≠ y → (decide (α x = a) && decide (α y = a)) = false :=
    fun hxy => bool_two fun h1 h2 => hxy (hα (h1.trans h2.symm))
  have hs : ∀ {x y : Fin 3}, x ≠ y → (decide (β x = b) && decide (β y = b)) = false :=
    fun hxy => bool_two fun h1 h2 => hxy (hβ (h1.trans h2.symm))
  have key := six_lv _ _ _ _ _ _ (hr (by decide : (0 : Fin 3) ≠ 1))
    (hr (by decide : (0 : Fin 3) ≠ 2)) (hr (by decide : (1 : Fin 3) ≠ 2))
    (hs (by decide : (0 : Fin 3) ≠ 1)) (hs (by decide : (0 : Fin 3) ≠ 2))
    (hs (by decide : (1 : Fin 3) ≠ 2))
  have key' : (1152 : ℝ) ≤ (lv (decide (α 0 = a)) (decide (β 1 = b)) : ℝ)
      * lv (decide (α 0 = a)) (decide (β 2 = b)) * lv (decide (α 1 = a)) (decide (β 0 = b))
      * lv (decide (α 1 = a)) (decide (β 2 = b)) * lv (decide (α 2 = a)) (decide (β 0 = b))
      * lv (decide (α 2 = a)) (decide (β 1 = b)) := by exact_mod_cast key
  simp only [Fin.prod_univ_six, hκ, offPair, lvZ]
  simp only [Matrix.cons_val]
  have e : ∀ x₁ x₂ x₃ x₄ x₅ x₆ : ℝ, x₁ / 3 * (x₂ / 3) * (x₃ / 3) * (x₄ / 3) * (x₅ / 3) * (x₆ / 3)
      = x₁ * x₂ * x₃ * x₄ * x₅ * x₆ / 729 := fun _ _ _ _ _ _ => by ring
  rw [e, le_div_iff₀ (by norm_num)]
  calc (128 / 81 : ℝ) * 729 = 1152 := by norm_num
    _ ≤ _ := by exact_mod_cast key

theorem lvZ_bounds (a b c e : ℕ) : 2 / 3 ≤ lvZ a b c e ∧ lvZ a b c e ≤ 4 / 3 := by
  unfold lvZ
  rw [lv_cast]
  constructor <;> split_ifs <;> norm_num

/-- **The table of a deficient bare even face is in the ball class with constant `17/16`.** -/
theorem lvZ_ball (S T : Finset ℕ) (a b : ℕ) : InBall S T (lvZ a b) (17 / 16) := by
  intro p q hm hpq j c _ d _ _
  set X := ∏ k ∈ univ.erase j, lvZ a b (p k) (q k)
  set y := lvZ a b (p j) (q j)
  set z := lvZ a b c d
  have hy := lvZ_bounds a b (p j) (q j)
  have hz := lvZ_bounds a b c d
  have hy0 : 0 < y := by linarith [hy.1]
  have hP : X * y = ∏ k, lvZ a b (p k) (q k) := by
    rw [mul_comm]
    exact Finset.mul_prod_erase univ (fun k => lvZ a b (p k) (q k)) (mem_univ j)
  have h6 := lvZ_six hm a b
  rw [← hP] at h6
  have hX0 : 0 ≤ X := prod_nonneg fun k _ => by linarith [(lvZ_bounds a b (p k) (q k)).1]
  have hnum : (17 / 16 : ℝ) ^ 600 * (4 / 3) ^ 9 ≤ (128 / 81) ^ 100 * (2 / 3) ^ 9 := by
    rw [show (600 : ℕ) = 6 * 100 from rfl, pow_mul]
    norm_num
  refine le_of_mul_le_mul_right ?_ (pow_pos hy0 9)
  calc (17 / 16 : ℝ) ^ 600 * y ^ 9 ≤ (17 / 16) ^ 600 * (4 / 3) ^ 9 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy0.le hy.2 9) (by norm_num)
    _ ≤ (128 / 81) ^ 100 * (2 / 3) ^ 9 := hnum
    _ ≤ (X * y) ^ 100 * z ^ 9 :=
        mul_le_mul (pow_le_pow_left₀ (by norm_num) h6 100) (pow_le_pow_left₀ (by norm_num) hz.1 9)
          (by norm_num) (pow_nonneg (mul_nonneg hX0 hy0.le) _)
    _ = X ^ 100 * y ^ 91 * z ^ 9 * y ^ 9 := by ring

/-! ### Bare even faces -/

/-- The mixture of the constant and `lvZ a b`. -/
theorem bmix_of_low {α K : ℝ} (hα : 3 ≤ α) (hK : 0 ≤ K) {a b : ℕ}
    (h : ∀ c ∈ S, ∀ d ∈ T, c ≠ d →
      K * (α - 1 + (if c ≠ a then 1 else 0) + (if d ≠ b then 1 else 0)) ≤ W c d) :
    BMix S T W (α * K) := by
  refine ⟨K * (α - 3), 3 * K, fun c e => 3 * K * lvZ a b c e, by nlinarith, by positivity,
    by nlinarith, fun c e => by unfold lvZ; positivity, ?_, fun c hc d hd hcd => ?_⟩
  · have := InBall.smul (by positivity : (0 : ℝ) ≤ 3 * K) (by norm_num) (lvZ_ball S T a b)
    exact this
  · refine le_trans (le_of_eq ?_) (h c hc d hd hcd)
    simp only [lvZ]
    rw [lv_cast]
    ring

/-- **A bare square is in the mixture class.** -/
theorem bmix_square (Lu Lv : Finset ℕ) (Li : Fin 2 → Finset ℕ) (hLi : ∀ j, (Li j).card = 3)
    (E : Fin 3 → ℕ → ℕ → ℝ) (hE0 : ∀ j c d, 0 ≤ E j c d) (A : Fin 3 → ℝ) (hA : ∀ j, 0 ≤ A j)
    (hE : ∀ j, Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    BMix Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 2 * ∏ j, A j) := by
  have hP0 : 0 ≤ ∏ j, A j := Finset.prod_nonneg fun j _ => hA j
  have h3 : faceConst3 2 = 3 := by norm_num [faceConst3]
  have hW : ∀ c ∈ Lu, ∀ d ∈ Lv,
      (∏ j, A j) * bsq (Li 0) (Li 1) c d ≤ faceSum Li (fun _ _ => 1) E c d := by
    intro c hc d hd
    have := faceSum_ge_bare Lu Lv Li E hE0 A hA hE hc hd
    rw [faceSum_two Li (fun _ => neP)] at this
    exact this
  by_cases hall : ∀ c ∈ Lu, ∀ d ∈ Lv, c ≠ d → 3 ≤ bsq (Li 0) (Li 1) c d
  · refine BMix.of_dom (by rw [h3]; positivity) fun c hc d hd hcd => ?_
    rw [h3]
    calc 3 * ∏ j, A j = (∏ j, A j) * 3 := mul_comm _ _
      _ ≤ (∏ j, A j) * bsq (Li 0) (Li 1) c d := mul_le_mul_of_nonneg_left (hall c hc d hd hcd) hP0
      _ ≤ _ := hW c hc d hd
  · push Not at hall
    obtain ⟨a, -, b, -, hab, hlt⟩ := hall
    rw [h3]
    refine bmix_of_low (le_refl 3) hP0 (a := a) (b := b) fun c hc d hd hcd => ?_
    have := bsq_low (hLi 0) (hLi 1) hab hlt hcd
    calc (∏ j, A j) * (3 - 1 + (if c ≠ a then 1 else 0) + (if d ≠ b then 1 else 0))
        = (∏ j, A j) * (2 + (if c ≠ a then 1 else 0) + (if d ≠ b then 1 else 0)) := by ring
      _ ≤ (∏ j, A j) * bsq (Li 0) (Li 1) c d := mul_le_mul_of_nonneg_left this hP0
      _ ≤ _ := hW c hc d hd

/-- **A bare even face of length at least six is in the mixture class.** -/
theorem bmix_even_long {m : ℕ} (hm : Even m) (hm4 : 4 ≤ m) (Lu Lv : Finset ℕ)
    (Li : Fin m → Finset ℕ) (hLu : Lu.card = 3) (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3)
    (E : Fin (m + 1) → ℕ → ℕ → ℝ) (hE0 : ∀ j c d, 0 ≤ E j c d) (A : Fin (m + 1) → ℝ)
    (hA : ∀ j, 0 ≤ A j)
    (hE : ∀ j, Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    BMix Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j) := by
  have hP0 : 0 ≤ ∏ j, A j := Finset.prod_nonneg fun j _ => hA j
  have hcount : ∀ c ∈ Lu, ∀ d ∈ Lv, (∏ j, A j) * psum (List.ofFn Li ++ [Lv]) (nes (m + 1)) c d
      ≤ faceSum Li (fun _ _ => 1) E c d := fun c hc d hd => by
    have h1 := faceSum_ge_bare Lu Lv Li E hE0 A hA hE hc hd
    have h2 : faceSum Li (fun _ _ => 1) (fun _ => neP) c d
        = psum (List.ofFn Li ++ [Lv]) (nes (m + 1)) c d := by
      rw [faceSum_eq_psum Li Lv _ c d hd, List.ofFn_const]
      rfl
    rwa [h2] at h1
  have hcard : ∀ L ∈ List.ofFn Li, L.card = 3 := fun L hL => by
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp hL
    exact hLi i
  obtain ⟨ψ, hψ, hψm⟩ := exists_enum hLv
  obtain ⟨φ, δs, hφ, hφm, hlen, hle, hkeep⟩ :=
    psum_aligned (List.ofFn Li) Lv ψ hcard hψ hψm Lu hLu
  rw [List.length_ofFn] at hlen hle
  have hodd : Odd δs.length := by
    rw [hlen]; obtain ⟨k, hk⟩ := hm; exact ⟨k, by omega⟩
  have hα : faceConst3 m = (dN (m + 1) : ℝ) := faceConst3_eq_dN m
  have hprop : ∀ i l, φ i ≠ ψ l → (i ≠ l ∨ ∃ δ ∈ δs, δ i = true) := fun i l hne => by
    by_cases hil : i = l
    · subst hil
      right
      by_contra hc
      push Not at hc
      exact hne (hkeep i fun δ hδ => by simpa using hc δ hδ)
    · exact Or.inl hil
  have hα3 : (3 : ℝ) ≤ faceConst3 m := by
    obtain ⟨k, hk⟩ := hm
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [hk, show k' + 1 + (k' + 1) = 2 * k' + 2 by ring]
    exact faceConst3_even_ge_three k'
  rcases amat_long δs hodd (by omega) with hall | ⟨x, hx⟩
  · refine BMix.of_dom (by positivity) fun c hc d hd hcd => ?_
    obtain ⟨i, rfl⟩ := enum_surj hLu hφ hφm hc
    obtain ⟨l, rfl⟩ := enum_surj hLv hψ hψm hd
    have h1 : (dN (m + 1) : ℝ) ≤ amat δs i l := by
      have := hall i l (hprop i l hcd)
      rw [hlen] at this
      exact_mod_cast this
    calc faceConst3 m * ∏ j, A j = (∏ j, A j) * dN (m + 1) := by rw [hα, mul_comm]
      _ ≤ (∏ j, A j) * psum (List.ofFn Li ++ [Lv]) (nes (m + 1)) (φ i) (ψ l) :=
          mul_le_mul_of_nonneg_left (h1.trans (hle i l)) hP0
      _ ≤ _ := hcount _ hc _ hd
  · refine bmix_of_low hα3 hP0 (a := φ x) (b := ψ x) fun c hc d hd hcd => ?_
    obtain ⟨i, rfl⟩ := enum_surj hLu hφ hφm hc
    obtain ⟨l, rfl⟩ := enum_surj hLv hψ hψm hd
    have hpar : dN (m + 1) = sN (m + 1) + 1 := by
      have := (sN_dN_parity (m + 1)).2 (by rw [← hlen]; exact hodd)
      exact this
    have h1 := hx i l (hprop i l hcd)
    rw [hlen] at h1
    have e1 : (if φ i ≠ φ x then (1 : ℝ) else 0) = if i ≠ x then 1 else 0 := by
      by_cases h : i = x
      · simp [h]
      · have : φ i ≠ φ x := fun e => h (hφ e)
        simp [h, this]
    have e2 : (if ψ l ≠ ψ x then (1 : ℝ) else 0) = if l ≠ x then 1 else 0 := by
      by_cases h : l = x
      · simp [h]
      · have : ψ l ≠ ψ x := fun e => h (hψ e)
        simp [h, this]
    have h2 : faceConst3 m - 1 + (if i ≠ x then (1 : ℝ) else 0) + (if l ≠ x then 1 else 0)
        ≤ amat δs i l := by
      rw [hα]
      have : ((dN (m + 1) : ℕ) : ℝ) = (sN (m + 1) : ℝ) + 1 := by exact_mod_cast hpar
      rw [this]
      have h1' : ((sN (m + 1) + (if i ≠ x then 1 else 0) + (if l ≠ x then 1 else 0) : ℕ) : ℝ)
          ≤ amat δs i l := by exact_mod_cast h1
      push_cast at h1'
      convert h1' using 2; split_ifs <;> simp
    rw [e1, e2]
    calc (∏ j, A j) * (faceConst3 m - 1 + (if i ≠ x then 1 else 0) + (if l ≠ x then 1 else 0))
        ≤ (∏ j, A j) * psum (List.ofFn Li ++ [Lv]) (nes (m + 1)) (φ i) (ψ l) :=
          mul_le_mul_of_nonneg_left (h2.trans (hle i l)) hP0
      _ ≤ _ := hcount _ hc _ hd

/-- **Every bare even face is in the mixture class**, with its ordinary constant. -/
theorem bmix_even_bare {m : ℕ} (hm : Even m) (hm2 : 2 ≤ m) (Lu Lv : Finset ℕ)
    (Li : Fin m → Finset ℕ) (hLu : Lu.card = 3) (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3)
    (E : Fin (m + 1) → ℕ → ℕ → ℝ) (hE0 : ∀ j c d, 0 ≤ E j c d) (A : Fin (m + 1) → ℝ)
    (hA : ∀ j, 0 ≤ A j)
    (hE : ∀ j, Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    BMix Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j) := by
  rcases Nat.lt_or_ge m 4 with h | h
  · obtain rfl : m = 2 := by obtain ⟨k, hk⟩ := hm; omega
    exact bmix_square Lu Lv Li hLi E hE0 A hA hE
  · exact bmix_even_long hm h Lu Lv Li hLu hLv hLi E hE0 A hA hE

/-! ### Vertex lifts -/

/-- **A vertex lift keeps the mixture class**, with the constant doubled. -/
theorem lift_bmix (hS : S.card = 3) (hT : T.card = 3) (hU : U.card = 3)
    (h : BMix S T X A) : BMix S U (fun c _ => liftV T X c) (2 * A) := by
  obtain ⟨u, v, Y, hu, hv, hN, hY0, hY, hW⟩ := h
  refine ⟨2 * u, 2 * v, fun c _ => liftV T Y c, by positivity, by positivity, by linarith,
    fun c _ => liftV_nonneg hY0 c, ?_, fun c hc d _ _ => ?_⟩
  · have := lift_ball (U := U) hS hT hU hY0 (by positivity) hY
    rwa [show 2 * (v * (17 / 16)) = 2 * v * (17 / 16) by ring] at this
  · have hle : ∑ e ∈ T, (if c ≠ e then u + Y c e else 0) ≤ liftV T X c :=
      Finset.sum_le_sum fun e he => by
        split_ifs with hce
        · exact hW c hc e he hce
        · exact le_refl 0
    have hn := card_filter_ne hT c
    have hsum : ∑ e ∈ T, (if c ≠ e then u + Y c e else 0)
        = ((T.filter fun e => c ≠ e).card : ℝ) * u + liftV T Y c := by
      unfold liftV
      rw [← Finset.sum_filter, ← Finset.sum_filter, ← nsmul_eq_mul, ← Finset.sum_const,
        ← Finset.sum_add_distrib]
    have hn' : (2 : ℝ) ≤ (T.filter fun e => c ≠ e).card := by exact_mod_cast hn
    show 2 * u + liftV T Y c ≤ liftV T X c
    nlinarith

end Outerplanar
