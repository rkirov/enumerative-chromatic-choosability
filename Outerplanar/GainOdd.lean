/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.GainBare
import Outerplanar.NumTags

/-!
# The gain class through odd faces

An odd face with one path edge in the gain class `Gain1` (`Outerplanar/Gain.lean`) and greedy
profiles elsewhere is in the gain class (`gain1_odd`). The face map is linear in the loaded side,
so the constant alternative goes to a greedy profile and the table `Z` to the normalized face
`Z'` of `Z` over bare sides:

* floor `2/3`: an odd face is transparent to floors (`dom_face_bare`, `oddB m = α`);
* four-cell bound `3/4`: the one-side transport lemma (`tb_transport`, no loss at odd faces);
* bijections `≥ 32/27`: at a face of length at least five the rank-one bound is homogeneous
  (`hasPot_face3` with the constant `(32/27)^(1/3)`); at a triangle, Hall's condition
  (`hasPot_tri`) with the four-cell constants `(3/4)(27/32)` and `1`, since
  `2 · (81/128) ≥ 1`.

From the research note `ai_research_notes/OUTERPLANAR_SEVEN_AND_CUTS_2026-11-23.md` ("A gain
from a single even face"); formalized by Claude.
-/

namespace Outerplanar

open Finset

/-! ### Small facts -/

theorem Gain1.mul_dom {S T : Finset ℕ} {W W' : ℕ → ℕ → ℝ} {A A' : ℝ} (hA : 0 ≤ A) (hA' : 0 ≤ A')
    (h : Gain1 S T W A) (h' : Dominant S T W' A') :
    Gain1 S T (fun c d => W' c d * W c d) (A' * A) := by
  obtain ⟨t, Z, ht0, ht1, hZ, hW⟩ := h
  refine ⟨t, Z, ht0, ht1, hZ, fun c hc d hd hcd => ?_⟩
  have hm : 0 ≤ (1 - t) + t * Z c d := add_nonneg (by linarith) (mul_nonneg ht0 (hZ.1 c d))
  calc A' * A * ((1 - t) + t * Z c d) = A' * (A * ((1 - t) + t * Z c d)) := by ring
    _ ≤ W' c d * W c d := mul_le_mul (h' c hc d hd hcd) (hW c hc d hd hcd)
        (mul_nonneg hA hm) (hA'.trans (h' c hc d hd hcd))

theorem BijGe.div {S T : Finset ℕ} {W : ℕ → ℕ → ℝ} {N Q : ℝ} (hN : 0 < N) (h : BijGe S T W N Q) :
    BijGe S T (fun c d => W c d / N) 1 Q := fun α β hα hβ hαm hβm hne => by
  have := h α β hα hβ hαm hβm hne
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    le_div_iff₀ (pow_pos hN 3)]
  linarith

theorem TB.rescale {S T : Finset ℕ} {W : ℕ → ℕ → ℝ} {τ κ : ℝ} (hκ : 0 < κ) (h : TB S T W 1 τ) :
    TB S T W κ (τ / κ ^ 3) := fun p q hm hpq i j k l hij hik hil hjk hjl hkl => by
  have := h p q hm hpq i j k l hij hik hil hjk hjl hkl
  have e : (τ / κ ^ 3) ^ 2 * κ ^ 6 = τ ^ 2 * 1 ^ 6 := by
    field_simp
  rw [e]
  exact this

/-- The face map is linear in one path edge. -/
theorem faceSum_slot {m : ℕ} (Li : Fin m → Finset ℕ) (j₀ : Fin (m + 1)) (X Y : ℕ → ℕ → ℝ)
    (a b : ℝ) (c d : ℕ) :
    faceSum Li (fun _ _ => 1) (fun j => if j = j₀ then (fun x y => a * X x y + b * Y x y)
        else fun x y => if x ≠ y then 1 else 0) c d
      = a * faceSum Li (fun _ _ => 1)
          (fun j => if j = j₀ then X else fun x y => if x ≠ y then 1 else 0) c d
        + b * faceSum Li (fun _ _ => 1)
          (fun j => if j = j₀ then Y else fun x y => if x ≠ y then 1 else 0) c d := by
  unfold faceSum
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun g _ => ?_
  have h : ∀ Z : ℕ → ℕ → ℝ, ∏ j : Fin (m + 1),
      (if j = j₀ then Z else fun x y => if x ≠ y then (1 : ℝ) else 0)
        (pathCol c d g j.castSucc) (pathCol c d g j.succ)
      = Z (pathCol c d g j₀.castSucc) (pathCol c d g j₀.succ)
        * ∏ j ∈ univ.erase j₀, (if pathCol c d g j.castSucc ≠ pathCol c d g j.succ then (1 : ℝ)
          else 0) := fun Z => by
    rw [← Finset.mul_prod_erase univ _ (mem_univ j₀)]
    simp only [ite_true]
    congr 1
    exact Finset.prod_congr rfl fun j hj => by simp only [Finset.ne_of_mem_erase hj, ↓reduceIte]
  rw [h, h, h]
  ring

/-! ### Odd faces -/

/-- **An odd face with one singly marked side is in the gain class.** -/
theorem gain1_odd {m : ℕ} (hm : Odd m) (Lu Lv : Finset ℕ) (Li : Fin m → Finset ℕ)
    (hLu : Lu.card = 3) (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3) (j₀ : Fin (m + 1))
    (E : Fin (m + 1) → ℕ → ℕ → ℝ) (hE0 : ∀ j c d, 0 ≤ E j c d) (A : Fin (m + 1) → ℝ)
    (hA : ∀ j, 0 < A j)
    (hG : Gain1 (pathList Lu Lv Li j₀.castSucc) (pathList Lu Lv Li j₀.succ) (E j₀) (A j₀))
    (hD : ∀ j, j ≠ j₀ →
      Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    Gain1 Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j) := by
  obtain ⟨t, Z, ht0, ht1, hZ, hEZ⟩ := hG
  obtain ⟨hZ0, hZD, hZB, hZT⟩ := hZ
  set Zm : ℕ → ℕ → ℝ := fun x y => if x ≠ y then Z x y else 0 with hZm
  have hZm0 : ∀ x y, 0 ≤ Zm x y := fun x y => by
    simp only [hZm]; split_ifs
    · exact hZ0 x y
    · exact le_refl 0
  set S₀ := pathList Lu Lv Li j₀.castSucc with hS₀
  set T₀ := pathList Lu Lv Li j₀.succ with hT₀
  have hZmD : Dominant S₀ T₀ Zm (2 / 3) := fun c hc d hd hcd => by
    simp only [hZm, ne_eq, hcd, not_false_eq_true, ite_true]; exact hZD c hc d hd hcd
  have hZmB : BijGe S₀ T₀ Zm 1 (32 / 27) := fun α β hα hβ hαm hβm hne => by
    simp only [hZm, ne_eq, hne, not_false_eq_true, ite_true]; exact hZB α β hα hβ hαm hβm hne
  have hZmT : TB S₀ T₀ Zm 1 (3 / 4) := fun p q hm' hpq i j k l hij hik hil hjk hjl hkl => by
    simp only [hZm, ne_eq, hpq, not_false_eq_true, ite_true]
    exact hZT p q hm' hpq i j k l hij hik hil hjk hjl hkl
  have hcard : ∀ i : Fin (m + 2), (pathList Lu Lv Li i).card = 3 := fun i => by
    refine Fin.cases hLu (fun i => ?_) i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa [pathList] using hLv
    · simpa [pathList] using hLi i
  set α := faceConst3 m with hα
  have hαpos : 0 < α := faceConst3_pos m
  have hoddB : oddB m = α := by
    have := oddB_div_odd hm
    rw [div_eq_one_iff_eq hαpos.ne'] at this
    exact this
  -- the face of `Z` over bare sides
  set Ez : Fin (m + 1) → ℕ → ℕ → ℝ :=
    fun j => if j = j₀ then Zm else fun x y => if x ≠ y then 1 else 0 with hEz
  have hEz0 : ∀ j c d, 0 ≤ Ez j c d := fun j c d => by
    by_cases hj : j = j₀
    · simp only [hEz, hj, ite_true]; exact hZm0 c d
    · simp only [hEz, hj, ite_false]; split_ifs <;> norm_num
  set Fz := faceSum Li (fun _ _ => 1) Ez with hFz
  have hFz0 : ∀ c d, 0 ≤ Fz c d := faceSum_nonneg _ _ _ (fun _ _ _ => zero_le_one) hEz0
  set Z' : ℕ → ℕ → ℝ := fun c d => Fz c d / α with hZ'
  -- floor
  have hfl : Dominant Lu Lv Fz (2 / 3 * α) := by
    have h := dom_face_bare Lu Lv Li hLi Ez hEz0 (fun j => if j = j₀ then 2 / 3 else 1)
      (fun j => by split_ifs <;> norm_num) fun j => by
        by_cases hj : j = j₀
        · subst hj; simp only [hEz, ite_true]; exact hZmD
        · simp only [hEz, hj, ite_false]; exact dominant_ne _ _
    simp only [Finset.prod_ite_eq', mem_univ, ↓reduceIte] at h
    rw [hoddB] at h
    exact fun c hc d hd hcd => le_trans (le_of_eq (by ring)) (h c hc d hd hcd)
  -- bijections
  have hκpos : 0 < (32 / 27 : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos (by norm_num) _
  have hκ3 : ((32 / 27 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = 32 / 27 := rpow_third_cube (by norm_num)
  have hZmP : HasPot S₀ T₀ Zm (1 * (32 / 27 : ℝ) ^ ((1 : ℝ) / 3)) :=
    hZmB.hasPot (hcard _) (hcard _) one_pos (by norm_num) fun c hc d hd hcd =>
      lt_of_lt_of_le (by norm_num) (hZmD c hc d hd hcd)
  rw [one_mul] at hZmP
  set κ := (32 / 27 : ℝ) ^ ((1 : ℝ) / 3) with hκ
  have hsideP : ∀ j, HasPot (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (Ez j)
      (if j = j₀ then κ else 1) := fun j => by
    by_cases hj : j = j₀
    · subst hj; simp only [hEz, ite_true]; exact hZmP
    · simp only [hEz, hj, ite_false]; exact hasPot_ne _ _
  have hprodκ : ∏ j : Fin (m + 1), (if j = j₀ then κ else 1) = κ := by
    simp only [Finset.prod_ite_eq', mem_univ, ↓reduceIte]
  have hbij : BijGe Lu Lv Fz α (32 / 27) := by
    rcases Nat.lt_or_ge m 3 with hlt | h3
    · obtain rfl : m = 1 := by obtain ⟨k, hk⟩ := hm; omega
      have h1 : faceConst3 1 = 1 := faceConst3_one
      have hT : ∀ j : Fin 2, TB (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (Ez j)
          (if j = j₀ then κ else 1) (if j = j₀ then (3 / 4) / κ ^ 3 else 1) := fun j => by
        by_cases hj : j = j₀
        · subst hj; simp only [hEz, ite_true]; exact hZmT.rescale hκpos
        · simp only [hEz, hj, ite_false]; exact (dominant_ne _ _).tb zero_le_one
      have h2 : 1 ≤ 2 * ((if (0 : Fin 2) = j₀ then (3 / 4) / κ ^ 3 else 1)
          * (if (1 : Fin 2) = j₀ then (3 / 4) / κ ^ 3 else 1)) := by
        rw [hκ3]
        fin_cases j₀ <;> simp <;> norm_num
      have hP := hasPot_tri hLu hLv hLi hEz0 (fun j => by split_ifs; exact hκpos; exact one_pos)
        hsideP hT h2
      rw [hprodκ] at hP
      have := (hP.bijGe hLu hLv hκpos.le)
      rw [show κ = 1 * κ by ring] at this
      have h' := this.of_one
      rw [hκ3] at h'
      rw [hα, h1]
      exact h'
    · have hP := hasPot_face3 (by omega) Lu Lv Li hLu hLv hLi Ez hEz0 _
        (fun j => by split_ifs; exact hκpos; exact one_pos) hsideP
      rw [hprodκ] at hP
      have h' := (hP.bijGe hLu hLv (mul_pos hαpos hκpos).le).of_one
      rw [hκ3] at h'
      exact h'
  -- four cells
  have htb : TB Lu Lv Fz α (3 / 4) := by
    have h := tb_transport m Lu Lv Li hLv hLi j₀ Ez hEz0 (fun _ => 1) (fun _ => one_pos)
      (by simp only [hEz, ite_true]; exact hZmT)
      (fun j hj => by simp only [hEz, hj, ite_false]; exact dominant_ne _ _)
    have hodd' : ¬ Even m := Nat.not_even_iff_odd.mpr hm
    rw [dd_face] at h
    simp only [hodd', ↓reduceIte, sub_zero] at h
    rw [div_self hαpos.ne', one_pow, mul_one, Finset.prod_const_one, mul_one] at h
    exact h
  have hZ'good : ZGood Lu Lv Z' := by
    refine ⟨fun c d => div_nonneg (hFz0 c d) hαpos.le, fun c hc d hd hcd => ?_,
      hbij.div hαpos, ?_⟩
    · rw [hZ', le_div_iff₀ hαpos]
      exact hfl c hc d hd hcd
    · have := htb.div hαpos
      exact this
  -- the mixture
  refine ⟨t, Z', ht0, ht1, hZ'good, fun c hc d hd hcd => ?_⟩
  set K := ∏ j ∈ univ.erase j₀, A j with hK
  have hKpos : 0 < K := Finset.prod_pos fun j _ => hA j
  have hbare := faceSum_bare_mul_le j₀ hE0 (fun j => (hA j).le) hD hc hd
  set Emix : ℕ → ℕ → ℝ := fun x y => A j₀ * (1 - t) * (if x ≠ y then 1 else 0) + A j₀ * t * Zm x y
    with hEmix
  have hmix_le : faceSum Li (fun _ _ => 1) (fun j => if j = j₀ then Emix
        else fun x y => if x ≠ y then 1 else 0) c d
      ≤ faceSum Li (fun _ _ => 1) (fun j => if j = j₀ then E j₀
        else fun x y => if x ≠ y then 1 else 0) c d := by
    refine faceSum_le_of_le (fun j x y => ?_) (fun j x hx y hy => ?_) hc hd
    · by_cases hj : j = j₀
      · simp only [hj, ite_true, hEmix]
        exact add_nonneg (mul_nonneg (mul_nonneg (hA j₀).le (by linarith)) (by split_ifs <;> norm_num))
          (mul_nonneg (mul_nonneg (hA j₀).le ht0) (hZm0 x y))
      · simp only [hj, ite_false]; split_ifs <;> norm_num
    · by_cases hj : j = j₀
      · subst hj
        simp only [ite_true, hEmix, hZm]
        by_cases hxy : x = y
        · simp only [hxy, ne_eq, not_true_eq_false, ite_false, mul_zero, add_zero]
          exact hE0 _ _ _
        · simp only [ne_eq, hxy, not_false_eq_true, ite_true, mul_one]
          have := hEZ x hx y hy hxy
          linarith
      · simp only [hj, ite_false, le_refl]
  have hlin := faceSum_slot Li j₀ (fun x y => if x ≠ y then 1 else 0) Zm (A j₀ * (1 - t))
    (A j₀ * t) c d
  have hF1 : α ≤ faceSum Li (fun _ _ => 1) (fun j => if j = j₀ then
      (fun x y => if x ≠ y then (1 : ℝ) else 0) else fun x y => if x ≠ y then 1 else 0) c d := by
    have h := dom_face_bare Lu Lv Li hLi (fun j => if j = j₀ then
      (fun x y => if x ≠ y then (1 : ℝ) else 0) else fun x y => if x ≠ y then 1 else 0)
      (fun j x y => by simp only [ite_self]; split_ifs <;> norm_num) (fun _ => 1)
      (fun _ => zero_le_one) (fun j => by simp only [ite_self]; exact dominant_ne _ _) c hc d hd hcd
    rw [Finset.prod_const_one, mul_one, hoddB] at h
    exact h
  have hEmix_eq : (fun j => if j = j₀ then Emix else fun x y => if x ≠ y then (1 : ℝ) else 0)
      = fun j => if j = j₀ then (fun x y => A j₀ * (1 - t) * (if x ≠ y then 1 else 0)
          + A j₀ * t * Zm x y) else fun x y => if x ≠ y then 1 else 0 := rfl
  rw [hEmix_eq, hlin] at hmix_le
  have hZc : Fz c d = α * Z' c d := by
    rw [hZ']; field_simp
  have hprod : ∏ j, A j = A j₀ * K := by
    rw [hK, Finset.mul_prod_erase univ A (mem_univ j₀)]
  rw [hprod]
  have h1t : 0 ≤ 1 - t := by linarith
  have hA0 := (hA j₀).le
  calc α * (A j₀ * K) * ((1 - t) + t * Z' c d)
      = K * (A j₀ * (1 - t) * α + A j₀ * t * (α * Z' c d)) := by ring
    _ ≤ K * (A j₀ * (1 - t) * faceSum Li (fun _ _ => 1) (fun j => if j = j₀ then
          (fun x y => if x ≠ y then (1 : ℝ) else 0) else fun x y => if x ≠ y then 1 else 0) c d
        + A j₀ * t * Fz c d) := by
          rw [hZc]
          refine mul_le_mul_of_nonneg_left ?_ hKpos.le
          have := mul_le_mul_of_nonneg_left hF1 (mul_nonneg hA0 h1t)
          linarith
    _ ≤ K * faceSum Li (fun _ _ => 1) (fun j => if j = j₀ then E j₀
          else fun x y => if x ≠ y then 1 else 0) c d :=
          mul_le_mul_of_nonneg_left hmix_le hKpos.le
    _ = faceSum Li (fun _ _ => 1) (fun j => if j = j₀ then E j₀
          else fun x y => if x ≠ y then 1 else 0) c d * K := mul_comm _ _
    _ ≤ _ := hbare

end Outerplanar
