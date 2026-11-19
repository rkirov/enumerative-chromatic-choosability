/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.LoadedCert

/-!
# The ball class is closed under sums

A weighted geometric mean with natural weights is superadditive (`gm_superadd`): from
`a ^ N ≤ ∏ x i ^ n i` and `b ^ N ≤ ∏ y i ^ n i`, `N = ∑ n i`, it follows that
`(a + b) ^ N ≤ ∏ (x i + y i) ^ n i`. Every inequality of the ball class (`InBall`,
`Outerplanar/Ball.lean`) has this shape, so the sum of two profiles in the ball class, with
constants `A` and `A'`, is in the ball class with constant `A + A'` (`InBall.add`).

This is what lets a face be split into a shorter face and a remainder: the constants of the two
parts add up.
-/

namespace Outerplanar

open Finset

/-- **Superadditivity of a weighted geometric mean** with natural weights. -/
theorem gm_superadd {ι : Type*} (s : Finset ι) (x y : ι → ℝ) (n : ι → ℕ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hy : ∀ i ∈ s, 0 ≤ y i) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hN : 0 < ∑ i ∈ s, n i) (h1 : a ^ (∑ i ∈ s, n i) ≤ ∏ i ∈ s, x i ^ n i)
    (h2 : b ^ (∑ i ∈ s, n i) ≤ ∏ i ∈ s, y i ^ n i) :
    (a + b) ^ (∑ i ∈ s, n i) ≤ ∏ i ∈ s, (x i + y i) ^ n i := by
  classical
  set N := ∑ i ∈ s, n i with hNdef
  have hxy : ∀ i ∈ s, 0 ≤ x i + y i := fun i hi => add_nonneg (hx i hi) (hy i hi)
  have hG0 : 0 ≤ ∏ i ∈ s, (x i + y i) ^ n i := prod_nonneg fun i hi => pow_nonneg (hxy i hi) _
  rcases hG0.eq_or_lt with hG | hG
  · -- some factor vanishes: both products vanish
    obtain ⟨i, hi, hzero⟩ := Finset.prod_eq_zero_iff.mp hG.symm
    have hni : n i ≠ 0 := fun h0 => by
      rw [h0, pow_zero] at hzero
      exact one_ne_zero hzero
    have hsum : x i + y i = 0 := (pow_eq_zero_iff hni).mp hzero
    have hxi : x i = 0 := le_antisymm (by linarith [hy i hi]) (hx i hi)
    have hyi : y i = 0 := le_antisymm (by linarith [hx i hi]) (hy i hi)
    have hX : ∏ i ∈ s, x i ^ n i = 0 :=
      Finset.prod_eq_zero hi (by rw [hxi, zero_pow hni])
    have hY : ∏ i ∈ s, y i ^ n i = 0 :=
      Finset.prod_eq_zero hi (by rw [hyi, zero_pow hni])
    rw [hX] at h1
    rw [hY] at h2
    have ha0 : a = 0 := by
      by_contra hne
      exact absurd h1 (not_le.mpr (pow_pos (lt_of_le_of_ne ha (Ne.symm hne)) _))
    have hb0 : b = 0 := by
      by_contra hne
      exact absurd h2 (not_le.mpr (pow_pos (lt_of_le_of_ne hb (Ne.symm hne)) _))
    rw [ha0, hb0, add_zero, zero_pow hN.ne', ← hG]
  · -- all factors with positive weight are positive
    have hpos : ∀ i ∈ s, n i ≠ 0 → 0 < x i + y i := by
      intro i hi hni
      rcases (hxy i hi).eq_or_lt with h0 | h0
      · exfalso
        have : ∏ i ∈ s, (x i + y i) ^ n i = 0 :=
          Finset.prod_eq_zero hi (by rw [← h0, zero_pow hni])
        exact hG.ne' this
      · exact h0
    set γ : ℝ := (∏ i ∈ s, (x i + y i) ^ n i) ^ ((N : ℝ)⁻¹) with hγ
    have hγpos : 0 < γ := Real.rpow_pos_of_pos hG _
    have hγN : γ ^ N = ∏ i ∈ s, (x i + y i) ^ n i :=
      Real.rpow_inv_natCast_pow hG.le hN.ne'
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    -- the two normalized families
    have key : ∀ (u : ι → ℝ), (∀ i ∈ s, 0 ≤ u i) → (∀ i ∈ s, u i ≤ x i + y i) → ∀ c : ℝ,
        0 ≤ c → c ^ N ≤ ∏ i ∈ s, u i ^ n i →
        c ≤ γ * ((∑ i ∈ s, (n i : ℝ) * (u i / (x i + y i))) / N) := by
      intro u hu hule c hc hcu
      have hp0 : ∀ i ∈ s, 0 ≤ (n i : ℝ) * (u i / (x i + y i)) := fun i hi =>
        mul_nonneg (Nat.cast_nonneg _) (div_nonneg (hu i hi) (hxy i hi))
      have hprod : ∏ i ∈ s, u i ^ n i
          = (∏ i ∈ s, (u i / (x i + y i)) ^ n i) * ∏ i ∈ s, (x i + y i) ^ n i := by
        rw [← prod_mul_distrib]
        refine prod_congr rfl fun i hi => ?_
        by_cases hni : n i = 0
        · rw [hni, pow_zero, pow_zero, pow_zero, mul_one]
        · rw [← mul_pow, div_mul_cancel₀ _ (hpos i hi hni).ne']
      have hamgm := amgm_real s (fun i => (n i : ℝ) * (u i / (x i + y i))) n hp0
      simp only [mul_pow, prod_mul_distrib] at hamgm
      have hkk : 0 < ∏ i ∈ s, ((n i : ℝ)) ^ n i := prod_pos fun i _ => by
        rcases Nat.eq_zero_or_pos (n i) with h0 | h0
        · rw [h0, pow_zero]; exact one_pos
        · exact pow_pos (by exact_mod_cast h0) _
      have h3 : (N : ℝ) ^ N * ∏ i ∈ s, (u i / (x i + y i)) ^ n i
          ≤ (∑ i ∈ s, (n i : ℝ) * (u i / (x i + y i))) ^ N := by
        have h4 : (∏ i ∈ s, ((n i : ℝ)) ^ n i) * ((N : ℝ) ^ N
              * ∏ i ∈ s, (u i / (x i + y i)) ^ n i)
            ≤ (∏ i ∈ s, ((n i : ℝ)) ^ n i)
              * (∑ i ∈ s, (n i : ℝ) * (u i / (x i + y i))) ^ N := by
          calc _ = ((N : ℝ)) ^ N * ((∏ i ∈ s, ((n i : ℝ)) ^ n i)
                * ∏ i ∈ s, (u i / (x i + y i)) ^ n i) := by ring
            _ ≤ _ := by
              have := hamgm
              rw [← hNdef] at this
              exact_mod_cast this
        exact le_of_mul_le_mul_left h4 hkk
      have hS0 : 0 ≤ ∑ i ∈ s, (n i : ℝ) * (u i / (x i + y i)) := sum_nonneg hp0
      have h5 : c ^ N ≤ (γ * ((∑ i ∈ s, (n i : ℝ) * (u i / (x i + y i))) / N)) ^ N := by
        rw [mul_pow, hγN, div_pow]
        calc c ^ N ≤ ∏ i ∈ s, u i ^ n i := hcu
          _ = (∏ i ∈ s, (u i / (x i + y i)) ^ n i) * ∏ i ∈ s, (x i + y i) ^ n i := hprod
          _ ≤ ((∑ i ∈ s, (n i : ℝ) * (u i / (x i + y i))) ^ N / (N : ℝ) ^ N)
              * ∏ i ∈ s, (x i + y i) ^ n i := by
            refine mul_le_mul_of_nonneg_right ?_ hG.le
            rw [le_div_iff₀ (pow_pos hNr _), mul_comm]
            exact h3
          _ = _ := by ring
      exact (pow_le_pow_iff_left₀ hc (mul_nonneg hγpos.le (div_nonneg hS0 hNr.le)) hN.ne').mp h5
    have ka := key x hx (fun i hi => le_add_of_nonneg_right (hy i hi)) a ha h1
    have kb := key y hy (fun i hi => le_add_of_nonneg_left (hx i hi)) b hb h2
    have hsum : (∑ i ∈ s, (n i : ℝ) * (x i / (x i + y i)))
        + ∑ i ∈ s, (n i : ℝ) * (y i / (x i + y i)) = N := by
      rw [← sum_add_distrib, hNdef, Nat.cast_sum]
      refine sum_congr rfl fun i hi => ?_
      by_cases hni : n i = 0
      · rw [hni]; simp
      · have := (hpos i hi hni).ne'
        field_simp
    have hab : a + b ≤ γ := by
      calc a + b ≤ γ * ((∑ i ∈ s, (n i : ℝ) * (x i / (x i + y i))) / N)
            + γ * ((∑ i ∈ s, (n i : ℝ) * (y i / (x i + y i))) / N) := add_le_add ka kb
        _ = γ * (((∑ i ∈ s, (n i : ℝ) * (x i / (x i + y i)))
            + ∑ i ∈ s, (n i : ℝ) * (y i / (x i + y i))) / N) := by ring
        _ = γ := by rw [hsum, div_self hNr.ne', mul_one]
    calc (a + b) ^ N ≤ γ ^ N := pow_le_pow_left₀ (add_nonneg ha hb) hab _
      _ = _ := hγN

theorem sum_nW : ∀ j : Fin 6, ∑ i : Fin 7, nW j.val i.val = 600 := by decide

/-- The seven entries of an inequality of the ball class, as one product. -/
theorem ball_eq_prod (j : Fin 6) (G : Fin 6 → ℝ) (x : ℝ) :
    (∏ k ∈ univ.erase j, G k) ^ 100 * G j ^ 91 * x ^ 9
      = ∏ i : Fin 7, (Fin.snoc G x : Fin 7 → ℝ) i ^ nW j.val i.val :=
  (prod_rows j (Fin.snoc G x) G x (fun k => Fin.snoc_castSucc (α := fun _ => ℝ) x G k)
    (Fin.snoc_last (α := fun _ => ℝ) x G)).symm

/-- One inequality of the ball class for a sum. -/
theorem ball_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (j : Fin 6) {G G' : Fin 6 → ℝ} {x x' : ℝ}
    (hG : ∀ k, 0 ≤ G k) (hG' : ∀ k, 0 ≤ G' k) (hx : 0 ≤ x) (hx' : 0 ≤ x')
    (h : a ^ 600 ≤ (∏ k ∈ univ.erase j, G k) ^ 100 * G j ^ 91 * x ^ 9)
    (h' : b ^ 600 ≤ (∏ k ∈ univ.erase j, G' k) ^ 100 * G' j ^ 91 * x' ^ 9) :
    (a + b) ^ 600 ≤ (∏ k ∈ univ.erase j, (G k + G' k)) ^ 100 * (G j + G' j) ^ 91
      * (x + x') ^ 9 := by
  rw [ball_eq_prod] at h h'
  have hsn : ∀ (H : Fin 6 → ℝ) (z : ℝ), (∀ k, 0 ≤ H k) → 0 ≤ z →
      ∀ i : Fin 7, 0 ≤ (Fin.snoc H z : Fin 7 → ℝ) i := fun H z hH hz i => by
    refine Fin.lastCases ?_ (fun k => ?_) i
    · rw [Fin.snoc_last]; exact hz
    · rw [Fin.snoc_castSucc]; exact hH k
  have key := gm_superadd univ (Fin.snoc G x : Fin 7 → ℝ) (Fin.snoc G' x' : Fin 7 → ℝ)
    (fun i => nW j.val i.val) (fun i _ => hsn G x hG hx i) (fun i _ => hsn G' x' hG' hx' i)
    ha hb (by rw [sum_nW]; norm_num) (by rw [sum_nW]; exact h) (by rw [sum_nW]; exact h')
  rw [sum_nW] at key
  have e : (fun i : Fin 7 => (Fin.snoc G x : Fin 7 → ℝ) i + (Fin.snoc G' x' : Fin 7 → ℝ) i)
      = (Fin.snoc (fun k => G k + G' k) (x + x') : Fin 7 → ℝ) := by
    funext i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simp only [Fin.snoc_last]
    · simp only [Fin.snoc_castSucc]
  rw [ball_eq_prod j (fun k => G k + G' k) (x + x'), ← e]
  exact key

variable {S T : Finset ℕ} {W W' : ℕ → ℕ → ℝ} {A A' : ℝ}

/-- **The ball class is closed under sums.** -/
theorem InBall.add (hA : 0 ≤ A) (hA' : 0 ≤ A') (h0 : ∀ c d, 0 ≤ W c d)
    (h0' : ∀ c d, 0 ≤ W' c d) (h : InBall S T W A) (h' : InBall S T W' A') :
    InBall S T (fun c d => W c d + W' c d) (A + A') := fun p q hm hpq j c hc d hd hcd =>
  ball_add hA hA' j (fun _ => h0 _ _) (fun _ => h0' _ _) (h0 _ _) (h0' _ _)
    (h p q hm hpq j c hc d hd hcd) (h' p q hm hpq j c hc d hd hcd)

/-- A smaller constant. -/
theorem InBall.weaken (hA' : 0 ≤ A') (hle : A' ≤ A) (h : InBall S T W A) : InBall S T W A' :=
  fun p q hm hpq j c hc d hd hcd =>
    (pow_le_pow_left₀ hA' hle _).trans (h p q hm hpq j c hc d hd hcd)

end Outerplanar
