/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.Algebra.BigOperators.Fin

/-!
# Kernels as weighted arithmetic–geometric mean inequalities

The profile of a face at a root pair `i` is a sum over the colourings of the path (*threads*).
Group the threads by the pair `y` they put on the loaded edge: `T i y` threads, each contributing
the child entry `w y`, so the root entry is at least `∑ y, T i y · w y`.

A *kernel* is a table of natural numbers `f i y` (joint masses of root pair and child pair).
`kernel_bound` is the inequality it certifies:

`∏ᵢ Rᵢ^Rᵢ · ∏ᵢᵧ T i y ^ f i y · ∏ᵧ w y ^ mᵧ ≤ ∏ᵢᵧ f i y ^ f i y · ∏ᵢ F i ^ Rᵢ`,

with row sums `Rᵢ = ∑ᵧ f i y` and column sums `mᵧ = ∑ᵢ f i y`. In logarithms: the root
expectation of `log F` is at least the conditional entropy of the thread given the root pair plus
the child expectation of `log w`. It is weighted AM–GM in every row, cleared of denominators
(`amgm_real`), so that a certificate is checked with natural-number arithmetic.

This is part of the formalization of the ball invariant (`Outerplanar/Ball.lean`); the numeric
form of the entropy condition is the one used by the verifier
`ai_research_notes/outerplanar/chain/cx/verify_theorem.py`.
-/

namespace Outerplanar

open Finset

/-- Weighted AM–GM with natural weights, cleared of denominators:
`D^D ∏ a^k ≤ (∏ k^k) (∑ a)^D` with `D = ∑ k`, for non-negative reals `a`. -/
theorem amgm_real {ι : Type*} (s : Finset ι) (a : ι → ℝ) (k : ι → ℕ) (ha : ∀ i ∈ s, 0 ≤ a i) :
    ((∑ i ∈ s, k i : ℕ) : ℝ) ^ (∑ i ∈ s, k i) * ∏ i ∈ s, a i ^ k i ≤
      (∏ i ∈ s, (k i : ℝ) ^ k i) * (∑ i ∈ s, a i) ^ (∑ i ∈ s, k i) := by
  classical
  set D := ∑ i ∈ s, k i with hD
  -- only the indices with positive weight matter
  set t := s.filter (fun i => 0 < k i) with ht
  have hkt : ∀ i ∈ s, i ∉ t → k i = 0 := fun i hi hit => by
    simp only [ht, mem_filter, not_and, not_lt, nonpos_iff_eq_zero] at hit
    exact hit hi
  have hp1 : ∏ i ∈ s, a i ^ k i = ∏ i ∈ t, a i ^ k i :=
    (prod_subset (filter_subset _ _) fun i hi hit => by rw [hkt i hi hit, pow_zero]).symm
  have hp2 : ∏ i ∈ s, (k i : ℝ) ^ k i = ∏ i ∈ t, (k i : ℝ) ^ k i :=
    (prod_subset (filter_subset _ _) fun i hi hit => by rw [hkt i hi hit, pow_zero]).symm
  have hDt : D = ∑ i ∈ t, k i :=
    (sum_subset (filter_subset _ _) fun i hi hit => hkt i hi hit).symm
  have hsum : ∑ i ∈ t, a i ≤ ∑ i ∈ s, a i :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun i hi _ => ha i hi
  have hsum0 : 0 ≤ ∑ i ∈ t, a i := sum_nonneg fun i hi => ha i (mem_filter.mp hi).1
  rcases Nat.eq_zero_or_pos D with hD0 | hDpos
  · have ht0 : t = ∅ := by
      by_contra hne
      obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have h1 : k i ≤ ∑ j ∈ t, k j := single_le_sum (fun _ _ => Nat.zero_le _) hi
      have h2 := (mem_filter.mp hi).2
      omega
    rw [hp1, hp2, ht0, hD0]
    simp
  · have hDr : (0 : ℝ) < D := by exact_mod_cast hDpos
    have hkpos : ∀ i ∈ t, (0 : ℝ) < k i := fun i hi => by exact_mod_cast (mem_filter.mp hi).2
    have hz0 : ∀ i ∈ t, 0 ≤ a i * D / k i := fun i hi =>
      div_nonneg (mul_nonneg (ha i (mem_filter.mp hi).1) hDr.le) (hkpos i hi).le
    have hgm := Real.geom_mean_le_arith_mean_weighted t (fun i => (k i : ℝ) / D)
      (fun i => a i * D / k i) (fun i hi => (div_pos (hkpos i hi) hDr).le)
      (by rw [← sum_div, ← Nat.cast_sum, ← hDt]; exact div_self hDr.ne') hz0
    have hrhs : ∑ i ∈ t, (k i : ℝ) / D * (a i * D / k i) = ∑ i ∈ t, a i :=
      sum_congr rfl fun i hi => by
        have := (hkpos i hi).ne'
        field_simp
    rw [hrhs] at hgm
    have hL0 : 0 ≤ ∏ i ∈ t, (a i * D / k i) ^ ((k i : ℝ) / D) :=
      prod_nonneg fun i hi => Real.rpow_nonneg (hz0 i hi) _
    have hpow := pow_le_pow_left₀ hL0 (hgm.trans hsum) D
    have e : (∏ i ∈ t, (a i * D / k i) ^ ((k i : ℝ) / D)) ^ D
        = ∏ i ∈ t, (a i * D / k i) ^ k i := by
      rw [← prod_pow]
      refine prod_congr rfl fun i hi => ?_
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hz0 i hi), div_mul_cancel₀ _ hDr.ne',
        Real.rpow_natCast]
    rw [e] at hpow
    have e2 : (∏ i ∈ t, (a i * D / k i) ^ k i) * ∏ i ∈ t, (k i : ℝ) ^ k i
        = (D : ℝ) ^ D * ∏ i ∈ t, a i ^ k i := by
      rw [← prod_mul_distrib]
      have h1 : ∀ i ∈ t, (a i * D / k i) ^ k i * (k i : ℝ) ^ k i = (D : ℝ) ^ k i * a i ^ k i :=
        fun i hi => by
          rw [← mul_pow, div_mul_cancel₀ _ (hkpos i hi).ne', mul_pow, mul_comm]
      rw [prod_congr rfl h1, prod_mul_distrib, prod_pow_eq_pow_sum, ← hDt]
    rw [hp1, hp2, ← e2, mul_comm (∏ i ∈ t, (k i : ℝ) ^ k i)]
    exact mul_le_mul_of_nonneg_right hpow
      (prod_nonneg fun i hi => pow_nonneg (hkpos i hi).le _)

/-- **The inequality certified by a kernel.** `F i` dominates `∑ y, T i y · w y`; `f` is a table of
joint masses. -/
theorem kernel_bound {ι κ : Type*} [Fintype ι] [Fintype κ] (F : ι → ℝ) (w : κ → ℝ)
    (hw : ∀ y, 0 ≤ w y) (T f : ι → κ → ℕ) (hF : ∀ i, ∑ y, (T i y : ℝ) * w y ≤ F i) :
    (∏ i, ((∑ y, f i y : ℕ) : ℝ) ^ (∑ y, f i y)) * (∏ i, ∏ y, (T i y : ℝ) ^ f i y)
        * ∏ y, w y ^ (∑ i, f i y)
      ≤ (∏ i, ∏ y, (f i y : ℝ) ^ f i y) * ∏ i, F i ^ (∑ y, f i y) := by
  have hrow : ∀ i, ((∑ y, f i y : ℕ) : ℝ) ^ (∑ y, f i y)
      * ((∏ y, (T i y : ℝ) ^ f i y) * ∏ y, w y ^ f i y)
      ≤ (∏ y, (f i y : ℝ) ^ f i y) * F i ^ (∑ y, f i y) := by
    intro i
    have h0 : ∀ y ∈ (univ : Finset κ), 0 ≤ (T i y : ℝ) * w y := fun y _ =>
      mul_nonneg (Nat.cast_nonneg _) (hw y)
    have h1 := amgm_real univ (fun y => (T i y : ℝ) * w y) (f i) h0
    simp only [mul_pow, prod_mul_distrib] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_
      (prod_nonneg fun y _ => pow_nonneg (Nat.cast_nonneg _) _))
    exact pow_le_pow_left₀ (sum_nonneg h0) (hF i) _
  have hall := prod_le_prod₀ (s := (univ : Finset ι))
    (fun i _ => mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
      (mul_nonneg (prod_nonneg fun y _ => pow_nonneg (Nat.cast_nonneg _) _)
        (prod_nonneg fun y _ => pow_nonneg (hw y) _)))
    (fun i _ => hrow i)
  simp only [prod_mul_distrib] at hall
  have hcomm : ∏ i, ∏ y, w y ^ f i y = ∏ y, w y ^ (∑ i, f i y) := by
    rw [prod_comm]
    exact prod_congr rfl fun y _ => prod_pow_eq_pow_sum _ _ _
  rw [hcomm] at hall
  calc _ = (∏ i, ((∑ y, f i y : ℕ) : ℝ) ^ (∑ y, f i y))
        * ((∏ i, ∏ y, (T i y : ℝ) ^ f i y) * ∏ y, w y ^ (∑ i, f i y)) := by ring
    _ ≤ _ := hall

end Outerplanar
