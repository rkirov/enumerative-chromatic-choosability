/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.Kernel

/-!
# One instance of the ball inequality from a kernel certificate

The ball inequality at a root edge (`InBall`, `Outerplanar/Ball.lean`) is a statement about seven
root entries `F i`: the six good pairs, and the pair that receives the moved weight. With root
weights `n i` (`100` on five good pairs, `91` on the donor, `9` on the recipient) it reads
`(α A) ^ 600 ≤ ∏ F i ^ n i`.

`ball_instance` derives it from data that is checked by natural-number arithmetic:

* thread counts `T i y` and a kernel `f i y` whose row sums are `c₀ · n i`;
* a *plan* `μ`: the column sums of `f`, taken `s` times, are a sum of weight vectors `bv y z` of
  vertices of the child's ball (`y` the donor among the six good child pairs, `z` any column);
* the entropy inequality `α ^ (600 c₀) · ∏ f ^ f ≤ ∏ R ^ R · ∏ T ^ f`.

The columns are the six good pairs of the loaded edge and three further slots (`Col`).
-/

namespace Outerplanar

open Finset

/-- The columns of a kernel: the six good pairs of the loaded edge, and three further slots (for
its completed pairs). -/
abbrev Col := Fin 6 ⊕ Fin 3

/-- The monomial `∏ w y ^ v y`. -/
def mono (w : Col → ℝ) (v : Col → ℕ) : ℝ := ∏ y, w y ^ v y

theorem mono_nonneg {w : Col → ℝ} (hw : ∀ y, 0 ≤ w y) (v : Col → ℕ) : 0 ≤ mono w v :=
  prod_nonneg fun y _ => pow_nonneg (hw y) _

theorem mono_smul (w : Col → ℝ) (n : ℕ) (v : Col → ℕ) : mono w (n • v) = mono w v ^ n := by
  unfold mono
  rw [← prod_pow]
  refine prod_congr rfl fun y _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_comm, pow_mul]

theorem mono_sum {ι : Type*} (s : Finset ι) (w : Col → ℝ) (v : ι → Col → ℕ) :
    mono w (∑ i ∈ s, v i) = ∏ i ∈ s, mono w (v i) := by
  unfold mono
  rw [prod_comm]
  refine prod_congr rfl fun y _ => ?_
  rw [Finset.sum_apply, prod_pow_eq_pow_sum]

/-- The weight vector of a vertex of the child's ball: `100` on the good pairs, with `9` moved
from the good pair `y` to the column `z`. -/
def bv (y : Fin 6) (z : Col) : Col → ℕ := fun t =>
  (match t with
    | Sum.inl k => if k = y then 91 else 100
    | Sum.inr _ => 0) + (if t = z then 9 else 0)

theorem mono_bv (w : Col → ℝ) (y : Fin 6) (z : Col) :
    mono w (bv y z)
      = (∏ k ∈ univ.erase y, w (Sum.inl k)) ^ 100 * w (Sum.inl y) ^ 91 * w z ^ 9 := by
  unfold mono bv
  simp only [pow_add, prod_mul_distrib]
  have h1 : ∏ t : Col, w t ^ (if t = z then 9 else 0) = w z ^ 9 := by
    rw [Finset.prod_eq_single z (fun t _ ht => by rw [ite_eq_right ht, pow_zero])
      (fun h => absurd (mem_univ z) h), ite_eq_left rfl]
  have h2 : ∏ t : Col, w t ^ (match t with
      | Sum.inl k => if k = y then 91 else 100
      | Sum.inr _ => 0)
      = (∏ k ∈ univ.erase y, w (Sum.inl k)) ^ 100 * w (Sum.inl y) ^ 91 := by
    rw [Fintype.prod_sum_type]
    simp only [pow_zero, prod_const_one, mul_one]
    rw [← Finset.mul_prod_erase univ _ (mem_univ y), ite_eq_left rfl, ← prod_pow, mul_comm]
    congr 1
    exact prod_congr rfl fun k hk => by rw [ite_eq_right (Finset.ne_of_mem_erase hk)]
  rw [h1, h2]

/-- A plan of ball vertices gives a lower bound for the corresponding monomial. -/
theorem plan_bound {w : Col → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hball : ∀ (y : Fin 6) (z : Col), A ^ 600 ≤ mono w (bv y z)) (μ : Fin 6 → Col → ℕ) :
    A ^ (600 * ∑ y, ∑ z, μ y z) ≤ mono w (∑ y, ∑ z, μ y z • bv y z) := by
  rw [mono_sum]
  simp only [mono_sum, mono_smul]
  rw [pow_mul, ← prod_pow_eq_pow_sum]
  refine prod_le_prod₀ (fun y _ => pow_nonneg (pow_nonneg hA _) _) fun y _ => ?_
  rw [← prod_pow_eq_pow_sum]
  exact prod_le_prod₀ (fun z _ => pow_nonneg (pow_nonneg hA _) _) fun z _ =>
    pow_le_pow_left₀ (pow_nonneg hA _) (hball y z) _

theorem mono_add (w : Col → ℝ) (v v' : Col → ℕ) : mono w (v + v') = mono w v * mono w v' := by
  unfold mono
  rw [← prod_mul_distrib]
  exact prod_congr rfl fun y _ => by rw [Pi.add_apply, pow_add]

/-- **One instance of the ball inequality from a kernel**, given the bound for the child side. -/
theorem ball_instance_of_child {F : Fin 7 → ℝ} {w : Col → ℝ} (hw : ∀ y, 0 ≤ w y) {A : ℝ}
    (hA : 0 ≤ A) (T f : Fin 7 → Col → ℕ) (hF : ∀ i, ∑ y, (T i y : ℝ) * w y ≤ F i)
    (hF0 : ∀ i, 0 ≤ F i) (n : Fin 7 → ℕ) (c₀ : ℕ) (hc : 0 < c₀)
    (hrow : ∀ i, ∑ y, f i y = c₀ * n i)
    (hchild : A ^ (600 * c₀) ≤ mono w fun y => ∑ i, f i y) (α : ℕ)
    (hnum : α ^ (600 * c₀) * ∏ i, ∏ y, f i y ^ f i y
      ≤ (∏ i, (∑ y, f i y) ^ (∑ y, f i y)) * ∏ i, ∏ y, T i y ^ f i y) :
    ((α : ℝ) * A) ^ 600 ≤ ∏ i, F i ^ n i := by
  -- the kernel inequality
  have hk := kernel_bound F w hw T f hF
  have hnum' : (α : ℝ) ^ (600 * c₀) * ∏ i, ∏ y, (f i y : ℝ) ^ f i y
      ≤ (∏ i, ((∑ y, f i y : ℕ) : ℝ) ^ (∑ y, f i y)) * ∏ i, ∏ y, (T i y : ℝ) ^ f i y := by
    exact_mod_cast hnum
  have hff : 0 < ∏ i : Fin 7, ∏ y : Col, (f i y : ℝ) ^ f i y := by
    refine prod_pos fun i _ => prod_pos fun y _ => ?_
    rcases Nat.eq_zero_or_pos (f i y) with h0 | hpos
    · rw [h0, pow_zero]; exact one_pos
    · exact pow_pos (by exact_mod_cast hpos) _
  have hRT0 : 0 ≤ (∏ i, ((∑ y, f i y : ℕ) : ℝ) ^ (∑ y, f i y))
      * ∏ i, ∏ y, (T i y : ℝ) ^ f i y :=
    mul_nonneg (prod_nonneg fun i _ => pow_nonneg (Nat.cast_nonneg _) _)
      (prod_nonneg fun i _ => prod_nonneg fun y _ => pow_nonneg (Nat.cast_nonneg _) _)
  have hmono : mono w (fun y => ∑ i, f i y) = ∏ y, w y ^ (∑ i, f i y) := rfl
  have hprodF : ∏ i, F i ^ (∑ y, f i y) = (∏ i, F i ^ n i) ^ c₀ := by
    rw [← prod_pow]
    exact prod_congr rfl fun i _ => by rw [hrow i, mul_comm, pow_mul]
  -- combine
  have hmain : (∏ i, ∏ y, (f i y : ℝ) ^ f i y) * (((α : ℝ) * A) ^ 600) ^ c₀
      ≤ (∏ i, ∏ y, (f i y : ℝ) ^ f i y) * (∏ i, F i ^ n i) ^ c₀ := by
    calc (∏ i, ∏ y, (f i y : ℝ) ^ f i y) * (((α : ℝ) * A) ^ 600) ^ c₀
        = ((α : ℝ) ^ (600 * c₀) * ∏ i, ∏ y, (f i y : ℝ) ^ f i y) * A ^ (600 * c₀) := by
          rw [← pow_mul, mul_pow]
          ring
      _ ≤ ((∏ i, ((∑ y, f i y : ℕ) : ℝ) ^ (∑ y, f i y)) * ∏ i, ∏ y, (T i y : ℝ) ^ f i y)
            * mono w (fun y => ∑ i, f i y) :=
          mul_le_mul hnum' hchild (pow_nonneg hA _) hRT0
      _ ≤ (∏ i, ∏ y, (f i y : ℝ) ^ f i y) * ∏ i, F i ^ (∑ y, f i y) := by
          rw [hmono]
          exact hk
      _ = _ := by rw [hprodF]
  have hpow := le_of_mul_le_mul_left hmain hff
  exact (pow_le_pow_iff_left₀ (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) hA) _)
    (prod_nonneg fun i _ => pow_nonneg (hF0 i) _) hc.ne').mp hpow

/-- **One instance of the ball inequality from a kernel certificate.** -/
theorem ball_instance {F : Fin 7 → ℝ} {w : Col → ℝ} (hw : ∀ y, 0 ≤ w y) {A : ℝ} (hA : 0 ≤ A)
    (hball : ∀ (y : Fin 6) (z : Col), A ^ 600 ≤ mono w (bv y z))
    (T f : Fin 7 → Col → ℕ) (hF : ∀ i, ∑ y, (T i y : ℝ) * w y ≤ F i) (hF0 : ∀ i, 0 ≤ F i)
    (n : Fin 7 → ℕ) (c₀ : ℕ) (hc : 0 < c₀) (hrow : ∀ i, ∑ y, f i y = c₀ * n i)
    (s : ℕ) (hs : 0 < s) (μ : Fin 6 → Col → ℕ)
    (hplan : (s • fun y => ∑ i, f i y) = ∑ y, ∑ z, μ y z • bv y z)
    (hμ : ∑ y, ∑ z, μ y z = s * c₀) (α : ℕ)
    (hnum : α ^ (600 * c₀) * ∏ i, ∏ y, f i y ^ f i y
      ≤ (∏ i, (∑ y, f i y) ^ (∑ y, f i y)) * ∏ i, ∏ y, T i y ^ f i y) :
    ((α : ℝ) * A) ^ 600 ≤ ∏ i, F i ^ n i := by
  have hchild : A ^ (600 * c₀) ≤ mono w fun y => ∑ i, f i y := by
    have h1 := plan_bound hA hball μ
    rw [← hplan, mono_smul, hμ, show 600 * (s * c₀) = (600 * c₀) * s by ring, pow_mul] at h1
    exact (pow_le_pow_iff_left₀ (pow_nonneg hA _) (mono_nonneg hw _) hs.ne').mp h1
  exact ball_instance_of_child hw hA T f hF hF0 n c₀ hc hrow hchild α hnum

end Outerplanar
