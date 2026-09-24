import GridGen.PolymerPartition
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Differentiating the actual finite partition sum

The derivative is a sum over a distinguished block and the partition function of its
complement. In particular the affine list interpolation has exactly the signed deficiency
terms used in the proposed full-grid proof.
-/

namespace GridGen.Polymer

open Finset

variable {V : Type*} [DecidableEq V]

theorem hasDerivAt_partitionSum (U : Finset V) (w : Finset V → ℝ → ℝ)
    (w' : Finset V → ℝ) (t : ℝ)
    (hw : ∀ S ∈ blocks U, HasDerivAt (w S) (w' S) t) :
    HasDerivAt (fun t => partitionSum (fun S => w S t) U)
      (∑ S ∈ blocks U, w' S * partitionSum (fun T => w T t) (U \ S)) t := by
  classical
  have hp : ∀ P : Finpartition U,
      HasDerivAt (fun t => ∏ S ∈ P.parts, w S t)
        (∑ S ∈ P.parts, w' S * ∏ T ∈ P.parts.erase S, w T t) t := by
    intro P
    simpa only [smul_eq_mul, mul_comm] using
      HasDerivAt.fun_finsetProd (fun S hS => hw S (parts_subset_blocks P hS))
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun P _ => hp P)
  rw [marked_partition_sum] at hsum
  exact hsum

/-- A convenient explicit finite interpolation; graph coefficients and list deficiencies
will later supply `c` and `d`. -/
noncomputable def interpolatedSum (c d : Finset V → ℝ) (k t : ℝ) (U : Finset V) : ℝ :=
  partitionSum (fun S => c S * (k - t * d S)) U

theorem hasDerivAt_interpolatedSum (c d : Finset V → ℝ) (k t : ℝ) (U : Finset V) :
    HasDerivAt (fun t => interpolatedSum c d k t U)
      (-∑ S ∈ blocks U, c S * d S * interpolatedSum c d k t (U \ S)) t := by
  have hw : ∀ S ∈ blocks U,
      HasDerivAt (fun t => c S * (k - t * d S)) (-c S * d S) t := by
    intro S _
    convert! ((hasDerivAt_const t k).sub ((hasDerivAt_id t).mul_const (d S))).const_mul
      (c S) using 1
    try simp
  have h := hasDerivAt_partitionSum U (fun S t => c S * (k - t * d S))
    (fun S => -c S * d S) t hw
  simpa only [interpolatedSum, neg_mul, Finset.sum_neg_distrib] using h

end GridGen.Polymer
