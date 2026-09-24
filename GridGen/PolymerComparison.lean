import GridGen.PolymerModel
import GridGen.PolymerDerivative
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Algebra.BigOperators.Field

/-!
# The finite polymer comparison engine

Normalization of the actual partition sum, and the comparison of the endpoints of a finite
interpolation whose derivative is nonnegative on `[0,1]`. The graph-specific derivative
bound is `graphActivity_cert_derivative_sum_nonneg`.
-/

namespace GridGen.Polymer

open Finset

variable {V : Type*} [DecidableEq V]

/-- Normalizing every block by `q` to its size normalizes the entire partition function
by `q` to the size of its ground set. -/
theorem partitionSum_normalized (w : Finset V → ℝ) (q : ℝ) (U : Finset V) :
    partitionSum (fun S => w S / q ^ S.card) U = partitionSum w U / q ^ U.card := by
  classical
  unfold partitionSum
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro P _
  rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, P.sum_card_parts]

/-- Endpoints of a finite partition interpolation compare once its proved derivative
formula is nonnegative on the interval. Differentiability and continuity are supplied here. -/
theorem partitionSum_endpoints_le (U : Finset V) (w : Finset V → ℝ → ℝ)
    (w' : Finset V → ℝ → ℝ)
    (hw : ∀ t, ∀ S ∈ blocks U, HasDerivAt (w S) (w' S t) t)
    (hnonneg : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ ∑ S ∈ blocks U, w' S t * partitionSum (fun T => w T t) (U \ S)) :
    partitionSum (fun S => w S 0) U ≤ partitionSum (fun S => w S 1) U := by
  have hd := fun t => hasDerivAt_partitionSum U w (fun S => w' S t) t (hw t)
  have hm : MonotoneOn (fun t => partitionSum (fun S => w S t) U) (Set.Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · exact (continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)).continuousOn
    · exact fun t _ => (hd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hd t).deriv]
      exact hnonneg t (interior_subset ht)
  exact hm (by simp) (by simp) (by norm_num)

/-- The strict form: a derivative positive on the interior makes the endpoints differ. -/
theorem partitionSum_endpoints_lt (U : Finset V) (w : Finset V → ℝ → ℝ)
    (w' : Finset V → ℝ → ℝ)
    (hw : ∀ t, ∀ S ∈ blocks U, HasDerivAt (w S) (w' S t) t)
    (hpos : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      0 < ∑ S ∈ blocks U, w' S t * partitionSum (fun T => w T t) (U \ S)) :
    partitionSum (fun S => w S 0) U < partitionSum (fun S => w S 1) U := by
  have hd := fun t => hasDerivAt_partitionSum U w (fun S => w' S t) t (hw t)
  have hm : StrictMonoOn (fun t => partitionSum (fun S => w S t) U) (Set.Icc 0 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 1)
    · exact (continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)).continuousOn
    · intro t ht
      rw [(hd t).deriv]
      exact hpos t (interior_subset ht)
  exact hm (by simp) (by simp) (by norm_num)

end GridGen.Polymer
