import k3_entropy.Grid3Entropy

/-!
# Rowwise collision certificates

Apply the collision entropy inequality before averaging over source states. For a rational
source law `c / D`, the resulting logarithmic bound is certified by one finite product.
This is an optional stronger certificate, not an assertion that every seam passes it.
-/

namespace Grid3.Three

open Finset Real

variable {S T : Type*} [Fintype S] [Fintype T]

theorem row_collision_bound (a : S → ℝ) (K : S → T → ℝ)
    (ha : ∀ s, 0 ≤ a s) (hK : ∀ s t, 0 ≤ K s t)
    (hKn : ∀ s, ∑ t, K s t = 1) :
    (∑ s, a s * (-Real.log (∑ t, (K s t)^2))) ≤ ∑ s, a s * H (K s) := by
  exact Finset.sum_le_sum fun s _ =>
    mul_le_mul_of_nonneg_left (H_ge_neg_log_collision (K s) (hK s) (hKn s)) (ha s)

/-- For rational weights, a product inequality gives the weighted logarithmic bound.
The weights need not be positive individually; positivity of the row collision masses suffices. -/
theorem log_le_weighted_neg_log_of_prod (c : S → ℕ) (D : ℕ) (hD : 0 < D)
    (z : S → ℝ) (hz : ∀ s, 0 < z s) (r : ℝ) (hr : 0 < r)
    (hprod : r^D * ∏ s, (z s)^(c s) ≤ 1) :
    Real.log r ≤ ∑ s, ((c s : ℝ) / D) * (-Real.log (z s)) := by
  have hDp : (0 : ℝ) < D := by exact_mod_cast hD
  have hp : (0 : ℝ) < ∏ s, (z s)^(c s) :=
    Finset.prod_pos fun s _ => pow_pos (hz s) _
  have hlog := Real.log_le_log (mul_pos (pow_pos hr _) hp) hprod
  rw [Real.log_one, Real.log_mul (ne_of_gt (pow_pos hr _)) (ne_of_gt hp),
    Real.log_pow, Real.log_prod (fun s _ => ne_of_gt (pow_pos (hz s) _))] at hlog
  simp only [Real.log_pow] at hlog
  have heq : (D : ℝ) * (∑ s, ((c s : ℝ) / D) * (-Real.log (z s)))
      = -(∑ s, (c s : ℝ) * Real.log (z s)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro s _
    field_simp
  nlinarith

/-- A witness-free finite product certificate for rational-law conditional entropy. -/
theorem row_collision_product_bound (c : S → ℕ) (D : ℕ) (hD : 0 < D)
    (K : S → T → ℝ) (hK : ∀ s t, 0 ≤ K s t) (hKn : ∀ s, ∑ t, K s t = 1)
    (hz : ∀ s, 0 < ∑ t, (K s t)^2) (r : ℝ) (hr : 0 < r)
    (hprod : r^D * ∏ s, (∑ t, (K s t)^2)^(c s) ≤ 1) :
    Real.log r ≤ ∑ s, ((c s : ℝ) / D) * H (K s) := by
  exact le_trans (log_le_weighted_neg_log_of_prod c D hD _ hz r hr hprod)
    (row_collision_bound _ K (fun s => by positivity) hK hKn)

/-- Connect the product certificate directly to the existing Markov-chain seam term. -/
theorem seamterm_ge_log_row_collision [DecidableEq S]
    (alpha : S → ℝ) (K : ℕ → S → S → ℝ)
    (hK : ∀ j s t, 0 ≤ K j s t) (hKn : ∀ j s, ∑ t, K j s t = 1)
    (j : ℕ) (c : S → ℕ) (D : ℕ) (hD : 0 < D)
    (hcons : ∀ s, lastMarg alpha K j s = (c s : ℝ) / D)
    (hz : ∀ s, 0 < ∑ t, (K j s t)^2) (r : ℝ) (hr : 0 < r)
    (hprod : r^D * ∏ s, (∑ t, (K j s t)^2)^(c s) ≤ 1) :
    Real.log r ≤ seamterm alpha K j := by
  rw [seamterm_marginal alpha K hKn j]
  have h := row_collision_product_bound c D hD (K j) (hK j) (hKn j) hz r hr hprod
  have heq : (∑ s, ((c s : ℝ) / D) * H (K j s))
      = ∑ s, lastMarg alpha K j s * rowH (K j) s := by
    apply Finset.sum_congr rfl
    intro s _
    rw [hcons s]
    congr 1
    unfold H rowH
    apply Finset.sum_congr rfl
    intro t _
    rw [Real.negMulLog]
    ring
  rwa [heq] at h

end Grid3.Three

#print axioms Grid3.Three.row_collision_product_bound
