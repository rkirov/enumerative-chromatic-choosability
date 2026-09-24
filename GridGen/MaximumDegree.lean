import GridGen.PolymerUniformBounds
import GridGen.PolymerCertificate

/-!
# A size-independent ECC threshold of 5.67 times the maximum degree

The integer condition `567 * D ≤ 100 * k` is exactly `k ≥ ceil(5.67 * D)`.
There is no restriction on graph order, connectedness, or maximum degree.
An instance of `GridGen.Polymer.eccAt_of_parityCert` with the hyperbolic certificate
`parityCert_uniform`. The degree-specific certificates are sharper for small degrees
(`GridGen/DegreeFourTwenty.lean`, `GridGen/SmallDegree.lean`).
-/

namespace GridGen.Polymer

/-- The uniform threshold as a `CertifiedAt`: `s = 100/63`, so the activity is `100/(63k)`
and `D x ≤ 10000/35721` is exactly `567 D ≤ 100 k`. -/
theorem certifiedAt_uniform {D k : ℕ} (hk : 567 * D ≤ 100 * k) (hk0 : 0 < k) :
    CertifiedAt D k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk0
  have hDk : (567 : ℝ) * D ≤ 100 * k := by exact_mod_cast hk
  refine certifiedAt_of_parityCert (k₀ := k) (s := 100 / 63)
    (parityCert_uniform (by positivity) ?_) (by norm_num) (by norm_num) hk0 le_rfl
  rw [← mul_div_assoc, div_le_div_iff₀ hk' (by norm_num)]
  linarith

end GridGen.Polymer

namespace SimpleGraph

/-- Uniform ECC for all finite simple graphs, including list size zero and degree zero.
The hypothesis is an exact natural-number formulation of `k ≥ ceil(5.67 * D)`. -/
theorem eccAt_of_degree_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {D k : ℕ}
    (hdeg : ∀ v, G.degree v ≤ D) (hk : 567 * D ≤ 100 * k) : G.ECCAt k := by
  by_cases hk0 : k = 0
  · subst k
    intro L hL
    have heq : L = constList V 0 := by
      funext v
      simpa only [constList, Finset.range_zero] using Finset.card_eq_zero.mp (hL v)
    rw [heq]
    exact le_rfl
  · exact GridGen.Polymer.eccAt_of_certifiedAt G hdeg
      (GridGen.Polymer.certifiedAt_uniform hk (Nat.pos_of_ne_zero hk0))

/-- The threshold in terms of the graph's actual maximum degree. -/
theorem eccAt_of_maxDegree_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (hk : 567 * G.maxDegree ≤ 100 * k) : G.ECCAt k :=
  eccAt_of_degree_bound G (fun v => G.degree_le_maxDegree v) hk

/-- Integer ceiling form: `(567 * Δ + 99) / 100 = ceil(5.67 * Δ)`. -/
theorem eccAt_of_maxDegree_ceiling {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (hk : (567 * G.maxDegree + 99) / 100 ≤ k) : G.ECCAt k := by
  apply eccAt_of_maxDegree_bound G
  omega

end SimpleGraph
