import GridGen.PolymerCertificate
import GridGen.PolymerGridDegree
import ListColoring.BoxProd

/-!
# Parity-improved eventual ECC for all finite graphs of maximum degree at most four

An instance of `GridGen.Polymer.eccAt_of_parityCert`: the only degree-specific input is the
rational certificate `parityCert_degree_four`, checked by `norm_num`. There is no hypothesis
on graph order, planarity, or bipartiteness.
-/

namespace GridGen.Polymer

open SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The degree-four certificate at `k₀ = 20`, `s = 17/10`: activity `x₀ = 17/200`, branch
masses `(553/500, 3/10)` under three ports, root odd mass `7/17` under four. -/
theorem parityCert_degree_four :
    ParityCert 4 ((17 / 10 : ℝ) / (20 : ℕ)) (553 / 500) (3 / 10) (7 / 17) := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_, by norm_num⟩ <;>
    norm_num [parityPower]

end GridGen.Polymer

namespace SimpleGraph

/-- Every finite simple graph of maximum degree at most four is ECC at every list size
at least 20. This is a degree bound, not a bound on the number of vertices or edges. -/
theorem eccAt_of_degree_le_four_twenty {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ 4) {k : ℕ} (hk : 20 ≤ k) : G.ECCAt k := by
  exact GridGen.Polymer.eccAt_of_parityCert G hdeg GridGen.Polymer.parityCert_degree_four
    (by norm_num) (by norm_num) (by norm_num) hk

end SimpleGraph

namespace ListColoring

open SimpleGraph
open scoped SimpleGraph

/-- Arbitrary rectangles, with both dimensions unrestricted. `pathG n` has `n+1` vertices. -/
theorem ecc_boxProd_pathG_of_twenty {k : ℕ} (hk : 20 ≤ k) (n m : ℕ) :
    (pathG n □ pathG m).ECCAt k := by
  classical
  apply SimpleGraph.eccAt_of_degree_le_four_twenty _ _ hk
  intro v
  convert! GridGen.Polymer.degree_full_grid_le_four n m v

end ListColoring
