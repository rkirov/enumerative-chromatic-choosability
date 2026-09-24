import GridGen.MaximumDegree
import GridGen.DegreeFourTwenty
import GridGen.SmallDegree
import GridGen.PolymerStability

/-!
# Eventual ECC with a linear maximum-degree bound

One argument, `GridGen.Polymer.eccAt_of_parityCert` (`PolymerCertificate.lean`), with its
numbers abstracted into a `ParityCert`: a finite connected-block interpolation between
`P(G,k)` and `P(G,L)`, kept positive and monotone by a root budget on even-sized blocks and
nondecreasing by charging odd-sized blocks to the edges of their spanning trees.

Instances:
* `SimpleGraph.eccAt_of_maxDegree_bound`: every finite graph, `567 Δ ≤ 100 k`
  (hyperbolic certificate `parityCert_uniform`, `MaximumDegree.lean`);
* `SimpleGraph.eccAt_of_degree_le_four_twenty`: `Δ ≤ 4`, `k ≥ 20`, with the rectangle
  corollary `ListColoring.ecc_boxProd_pathG_of_twenty` (`DegreeFourTwenty.lean`);
* `Δ ≤ 3, 5, 6, 7, 8` at `k ≥ 15, 26, 32, 37, 43` (`SmallDegree.lean`).

Every instance also gives strict inequality when two adjacent lists differ, and the
characterization of equality on connected graphs (`PolymerCertificate.lean`; stated at the
uniform threshold in `PolymerStability.lean`). `PolymerAxiomAudit.lean` checks their axioms. The argument, module by module, is in
`GridGen/README.md`.
-/
