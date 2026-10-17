import GridGen.MaximumDegree
import GridGen.PolymerStability
import GridGen.PeelDegree

/-!
# Eventual ECC with a linear maximum-degree bound

One argument, `GridGen.Polymer.eccAt_of_parityCert` (`PolymerCertificate.lean`), with its
numbers abstracted into a `ParityCert`: a finite connected-block interpolation between
`P(G,k)` and `P(G,L)`, kept positive and monotone by a root budget on even-sized blocks and
nondecreasing by charging odd-sized blocks to the edges of their spanning trees.

Instances:
* `SimpleGraph.eccAt_of_maxDegree_bound`: every finite graph, `567 Δ ≤ 100 k`
  (hyperbolic certificate `parityCert_uniform`, `MaximumDegree.lean`);
* the degree-sensitive variant (`PolymerPeel*.lean`), which needs the deletion ratio only at
  vertices of residual degree `≤ Δ - 1`: `Δ ≤ 3, 4, 5, 6, 7, 8` at `k ≥ 11, 17, 22, 28, 33, 39`
  (`PeelDegree.lean`). The induction was proposed by Codex (OpenAI);
* the neighbour-pair variant (`PolymerPair*.lean`, `PolymerUpperRoot.lean`), also Codex's proposal:
  `Δ ≤ 4, 6, 8` at `k ≥ 16, 27, 38`.

The uniform `CertifiedAt` instance also gives strict inequality when two adjacent lists differ,
and the characterization of equality on connected graphs (`PolymerCertificate.lean`; stated in
`PolymerStability.lean`). `PolymerAxiomAudit.lean` checks their axioms. The argument, module by module, is in
`GridGen/README.md`.
-/
