# `GridGen/` — maximum-degree thresholds, and the general-height grid reduction

Two independent developments share this library.

1. **The polymer route** (`Polymer*.lean`, `PolymerCertificate.lean`, `MaximumDegree.lean`,
   `DegreeFourTwenty.lean`, `SmallDegree.lean`, `PolymerStability.lean`): every finite graph of
   maximum degree `Δ` is `k`-ECC once `k` is linear in `Δ`, with no hypothesis on order,
   connectedness, planarity or bipartiteness. Complete, with no unproved step, axiom-audited.
2. **The column-lookback reduction** (`Column`, `Graph`, `Telescope`, `Uniform`, `Main`,
   `Explicit`, `Three`): `H □ P_n` is `k`-ECC from a two-step seam inequality and an initial
   inequality, both stated as `Prop`s; proved at height three from `Grid3/`, open at height ≥ 4.
   See `ai_research_notes/GRID_REVIEW_2026-09-02.md` §5.6.

The rest of this file is about the polymer route.

## Statements

| Lean name | Hypothesis | Conclusion |
|---|---|---|
| `SimpleGraph.eccAt_of_degree_bound` | every degree `≤ D`, `567 D ≤ 100 k` | `G.ECCAt k` |
| `SimpleGraph.eccAt_of_maxDegree_bound`, `…_ceiling` | `567 Δ ≤ 100 k`, i.e. `k ≥ ⌈5.67 Δ⌉` | `G.ECCAt k` |
| `SimpleGraph.eccAt_of_degree_le_three` | `Δ ≤ 3`, `k ≥ 15` | `G.ECCAt k` |
| `SimpleGraph.eccAt_of_degree_le_four_twenty` | `Δ ≤ 4`, `k ≥ 20` | `G.ECCAt k` |
| `ListColoring.ecc_boxProd_pathG_of_twenty` | any rectangle `P_n □ P_m`, `k ≥ 20` | ECC at `k` |
| `SimpleGraph.eccAt_of_degree_le_{five,six,seven,eight}` | `Δ ≤ 5, 6, 7, 8`; `k ≥ 26, 32, 37, 43` | `G.ECCAt k` |
| `SimpleGraph.eccAt_of_degree_le_three_eleven` … `_eight_thirtyNine` | `Δ ≤ 3, …, 8`; `k ≥ 11, 17, 22, 28, 33, 39` | `G.ECCAt k` (degree-sensitive, `PeelDegree.lean`) |
| `SimpleGraph.eccAt_of_degree_le_four_seventeen` | `Δ ≤ 4`, `k ≥ 17` | `G.ECCAt k` |
| `ListColoring.ecc_boxProd_pathG_of_seventeen` | any rectangle `P_n □ P_m`, `k ≥ 17` | ECC at `k` |
| `SimpleGraph.eccAt_of_degree_le_{four_sixteen,six_twentySeven,eight_thirtyEight}` | `Δ ≤ 4, 6, 8`; `k ≥ 16, 27, 38` | `G.ECCAt k` (neighbour pairs, `PeelDegree.lean`) |
| `ListColoring.ecc_boxProd_pathG_of_sixteen` | any rectangle `P_n □ P_m`, `k ≥ 16` | ECC at `k` |
| `GridGen.Polymer.colConst_lt_col_of_certifiedAt_of_adj` | a `CertifiedAt` threshold (rows 1–6); two adjacent lists differ | `P(G,k) < P(G,L)` |
| `GridGen.Polymer.col_eq_colConst_iff_of_certifiedAt` | a `CertifiedAt` threshold (rows 1–6); `G` connected | `P(G,L) = P(G,k)` iff `L` is constant |

`PolymerStability.lean` restates the last two at the uniform threshold under the names
`SimpleGraph.colConst_lt_col_of_degree_bound_of_adj_lists_ne` and
`SimpleGraph.col_eq_colConst_iff_constant_of_degree_bound`. For comparison, the ceiling bound gives
18, 23, 29, 35, 40, 46 at `Δ = 3, …, 8`. `lake build GridGen.PolymerAxiomAudit` runs 41 guarded
transitive axiom checks, each exactly `[propext, Classical.choice, Quot.sound]`.

None of this is ECC at *every* list size (`K₂,₄ ⊂` degree-four graphs fails at 2), and no threshold
is claimed optimal. For grids the list sizes `3 ≤ k ≤ 15` stay open at heights `≥ 4`.

## The argument

Fix a `k`-list assignment `L`. For a vertex set `S` let `d(S) = k − |⋂_{v∈S} L(v)|` and let
`c(S) = Σ (−1)^{|F|}` over edge sets `F ⊆ E(G[S])` connecting `S`. Grouping Whitney's expansion
by connected components gives, for `t ∈ [0,1]`,

    Z_t(U) = Σ_{partitions π of U} Π_{S∈π} c(S) (k − t d(S)) x^{|S|},

with `Z_0(V) = x^{|V|} P(G,k)` and `Z_1(V) = x^{|V|} P(G,L)` (`PolymerEndpoints.lean`). So it is
enough that `t ↦ Z_t(V)` is nondecreasing.

* **Signs.** A sign-reversing cancellation leaves only spanning trees, so
  `|c(S)| ≤ #trees(G[S])` and `(−1)^{|S|−1} c(S) ≥ 0` (`PolymerCancellation`, `PolymerTreeGraph`,
  `PolymerSigns`). Only even-sized blocks have negative activity, and only odd-sized blocks of
  size `≥ 3` can make the derivative negative.
* **Positivity.** A root recursion, charging only the negative (even-sized) blocks, proves
  `Z_t(U) > 0` and `Z_t(B) ≤ Z_t(U)` for `B ⊆ U` by strong induction, whenever the even-block
  penalty at every root is at most `k x − 1` (`PolymerRatio`, `PolymerModel`, `PolymerParityActivity`).
* **Derivative.** `Z'_t(U) = −Σ_S c(S) d(S) x^{|S|} Z_t(U∖S)`. Edges contribute `d_e x² Z_t(U∖e) ≥ 0`.
  An odd block's deficiency is at most the sum of `d_e` along any of its spanning trees (the
  Wang–Qian–Yan inequality, `PolymerDeficiency`), so each block is charged to the edges of its
  individual trees, and deletion monotonicity moves `Z_t(U∖S)` up to `Z_t(U∖e)`
  (`PolymerGraphCharge`, `PolymerParityMonotonicity`).
* **Counting trees.** Spanning trees inject, weight-preservingly, into non-backtracking walk-tree
  codes: rooted at a vertex (`D` child ports, then `D − 1`), or split at an anchor edge into two
  branches (`PolymerWalkTree`, `PolymerTreeEncoding`, `PolymerTreeSize`, `PolymerEdgeEncoding`).
  Split by parity, a branch's even and odd masses `(E, O)` multiply like `(a + b z)` in
  `ℝ[z]/(z² − 1)`: an optional child contributes `(1 + x O, x E)` (`parityPower`,
  `PolymerParityBounds`, `PolymerParityCount`).

### The certificate

All the numbers enter through one structure (`PolymerParityBounds.lean`):

```
structure ParityCert (D : ℕ) (x₀ e o r : ℝ) : Prop where
  branch : parityPower (1 + x₀ o) (x₀ e) (D − 1) ≤ (e, o)      -- componentwise
  root   : (parityPower (1 + x₀ o) (x₀ e) D).odd ≤ r
  edge   : 2 e o < 1
```

`CertifiedAt D k` asks for a certificate, an activity `x ≤ x₀`, and the root budget `k x r ≤ k x − 1`.
Under it the derivative is at least `(1 − 2eo) Σ_e d_e x² Z_t(U∖e)`. That gives ECC, strictness
when some edge has unequal lists, and the equality case (`PolymerCertificate.lean`).
`certifiedAt_of_parityCert` scales a certificate at `x₀ = s / k₀` with `s r ≤ s − 1` to every `k ≥ k₀`.

| instance | `D` | `k₀` | `s` | `e` | `o` | `r` |
|---|---|---|---|---|---|---|
| `parityCert_degree_three` | 3 | 15 | 3/2 | 132/125 | 27/125 | 1/3 |
| `parityCert_degree_four` | 4 | 20 | 17/10 | 553/500 | 3/10 | 7/17 |
| `parityCert_degree_five` | 5 | 26 | 8/5 | 111/100 | 29/100 | 3/8 |
| `parityCert_degree_six` | 6 | 32 | 3/2 | 11/10 | 7/25 | 1/3 |
| `parityCert_degree_seven` | 7 | 37 | 8/5 | 9/8 | 63/200 | 3/8 |
| `parityCert_degree_eight` | 8 | 43 | 8/5 | 113/100 | 8/25 | 3/8 |
| `parityCert_uniform` | any | `k` | 100/63 | 117/100 | 37/100 | 37/100 |

The finite instances are checked by `norm_num`. The uniform one bounds `parityPower` by
`(e^{ot} cosh(et), e^{ot} sinh(et))` at `t = n x`, and checks the endpoint `t = 10000/35721` with
Mathlib's degree-seven Taylor bound for `exp` (`PolymerUniformBounds.lean`).

Numerically, the finite thresholds above are the least this certificate shape reaches for each
`D`: the root budget binds, not the edge budget. The uniform constant tends to about `5.6634`.
For this certificate, degree four at 19 would need a new idea; the two variants below are such
ideas.

### Degree-sensitive variants

* **Peeling** (`PolymerPeel`, `PolymerPeelGraph`, `PolymerPeelRoot`, `PolymerPeelCertificate`).
  The ratio `Z_t(U − u) ≤ Z_t(U)` is claimed only when `u` has at most `D − 1` neighbours in `U`.
  Every comparison the argument makes deletes a connected block outward from a root or an anchor
  edge (`PeelChain`), so each step removes a vertex that has already lost a neighbour. At such a
  root the harm counts trees of `G[U]` (`restrictTo G U`) with `D − 1` ports, so the budget is
  `k x o ≤ k x − 1` with the branch mass `o`; a full-degree root needs only positivity, `r < 1`.
  This is `CertifiedPeelAt`.
* **Neighbour pairs** (`PolymerPairBlocks`, `PolymerUpperRoot`, `PolymerPairRoot`,
  `PolymerPairCertificate`). A third claim joins the induction, `Z_t(U) ≤ k x Z_t(U − u)` at every
  vertex: the edges at a root outweigh the odd blocks charged to them, by `2eo < 1`. With it each
  positive block `{v, u, w}` (`u, w` neighbours of `v`; coefficient `1`, or `2` for a triangle) is
  worth at least `x / k` relative to `Z_t(U − v)`, and the deficient edges' savings pay for the
  pairs' deficiencies once `(D − 2) x³ ≤ x / k`. A root with `D − 1` neighbours gains
  `C(D − 1, 2) x / k`; roots with fewer use the `D − 2`-port mass. This is `CertifiedPairAt`.

| `D` | peel `k₀` | `s` | `e` | `o` | `r` | pair `k₀` | `s` | `e` | `o` | `r` |
|---|---|---|---|---|---|---|---|---|---|---|
| 3 | 11 | 71/50 | 549/500 | 59/200 | 231/500 | — | | | | |
| 4 | 17 | 7/5 | 549/500 | 57/200 | 391/1000 | 16 | 13/8 | 117/100 | 39/100 | 11/20 |
| 5 | 22 | 3/2 | 283/250 | 333/1000 | 427/1000 | — | | | | |
| 6 | 28 | 73/50 | 1121/1000 | 157/500 | 77/200 | 27 | 159/100 | 146/125 | 19/50 | 47/100 |
| 7 | 33 | 8/5 | 583/500 | 3/8 | 56/125 | — | | | | |
| 8 | 39 | 38/25 | 571/500 | 341/1000 | 99/250 | 38 | 79/50 | 117/100 | 379/1000 | 9/20 |

The pair certificates are stated at `k₀` only; larger `k` use the peel instances. Numerically
neither family goes further. For grids at `k = 15` the best degree-three root budget misses by
about four percent, and removing the grid's 4-cycles from the walk-tree count recovers a tenth of
that. To first order the root's edges alone need `s (1 − 3s/k) ≥ 1`, which already forces
`k ≥ 12`. Arbitrary heights below 16 need a different method.

## Credit

The ingredients are not new, and neither is the positivity half:

* the degree-sensitive deletion ratio, and the neighbour-pair refinement with its upper ratio, were
  proposed by Codex (OpenAI), consulted on 2026-10-07
  (`ai_research_notes/CODEX_GRID_ALL_HEIGHTS_2026-10-07.md` §3). The formalization, the
  certificates other than degree four, and the `D − 2`-port treatment of smaller roots are this
  repository's;

* the connected-block (polymer) expansion and the tree-graph bound are standard; see Sokal,
  *Bounds on the complex zeros of (di)chromatic polynomials and Potts-model partition functions*
  (2001);
* the deficiency inequality along a tree is Wang–Qian–Yan (2017), as quoted in Lemma 10 of
  Zhang–Dong below;
* the interpolation between `P(G,k)` and `P(G,L)` with tree-wise deficiency charging is the method of
  Zhang–Dong, *When chromatic polynomials coincide with list-color functions: a threshold linear
  in the maximum degree*, arXiv:2609.08540 (September 2026), who prove `k ≥ 23.41 Δ` with a
  quantitative strictness estimate;
* **the constants coincide with Dong–Koh**, *Bounds for the real zeros of chromatic polynomials*,
  Combin. Probab. Comput. **17** (2008). They prove `P(G,q) ≠ 0` for real `q ≥ 5.664 Δ`, and
  `q ≥ 4.765 Δ` when `Δ = 3`. This proof's limiting constant is 5.6634, and at `Δ = 3` it reaches
  `k ≥ 15 > 3 · 4.765`. We have not compared the two proofs line by line. The agreement suggests
  their bound rests on the same sign-separated root recursion, so the positivity half of this
  argument should be credited to them. Positivity of `P(G,q)` alone is weaker than what is known:
  Bencs–Regts (arXiv:2505.04366) exclude all complex zeros with `|q| ≥ 4.25 Δ`.

What this development adds is the *list-colouring comparison* at these constants. Positivity and
monotonicity of the interpolation carry over from the real-root recursion, with only even blocks
charged. The derivative charges only odd blocks, to individual trees, and keeps the edge-deletion
partition functions. At `Δ = 4` this gives 20 against the 94 that Zhang–Dong's bound gives there.
This is a formal result of a 2026 AI research collaboration, not a claim of priority beyond the
comparison stated. The literature check is targeted, not exhaustive
(`MAX_DEGREE_ECC_LITERATURE_2026-09-12.md`).

## Build

```sh
lake build GridGen                     # everything, including the polymer route
lake build GridGen.PolymerAxiomAudit   # 28 guarded axiom checks
python3 GridGen/polymer_audit.py --max-n 5 --grids   # independent exact-arithmetic bug detector
python3 GridGen/parity_budget_review.py --explore    # rational certificates and numerical minima
```

The polymer route imports no seam certificate and evaluates no `Finpartition` instance. History:
the threshold went 544 → 25 (tree-wise charging) → 20 (coefficient signs), then was generalized to
`⌈5.67 Δ⌉` and factored through `ParityCert` (2026-09-23). The superseded modules and dated
notes are kept, untracked, in `ai_research_notes/gridgen_retired_threshold25/` and
`ai_research_notes/gridgen_history/`.
