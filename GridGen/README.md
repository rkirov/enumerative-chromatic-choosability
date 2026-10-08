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
| `GridGen.Polymer.colConst_lt_col_of_certifiedAt_of_adj` | any threshold above; two adjacent lists differ | `P(G,k) < P(G,L)` |
| `GridGen.Polymer.col_eq_colConst_iff_of_certifiedAt` | any threshold above; `G` connected | `P(G,L) = P(G,k)` iff `L` is constant |

`PolymerStability.lean` restates the last two at the uniform threshold under the names
`SimpleGraph.colConst_lt_col_of_degree_bound_of_adj_lists_ne` and
`SimpleGraph.col_eq_colConst_iff_constant_of_degree_bound`. For comparison, the ceiling bound gives
18, 23, 29, 35, 40, 46 at `Δ = 3, …, 8`. `lake build GridGen.PolymerAxiomAudit` runs 28 guarded
transitive axiom checks, each exactly `[propext, Classical.choice, Quot.sound]`.

None of this is ECC at *every* list size (`K₂,₄ ⊂` degree-four graphs fails at 2), and no threshold
is claimed optimal. For grids the list sizes `3 ≤ k ≤ 16` stay open at heights `≥ 4`.

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
Degree four at 19, or a factor near 5, would need a new idea. For example, the root recursion
could keep the cancellation between neighbouring positive and negative blocks instead of
bounding each adverse block separately.

## Credit

The ingredients are not new, and neither is the positivity half:

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
