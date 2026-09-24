# Maximum degree and eventual ECC

Literature checked: 2026-09-12, extended 2026-09-23 (chromatic-root bounds). This note does not
establish a priority or best-known-bound claim. The formal results and the argument are in
[`README.md`](README.md): ECC for `567 Δ ≤ 100 k`, and sharper finite-degree thresholds
(`Δ ≤ 3, 4, 5, 6, 7, 8` at `k ≥ 15, 20, 26, 32, 37, 43`), all from one parity certificate, with
strict inequality whenever adjacent lists differ.

## Real and complex chromatic roots (added 2026-09-23)

- Dong–Koh, *Bounds for the real zeros of chromatic polynomials*, Combin. Probab. Comput. 17(6)
  (2008): every real zero of `P(G,q)` lies in `[0, 5.664Δ)`; for `Δ = 3`, in `[0, 4.765Δ)`.
  **These are the constants this development's certificate reaches** (limit ≈ 5.6634; `Δ = 3`
  at 15 > 14.295). The positivity half of the argument (the root recursion with sign-separated
  tree counts) should be credited to them, pending a line-by-line comparison of the proofs.
- Sokal (2001), complex zeros in `|q| < 7.963907Δ`; Fernández–Procacci (2008), `6.91Δ`, using
  Penrose's tree identity; Jenssen–Patel–Regts, `5.94Δ`; Bencs–Regts, arXiv:2505.04366 (2025/26),
  `4.25Δ` in general, `3.60Δ` for large girth, `3.81Δ` for claw-free graphs.
- So `P(G,k) > 0` at our thresholds is already known and weaker than known. What is not in this
  literature is the comparison `P(G,L) ≥ P(G,k)` with every `k`-list assignment, which needs the
  derivative half as well.

## Directly relevant degree result

Zhang and Dong's September 8, 2026 preprint proves equality for `k ≥ 23.41Δ`, `Δ ≥ 3`.
Its Theorem 5 also gives a quantitative exponential improvement for nonconstant adjacent
lists. Components reduce the disconnected case; degrees at most two are treated separately.
Thus its degree-four specialization gives integer threshold 94.
[Primary source, Theorem 5](https://arxiv.org/html/2609.08540v1).

Their method overlaps substantially: connected-set expansions, interpolation, tree bounds,
and treewise deficiency charging. Lemma 10 attributes the deficiency inequality to
Wang–Qian–Yan. Lemmas 8–9 concern vertex- and edge-rooted trees; Lemma 12 controls polymer
deletion ratios. These ingredients must not be advertised as new here.
[Primary source, Sections 2–3](https://arxiv.org/html/2609.08540v1).

Our formalized refinement retains actual edge-deletion partition functions in the charging
comparison, uses `Δ − 1`-child branch majorants, and charges only adverse coefficient parities.
Its degree-four constant is 20, versus the above sufficient constant 94, and its general factor
is 5.67 versus 23.41. This is not a claim that the literature search exhausts every other result.

## Other relevant results and limitations

- Dong–Zhang, JCTB 161 (2023), 109–119: for graphs with `m ≥ 4` edges, equality holds
  for `k ≥ m−1`, with a quantitative deficiency lower bound. This is an edge-count bound,
  not a size-independent degree bound. It can still be better on small graphs.
  [Original article](https://www.sciencedirect.com/science/article/abs/pii/S0095895623000096).
- Kaul et al., *On the List Color Function Threshold*, JGT 105 (2024), 386–397:
  `τ(K_{2,n}) − χℓ(K_{2,n}) ≥ c√n` for a fixed positive constant and `n ≥ 16`.
  [Original paper](https://arxiv.org/abs/2202.03431).
  Since `K_{2,n}` has maximum degree `n`, degeneracy two, and average degree below four,
  this implies that neither bounded degeneracy nor bounded average degree can replace
  bounded maximum degree in a universal constant-threshold statement.
- Kaul et al., *Bounding the List Color Function Threshold from Above*, Involve 16 (2023),
  849–882: `τ(K_{2,4}) = τ(K_{2,5}) = 3`; the paper also recalls ECC for cycles and chordal
  graphs. [Original paper](https://arxiv.org/abs/2207.04831).
  Consequently maximum degree at most four does **not** imply ECC at every list size:
  `K_{2,4}` already fails at two. Graphs of maximum degree at most two, by contrast, are
  disjoint unions of paths, cycles, and isolated vertices, and are ECC at every size.
- Sokal's *Bounds on the Complex Zeros of (Di)Chromatic Polynomials and Potts-Model
  Partition Functions* supplies the polymer/tree-counting background, not by itself a
  list-count comparison. [Original paper](https://arxiv.org/abs/cond-mat/9904146).

Ordinary list-colorability guarantees existence of a coloring. ECC asks for at least
the full uniform-list count, so an existence bound alone does not finish this project.

## Implementation framing

The generic argument is `GridGen.Polymer.CertifiedAt` (`PolymerCertificate.lean`); every
threshold is a `ParityCert` instance. `lake build GridGen.PolymerAxiomAudit` runs 28 guarded
transitive axiom checks. No unproved target proposition is used.
