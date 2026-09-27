# Two-degenerate graphs, and the exact threshold for `K₂,ₙ` at four

The conjecture

> Every 2-degenerate graph is `ECCAt k` for every `k ≥ 4`

is false.  `K₂,₂₆` is 2-degenerate and is not `ECCAt 4` (`Counterexample.lean`).  And `K₂,₂₅`
*is* `ECCAt 4` (`K2n/`), so `K₂,ₙ` is enumeratively chromatic-choosable at four exactly when
`n ≤ 25`:

```lean
SimpleGraph.TwoDegenerate.K2_25.eccAt_four :
  (completeBipartiteGraph (Fin 2) (Fin 25)).ECCAt 4
SimpleGraph.TwoDegenerate.K2_25.eccAt_four_twentyFive_and_not_twentySix
```

## Exact witness

Give the two vertices on the small side the lists

```text
A = {0,1,2,3}       B = {0,1,4,5}.
```

On the other side use these four lists with the displayed multiplicities:

```text
{0,1,2,4}  × 6       {0,1,2,5}  × 7
{0,1,3,4}  × 7       {0,1,3,5}  × 6.
```

For fixed colors `a ∈ A` and `b ∈ B`, the corresponding fiber contains

```text
∏_y |L(y) \ {a,b}|
```

colorings.  Summing the 16 fibers gives

```text
P(K₂,₂₆, L) =  9,925,029,789,650
P(K₂,₂₆, 4) = 10,168,268,619,684
gap            =    243,238,830,034.
```

The Lean proof is in `Counterexample.lean`.  It first proves the general `K₂,W` fiber formula,
then checks these small closed products with kernel reduction.  It also supplies the explicit
degeneracy ordering: put the two-vertex side first and all other vertices afterwards.

Run the independent arithmetic checker with:

```sh
python3 TwoDegenerate/verify_k2_26.py
```

## Relation to the literature

Kaul, Kumar, Liu, Mudrock, Rewers, Shin, Tanahara and To, *Bounding the List Color Function
Threshold from Above*, Involve **16** (2023), 849–882, Theorem 7(ii), proved equality for
`K₂,n` at four for `n ≤ 24`, strict inequality for `n ≥ 27`, and left `n = 25,26` open.
Their balanced-list formula, independently reevaluated here, already yields the witness above at
`n = 26`.  Thus this closes the `n = 26` case negatively, and `K2n/` closes `n = 25` positively,
over all four-list assignments.  Together with their theorem this determines the threshold
exactly.  As far as a targeted search found, neither case had been settled in the literature.

## `K₂,₂₅` is ECC at four

Every four-list assignment has at least `P(K₂,₂₅, 4) = 4·3²⁵ + 12·2²⁵ = 3,389,557,090,956`
colorings.  The proof has three reductions and a certificate.

1. **Push into `A ∪ B`** (`K2n/Reduction.lean`, `exists_push`).  Replacing a right list `T` by a
   four-subset of `A ∪ B` containing `T ∩ (A ∪ B)` never increases `|T \ {a,b}|` for `a ∈ A`,
   `b ∈ B`, so it never increases the count.
2. **Encode.**  With `A ∩ B`, `A \ B`, `B \ A` listed in increasing order, a right list is
   determined, for the count, by its membership bits; `|T \ {a_i, b_j}|` is an explicit function
   `pairVal` of those bits (`card_sdiff_pair_eq_pairVal`).
3. **Group.**  Only the number `m_t` of right vertices of each type `t` matters, so the claim
   becomes, for each overlap `r = |A ∩ B|`,

   ```text
   ∑_{16 pairs p} ∏_t W[t][p] ^ m_t  ≥  4·3²⁵ + 12·2²⁵   whenever  ∑_t m_t = 25,
   ```

   with `C(8 − r, 4)` types (70, 35, 15, 5, 1 for `r = 0, …, 4`).
4. **Certificate** (`K2n/Checker.lean`, `K2n/R0.lean` … `R4.lean`).  A branch-and-bound tree over
   the multiplicities whose nodes are closed by weighted AM–GM with integer weights `k`:
   `(∏ k_p^{k_p}) (∑ a_p)^D ≥ D^D ∏ a_p^{k_p}`.  The continuous relaxation is convex, and its
   minimum is above the constant count for `r = 0, 1` (ratios 1.92 and 1.37), so one AM–GM node
   suffices there; for `r = 2, 3` it is *below* it (0.986 and 0.9993), so integrality is
   essential, and the trees have 597 and 163 nodes.  `r = 4` forces the constant assignment.
   `check_sound` proves the checker correct; `decide +kernel` runs it on the data, about 50 s in
   total on this machine.

By exhaustive integer search (outside Lean), the true minima for `r = 2` and `r = 3` are 1.0051
and 1.0090 times the constant count, attained at multiplicities `(7, 6, 5, 6)` plus one extra type,
and `(12, 12, 1)`.  With the one-line argument for `r = 4` (a right list `T ≠ A` misses some
`c ∈ A`, and the fiber `(c, c)` then gains a factor `4/3`), this would make the inequality strict
for every non-constant assignment; that strengthening is not formalized.  The certificates are regenerated, and re-checked in exact
integer arithmetic, by

```sh
python3 TwoDegenerate/K2n/gen_k2n.py            # rewrite R0..R4.lean
python3 TwoDegenerate/K2n/gen_k2n.py --check    # confirm the committed files (needs numpy)
```

## What survives of the research direction

Degeneracy by itself cannot provide a uniform ECC threshold: the family `K₂,n` is 2-degenerate
while its list-color-function threshold is unbounded.  It also shows why plain induction under
"add a vertex adjacent to two earlier vertices" cannot work: repeating that operation on the same
nonedge eventually destroys `ECCAt 4`.

The grid-motivated replacement should control this repetition.  Rectangular grids have maximum
degree at most four and every pair of vertices has at most two common neighbors, whereas `K₂,₂₆`
has a pair with 26 common neighbors.  A plausible next falsification target is therefore:

> Every 2-degenerate graph with maximum degree at most four and pair-codegree at most two is
> `ECCAt k` for every `k ≥ 4`.

This is a conjectural search target, not a theorem.  It should be attacked computationally before
any further general induction is developed.
