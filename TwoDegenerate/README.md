# Two-degenerate graphs, and `K₂,ₙ` at list sizes three, four and five

The conjecture

> Every 2-degenerate graph is `ECCAt k` for every `k ≥ 4`

is false.  `K₂,₂₆` is 2-degenerate and is not `ECCAt 4` (`Counterexample.lean`).

More completely, for `k = 3, 4, 5` the thresholds are exact (`K2n/Main.lean`):

```lean
SimpleGraph.TwoDegenerate.completeBipartite_two_eccAt_three_iff (n : ℕ) :
  (completeBipartiteGraph (Fin 2) (Fin n)).ECCAt 3 ↔ n ≤ 11
SimpleGraph.TwoDegenerate.completeBipartite_two_eccAt_four_iff (n : ℕ) :
  (completeBipartiteGraph (Fin 2) (Fin n)).ECCAt 4 ↔ n ≤ 25
SimpleGraph.TwoDegenerate.completeBipartite_two_eccAt_five_iff (n : ℕ) :
  (completeBipartiteGraph (Fin 2) (Fin n)).ECCAt 5 ↔ n ≤ 43
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
Threshold from Above*, Involve **16** (2023), 849–882 (arXiv:2207.04831), Theorem 7, prove:
`K₂,ₙ` is ECC at three for `2 ≤ n ≤ 10` and not for `n ≥ 12`; at four for `2 ≤ n ≤ 24` and not
for `n ≥ 27`; at five for `2 ≤ n ≤ 43` and not for `n ≥ 44`. They state that `K₂,₁₁` at three and
`K₂,₂₅`, `K₂,₂₆` at four are unknown, and conjecture (their Conjecture 8) that ECC at `m` is
inherited from `K₂,ₙ₊₁` by `K₂,ₙ`. This development settles the three open cases:

| | list size | result |
|---|---|---|
| `K₂,₁₁` | 3 | ECC (least count 6,256 against 6,150, by exhaustive search outside Lean) |
| `K₂,₂₅` | 4 | ECC |
| `K₂,₂₆` | 4 | not ECC (the witness below) |

So the sets of `n` with `K₂,ₙ` ECC at three, four and five are `n ≤ 11`, `n ≤ 25` and `n ≤ 43`, and
their Conjecture 8 holds at `m = 3, 4, 5`. The `K₂,₂₆` witness is their own Lemma 11 family at
`n = 26 = 4·6 + 2`; their proof checks that family only from `n = 27`. As far as a targeted search
found, none of the three cases had been settled in the literature.

Reading the paper closely, the formal proofs differ from it as follows. Their positive
cases rest on AM–GM lower bounds (their Lemma 13 and case analyses) checked by floating-point
Python loops over all multiplicity vectors (their Appendix B); here every case is a kernel-checked
exact certificate. For large `n` their negative side cites Theorem 14 of Kaul–Kumar–Mudrock–Rewers–
Shin–To (arXiv:2202.03431); here an induction on `n / 4` for the Lemma 11 family replaces it
(`K2n/Witness.lean`). Their Lemma 5 (lists may be pushed into `A ∪ B`) appears here as
`exists_push`, proved without their hypothesis `m ≥ χℓ(G)`. Typographical slips noticed:
"`⌊n/4⌋ ≥ 9 ln(16/17)`" and "`16 ln(16/17)`" should read `16/7`, and in the proof of Theorem 7(iii),
case `d = 0`, "`[10]` choose `4`" should be "choose `5`". None affects a result.

## `K₂,ₙ` at list sizes three, four and five

**Positive side, `n ≤ 11, 25, 43`** (`K2n/Reduction.lean`, `K2n/Checker.lean`, generated
`K2n/Keys/`, `K2n/Cert/`, `K2n/Positive{3,4,5}.lean`).

1. **Push into `A ∪ B`** (`exists_push`).  Replacing a right list `T` by a `k`-subset of `A ∪ B`
   containing `T ∩ (A ∪ B)` never increases `|T \ {a,b}|` for `a ∈ A`, `b ∈ B`.
2. **Encode.**  With `A ∩ B`, `A \ B`, `B \ A` listed in increasing order, a right list is
   determined, for the count, by its membership bits; `|T \ {a_i, b_j}|` is the explicit
   `pairVal k r` of those bits (`card_sdiff_pair_eq_pairVal`).
3. **Group.**  Only the number `m_t` of right vertices of each type `t` matters; for each overlap
   `r = |A ∩ B|` the claim becomes `∑_p ∏_t W[t][p] ^ m_t ≥ k(k−1)ⁿ + k(k−1)(k−2)ⁿ` for all
   multiplicities summing to `n` (`colConst_K2n` is the right-hand side).
4. **Certificates.**  Branch-and-bound trees whose nodes close by weighted AM–GM with integer
   weights, `(∏ w_p^{w_p}) (∑ a_p)^D ≥ D^D ∏ a_p^{w_p}` (`amgm_finset`); `check_sound` proves the
   checker, `decide +kernel` runs it. Almost every `(k, n, r)` needs a single AM–GM node; the
   convex relaxation drops below the constant count only next to the thresholds, where integrality
   is essential and the trees grow (`k = 3, n = 11`: 91 nodes; `k = 4, n = 25`: 575 and 133;
   `k = 5, n = 43`: 761 and 469).

**Negative side, `n ≥ 12, 26, 44`** (`K2n/Witness.lean`, `K2n/Negative.lean`).  The hubs get
`A = {0,…,k−1}` and `B = {0,…,k−3} ∪ {k, k+1}`; right vertex `w` gets `{0,…,k−3} ∪ {a, b}` with
`(a, b)` cycling through four pairs as `w mod 4` does (Kaul et al.'s Lemma 11 family).  For
`n = 4q + s` the count is `∑ c_p G_p^q` with every `G_p ≤ (k−1)⁴`, so one base inequality per
residue `s` (checked by `decide`) propagates to every larger `q` (`sum_geom_lt`).

The certificates are regenerated, and re-checked in exact integer arithmetic, by

```sh
python3 TwoDegenerate/K2n/gen_k2n.py            # rewrite Keys/, Cert/, Positive{3,4,5}.lean
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
