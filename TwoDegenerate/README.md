# Two-degenerate graphs: the conjecture fails

The conjecture

> Every 2-degenerate graph is `ECCAt k` for every `k ≥ 4`

is false.  `K₂,₂₆` is 2-degenerate and is not `ECCAt 4`.

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
`n = 26`.  Thus this closes the `n = 26` case negatively.  The `n = 25` case is not settled here.

The verifier exhausts every multiplicity vector for the four displayed right-list types.  Within
that restricted family, no witness exists at `n = 25`; this is not an exhaustion of all four-list
assignments.

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
