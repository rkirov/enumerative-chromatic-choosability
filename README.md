# List coloring and enumeratively chromatic-choosable graphs — a Lean 4 formalization

[![CI](https://github.com/rkirov/enumerative-chromatic-choosability/actions/workflows/ci.yml/badge.svg)](https://github.com/rkirov/enumerative-chromatic-choosability/actions/workflows/ci.yml)

📖 **[Read the companion book](https://rkirov.github.io/enumerative-chromatic-choosability/)**

A machine-checked development of Kirov & Naimi, *List coloring and n-monophilic graphs*,
Ars Combinatoria **124** (2016), 329–340 ([arXiv:1004.5183](https://arxiv.org/abs/1004.5183)).

Give each vertex of a graph its own list of `n` permitted colors and count the proper colorings
respecting those lists. A graph is **enumeratively chromatic-choosable at `n`** when that count is
minimized by giving every vertex the *same* list. Kostochka and Sidorenko raised the question in
1990; Kirov and Naimi prove that every cycle is enumeratively chromatic-choosable at `n` for every
`n`, characterize the graphs that are enumeratively chromatic-choosable at `2`, and construct, for
each `n`, a graph that is `n`-choosable but not enumeratively chromatic-choosable at `n`.

**A note on the name.** Kirov and Naimi call this property "`n`-monophilic". The name the literature
settled on is *enumeratively chromatic-choosable* (Kaul et al., Involve **16** (2023) 849–882;
Allred–Mudrock, [arXiv:2505.05662](https://arxiv.org/abs/2505.05662); Chi et al.,
[arXiv:2605.10861](https://arxiv.org/abs/2605.10861)), and that is the name used throughout this
development: `SimpleGraph.ECCAt G n` for the property at one `n`, and `SimpleGraph.ECC G` for
`∀ n, G.ECCAt n`. `provenance.md` §4 records the history, the relation to Ohba's
*chromatic-choosable*, and the invariants `ν(G)` and `τ(G)` the modern papers state things with.

As far as we can determine, **list coloring and choosability have not been formalized in any proof
assistant before**, and Mathlib at the revision targeted here has no chromatic polynomial, no
choosability, no DP-coloring, no chordality, and no Brooks or Vizing. Everything here is built from
`SimpleGraph` and `Finset`.

## Layout

| | |
|---|---|
| `ListColoring/` | the formalization |
| `Cacti/` | the cactus classification — beyond the paper, see below |
| `Ladder/` | ladders are `k`-ECC for every `k ≥ 3` — beyond the paper, see below |
| `Grid3/` | height-three grids are `k`-ECC for every `k ≥ 3` (`Grid3/Four/` is the `k = 4` case, `Grid3/Three/` the `k = 3` case) — beyond the paper, see below |
| `NonPersistence/` | Zhang–Dong's theorem, which refutes Kirov–Naimi §6 Question 2 |
| `TwoDegenerate/` | the formal `K₂,₂₆` counterexample to a uniform 2-degenerate-graph conjecture |
| `OpenProblems.lean` | Kirov–Naimi §6's questions; Question 1 still open and asserted with `sorry`, Question 2 **refuted** |
| `formalization.yaml` | machine-readable map: every numbered result of the paper → its Lean name, file, and status |
| `book/` | a Verso textbook companion (see `book/README.md`) |
| `plan.md` | milestones, design decisions, progress log, and findings |
| `references.md` | verified bibliography, with corrections to the literature |
| `check-submission.py` | lints the repository against a registry's mechanical requirements — licence, metadata, layout |
| `provenance.md` | **credit ledger** — which theorem in which paper each result is, and what is not claimed |
| `survey.md` | the original scoping report that started the project |

## Building

Toolchain: `leanprover/lean4:v4.33.0`; Mathlib is pinned in `lake-manifest.json`.

```sh
lake exe cache get     # fetch Mathlib oleans (first time only)
lake build             # the formalization
```

For the companion book (Verso `v4.33.0`):

```sh
cd book
lake build                                                     # checks every example in the text
lake env lean --run Main.lean --output _out --depth 2 --without-tex
python3 -m http.server 8000 --directory _out/html-multi        # Verso needs a server, not file://
```

Two notes carried over from development, both recorded in `plan.md`:

* The book deliberately declares **no `lean_exe`** — linking a native binary that imports Mathlib
  forces compiling all of Mathlib to object code (~2700 jobs, several GB). Hence the interpreted
  `lake env lean --run` invocation above.
* On the machine this was developed on, `.lake/packages` was a symlink into a sibling Mathlib
  checkout to save disk. That is a purely local optimisation, is `.gitignore`d, and is not needed
  for a fresh clone.

## What is proved

| Paper result | |
|---|---|
| Lemma 1 (cone over a clique) | ✅ |
| Kostochka–Sidorenko — every graph with a simplicial elimination ordering | ✅ |
| Lemma 2 (list swap → nested lists) | ✅ |
| Lemma 3(a),(b),(c) — the `A_k`/`B_k` recurrences and minimizing assignments | ✅ |
| Lemma 4 (strict monotonicity on paths) | ✅ |
| **Theorem 1 — every cycle is enumeratively chromatic-choosable at `n`, every `n ≥ 2`** | ✅ |
| Lemma 5 (cores, as pendant towers) | ✅ |
| Lemma 6 (`K₂,₃` is enumeratively chromatic-choosable at `2`) | ✅ |
| **Theorem 2** — the characterization of the graphs enumeratively chromatic-choosable at `2`, unconditionally | ✅ |
| §5 building block — `K_{n,nⁿ}` is `n`-colourable but not `n`-choosable | ✅ |
| §5 Lemmas 7, 8, 9, 10 and the full `H_{n+1}` construction | ✅ |
| **§5's conclusion at every list size `k ≥ 2`** — a graph that is `k`-choosable but not enumeratively chromatic-choosable at `k` | ✅ |

**One erratum in the paper, at `n = 1`.** Lemmas 7 and 10 of §5 are stated "for all `n ≥ 1`", i.e.
down to list size `2`. Lemmas 7, 9 and 10 are all false there, and
`ListColoring/Section5.lean` therefore assumes `2 ≤ n` throughout. The reason is structural: `p` is
defined as the least integer with `nᵖ > x^{n²}`, which at `n = 1` reads `1 > x` with
`x = col(K_{1,1}, L_j) = 2` — no such `p` exists, so `H₂` is not defined. Take any `p` anyway and
`v₁` is joined to both ends of the single edge of `G_{1,1} = K_{1,1}`, so `H₂` contains a triangle;
then `col(H₂, 2) = 0 < 2 = col(H₂, L)`, which is Lemma 7's inequality reversed, and `H₂` is not
`2`-colourable, so it is not `2`-choosable either. All three failures are `#guard`s at the foot of
that file. The paper's conclusion is unaffected: list size `2` is witnessed instead by `θ_{2,2,4}`,
`2`-choosable by Rubin and not enumeratively chromatic-choosable at `2` by the paper's own Figure 2
— both already proved here, and combined in
`SimpleGraph.KN5.exists_choosable_not_ecc_of_two_le`. This is the only error found in Kirov–Naimi;
`provenance.md` §3 records it, along with the rather longer list of claims of *ours* that were
refuted.

One dependency is worth stating plainly. **Rubin's characterization of 2-choosable graphs** (A. L.
Rubin, in Erdős–Rubin–Taylor 1980, pp. 131–134) had not, as far as we can determine, been formalized
anywhere. It is proved here, in both directions — `ListColoring.rubinTheorem` — out of
`choosable_two_of_rubinFamily` (⟸), the generalized-theta classification
`choosable_two_gtheta_iff` (arbitrary arity), the dumbbell case `not_choosable_two_of_dumbbell`,
Rubin's steps 4–6 (`rubin_structure`) and the core extraction (`hasCore`). It is a theorem from
1980; none of the mathematics is ours.

Kirov–Naimi's Theorem 2 is stated in `ListColoring/Theorem2.lean` with `RubinTheorem` as its first
explicit argument and the core alternatives as **real definitions** rather than abstract
propositions; `ListColoring.ecc_two_iff` supplies that argument, so Theorem 2 now assumes
nothing beyond connectivity. (The two live in different files only because everything Rubin's
theorem is proved from imports `ListColoring/Theorem2.lean`.)

## Beyond the paper: the cactus classification

`Cacti/` proves a result that is not in Kirov–Naimi and, as far as we know, not in the literature:
**the complete enumerative-chromatic-choosability spectrum of a cactus.** A *cactus* is a connected
graph in which any two cycles sharing an edge are the same cycle.

> A cactus is enumeratively chromatic-choosable — at *every* list size — iff it has at most one
> cycle or contains an odd cycle. (`ListColoring.isCactus_ecc_iff`)

The proof, in outline. Fix a root `r`. Both sides of `colConst k ≤ col L` are statements about the
*rooted profile* at `r` — the count of colourings per colour of `r` — so the goal is
`k·A ≤ ∑_c x_c`, where `A` is the uniform profile. That sum is what a cut vertex fails to respect,
so the induction over the block structure carries a pointwise bound on the profile instead and
converts to the sum only at the root, by an inequality of arithmetic-geometric type. The recursion
has one hard case: a cactus with no cut vertex is a single cycle.

Which pointwise bound depends on the list size, and that is the whole difficulty:

| | |
|---|---|
| `k ≥ 4` | the pair bound `A² ≤ x_c·x_d`. Peeling a block costs a factor, and the slack `k - 3 ≥ 1` pays for it |
| `k = 3` | the slack is exactly zero and the pair bound is **false**. GM dominance `A³ ≤ ∏_c x_c` replaces it, with every step tight — equality at the uniform configuration — so nothing anywhere may be discarded |
| `k = 2` | not a counting argument at all: an odd cycle makes both counts zero, and a cactus with two even cycles has none of the cores Theorem 2 allows |

The cycle blocks are where the three cases differ, and they split by parity. An odd cycle admits a
*balanced core* — a subfamily of colourings hitting every vertex-colour pair exactly `A` times —
at every list size, so odd cycles never need anything heavier. An even cycle admits none. Above `3`
a transfer matrix handles it; at `3` nothing so cheap works, which is why `Cacti/RefTensor.lean`
through `Cacti/LargeBranch.lean` exist: a tensor capacity argument over the cycle's word model,
split into `C₄`, `C₆` and every longer cycle.

The book's [*Beyond the Paper: Cacti*](https://rkirov.github.io/enumerative-chromatic-choosability/) chapter is a
guide to all of this that assumes only the chapters before it. `Cacti/Examples.lean` pins the definition down on three
graphs — `K₄` refused, a triangle accepted, and the bowtie accepted while having two cycles, which
is what keeps the classification from being a statement about unicyclic graphs.

This is the result of a 2026 AI research collaboration on this repository, not of the paper; the
working notes are in `ai_research_notes/`. `Cacti/` imports `ListColoring/` and is never imported
by it.

## Beyond the paper: ladders

`Ladder/` settles the height-two case of Kirov–Naimi §6's **Question 1** — *is a Cartesian product
of two enumeratively chromatic-choosable graphs one?* — for paths, which is the case the
`ai_research_notes/` grid conjecture is about:

> Every `2 × (n+1)` grid is enumeratively chromatic-choosable at every list size `k ≥ 3`
> (`ListColoring.ecc_boxProd_pathG_one`), and the count it is tight against is
> `k(k-1)(k² - 3k + 3)ⁿ` (`ListColoring.colConst_boxProd_pathG_one`).

Question 1 has been open since 2016, and paths are chordal, hence qualify at every list size, so a
positive answer would give every rectangular grid outright. Only height two is settled here;
`OpenProblems.lean` records the reduction and the fact that refuting the grid statement would
refute Question 1.

The proof is a transfer matrix on rungs. Grade the colourings of the first `j` columns by the
colours `(a,b)` of the last rung; adding a column replaces that vector by
`N'(c,d) = ∑_{a ≠ c, b ≠ d} N(a,b)`. What has to be shown is that each column multiplies the total
by at least `λ_k = k² - 3k + 3`, the number of successors a rung has under uniform lists. It does
not, pointwise: one state can be short by exactly one. The invariant

> **(I)** for every state `(a,b)`: `rowMass(a) + colMass(b) ≤ total`

pays for that deficit, and the work is showing the transfer preserves it.

`k ≥ 3` is sharp and enters at exactly one place, `Ladder.inv_ones`: the first rung's all-ones
vector satisfies (I) iff `2k ≤ k² - k`. At `2` the `2 × 3` grid really does fail.

Two things make the formal proof shorter than the pen-and-paper argument it started from. The
count of successors is itself a count of *states of two shortened lists*, which turns the whole
analysis into arithmetic and replaces a 1,200,000-configuration finite check by
`Ladder.deficient_structure`. And the mass off a state's row and column is an instance of the same
`ext`-weighted sum one list size down, so the lemma that buys the factor `λ_k` also proves the
transfer preserves (I) — no separate argument, and no `k = 3` / `k ≥ 4` split. The bridge needs no
ladder graph of its own: the induced subgraph of `pathG 1 □ pathG (n+1)` on the older columns *is*
`pathG 1 □ pathG n`.

Also a 2026 AI research collaboration result, not the paper's; notes in `ai_research_notes/`.
`Ladder/` imports `ListColoring/` and is imported by nothing — in particular not by
`OpenProblems.lean`, which stays imported by nothing at all.

## Beyond the paper: height three

`Grid3/` settles the height-three case of Question 1 for paths at every list size `k ≥ 3`:

> Every `3 × (n+1)` grid is enumeratively chromatic-choosable at every list size `k ≥ 3`
> (`ListColoring.ecc_boxProd_pathG_two_of_three`; `ecc_boxProd_pathG_two_of_four` is the `k ≥ 4`
> case and `ecc_boxProd_pathG_two` the `k ≥ 5` case), and the count it is tight against is
> `Fne k n · k(k-1)² + Dp k n · k(k-1)` (`ListColoring.colConst_boxProd_pathG_two`), where
> `Fne`, `Dp` are the integer sequences `Fne (i+1) = ene·Fne i + gam·Dp i`,
> `Dp (i+1) = Fne i + del·Dp i` of `Grid3/Transfer.lean` — `12, 54, 246, 1122, 5118, …` at `k = 3`.

Height three is different in kind from height two: the uniform count is not geometric (its
transfer has two eigenvalues), so no scalar per-column invariant can be tight, and the ladder's
proof does not extend. What replaces it is an exact **telescoping identity**: the list count minus
the uniform count is an initial term plus one term per seam, "the actual seam minus the uniform
pattern transfer, applied to the uniform future counts of the remaining columns". At height three
the states have two equality patterns, and every horizon reduces to two integer inequalities per
seam — the note's `(H1)`, and a Perron-growth inequality made integral by replacing `κ - 1` with
`1/cc`, `cc = (k-2)(k²-3k+3)`, which is what the future counts allow at every horizon.

Both inequalities are linear in the state vector, and the vector at a seam is a nonnegative
combination of the successor indicators of the states one column back, so both are checked
pointwise: for one state and three consecutive columns of lists. Fibred over the middle colour,
each is a sum of per-colour terms that do not depend on the middle list at all, and a **pair
lemma** — any two distinct colours have nonnegative sum — closes it. The pair lemma rests on a
pointwise bound on each state's deficiency, exact at uniform, and on an integer inequality whose
threshold is exactly `(k-2)(k-3) ≥ k + 1`: a colour can be *bad* only when it is the unique colour
of the next middle list missing from the next top (or bottom) list, and then every other colour
carries a surplus `(k-2)·z·(x-1) - 1` that pays for it.

`k = 4` needs two columns of lookback: the one-column pointwise form is false there
(`Grid3.not_depthOK_four_one`), while `Grid3/DepthTwo.lean` reduces the theorem to two explicit
finite local predicates on four consecutive columns, and `Grid3/Four/` proves them. The pair lemma
becomes *conditional*: the pair sum is at least `1`, or at least `-1` in two explicit Bad
configurations — a punctured bottom (or top) list equal to the next `T ∩ M` (resp. `M ∩ B`), with
one irregular middle colour — and it is proved, together with a regular-colour lemma, by LP
certificates over the 31 Venn atoms of the five lists involved, generated by
`ai_research_notes/cx/eig/gen6.py` and checked by `linear_combination` (`Grid3/Four/ArithPair/`,
one module per size-and-membership pattern, with the case split on membership bits replaced by
McCormick product facts). Over a column a Bad colour costs exactly one, and the depth-two
accounting (`Grid3/Four/Depth.lean`) injects each Bad state two columns back into a state with
surplus at least one, so the seam slack stays nonnegative.

`k = 3` cannot use this route: the Perron-growth inequality is false on actual chains. `Grid3/Three/`
proves it by an entropy argument instead. A list assignment with at least one nonuniform column
carries a Markov chain on column states whose column laws are the *signature laws* of the 39
column types and whose seam kernels are certified couplings; the chain's entropy is at least
`log 12 + n·log ρ` with `ρ = (5 + √17)/2`, and at most the log of the number of list colourings,
which is the inequality. The couplings are 22,157 records, one per row-reflection orbit of the
43,736 maximal seam keys, each checked by `decide +kernel` on a packed big-`Nat` literal
(`Grid3/Three/Cert/Data/`), with a kernel-checked enumeration proving that every valid maximal
key, or its reflection, has a record (`Grid3/Three/Cert/Keys/`); an arbitrary assignment is
canonicalized onto those records column by column
(`Grid3/Three/{Column,Seam,ColourMaps,Transport}.lean`), a seam whose record is the reflected
one is built between the reflected columns and carried back (`Grid3/Three/Reflect.lean`, the
column laws being reflection-equivariant), the uniform-to-uniform seam is the Parry
kernel with entropy exactly `log ρ` (`Grid3/Three/Cert/Parry.lean`), and the all-uniform
assignment is handled by a direct injection (`Grid3/AllU.lean`). See `Grid3/Three/README.md`.

Also a 2026 AI research collaboration result. `Grid3/` imports `ListColoring/` and is imported by
nothing.

## Beyond the paper: 2-degeneracy is not enough

`TwoDegenerate/` refutes the tempting grid generalization that every 2-degenerate graph is
enumeratively chromatic-choosable at every list size `k ≥ 4`. The complete bipartite graph
`K₂,₂₆` is 2-degenerate, but an explicit four-list assignment has

```text
 9,925,029,789,650 list colorings
10,168,268,619,684 constant-list colorings.
```

The general `K₂,n` construction comes from Kaul et al., *Bounding the List Color Function
Threshold from Above* (2023). Their Theorem 7(ii) proves failure for `n ≥ 27` and leaves `n = 25,26`
open. Re-evaluating their balanced-list formula gives the `n = 26` witness above, closing that case
negatively. `TwoDegenerate/Counterexample.lean` proves a general 16-fibre counting formula, checks
the two exact counts in the kernel, and verifies an explicit 2-degeneracy ordering. An independent
integer checker and the remaining corrected research direction are in
`TwoDegenerate/README.md`.

## Standard of proof

* No `sorry`, `admit`, or `native_decide` anywhere in `ListColoring/`, `Cacti/`,
  `NonPersistence/`, `Ladder/` or `TwoDegenerate/`, checked by CI.
  The two `sorry`s in the repository are both in `OpenProblems.lean`, which is a **separate
  `lean_lib`** for exactly that reason: it imports `ListColoring` and nothing imports it, so no
  theorem can rest on an unproved statement. A `sorry` there means *nobody knows* — those are
  §6's open questions, not gaps in the formalization of the paper.
* Every headline result depends on exactly the three standard Lean axioms — `propext`,
  `Classical.choice`, `Quot.sound` — enforced by the comparator's `permitted_axioms`.
* Statements were checked by brute-force evaluation *before* being proved, which repeatedly caught
  indexing and orientation errors that would not have surfaced as type errors. See the
  "Specs verified numerically" section of `plan.md`. The sweeps that cost minutes of evaluation live in `Checks/`, a library that is not a default build target; CI builds it separately (`lake build Checks`).
* CI runs the real [leanprover/comparator](https://github.com/leanprover/comparator) against
  `comparator/Challenge.lean`, which claims **fifteen keystone theorems** — ten from the paper,
  three of the cactus classification, and two of Zhang–Dong's non-persistence theorem, which
  answers the paper's own §6 Question 2 — and the definitions needed to state them — deliberately not the whole library, so that what is certified is legible.
  That checks three things an axiom audit cannot: that the statements really are the ones claimed,
  that only the permitted axioms are used, and that every proof replays through Lean's kernel
  from a `lean4export` export. (lean-eval's second, independent `nanoda` replay is not run: with
  the k = 3 certificate the export is close to 1 GB and a second sequential replay does not fit
  CI's six-hour limit.) It is CI-only — it builds three external tools.
* Every displayed statement in the companion book is an `example` discharged against the real
  theorem, so the prose cannot drift from the proofs.

## Design decisions

The two that shaped everything else:

**Colorings are counted as a `Finset (V → ℕ)`, not via Mathlib's bundled `SimpleGraph.Coloring`.**
The bundled type has no `Fintype` instance at this revision, and it fixes a single color type for
the whole graph, which is exactly wrong when lists vary per vertex. `G.Coloring` survives only as a
bridge to `Colorable` / `chromaticNumber`.

**Kirov–Naimi does not need the chromatic polynomial.** The natural reading of the literature
suggests a dependency on deletion–contraction and Whitney's broken-cycle theorem, but the paper
needs the *number* of colorings, never the polynomial. Dropping that layer kept edge contraction —
absent from Mathlib — off the critical path. The polynomial is nevertheless built here, separately,
in `ListColoring/ChromaticPolynomial.lean` via the Whitney subset expansion, so that
`ecc_iff_listColorFunction_eq_eval` can say `P_ℓ(G,n) = P(G,n)` with a genuine polynomial on
the right. Likewise Kostochka–Sidorenko needs only a simplicial elimination ordering, so **Dirac's
theorem is not on its critical path** — though it is proved here anyway, as
`isChordal_iff_exists_cliqueTower`.

See `plan.md` for what mechanization turned up: hypotheses that proved load-bearing, hypotheses that
proved unnecessary, and the places where a naive formalization diverges from a correct informal
argument.
