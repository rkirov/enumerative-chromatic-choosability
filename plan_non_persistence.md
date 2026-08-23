# Formalizing Zhang–Dong, *Non-persistence of equality between chromatic polynomials and list-color functions*

**Paper.** Meiqiao Zhang, Fengming Dong, [arXiv:2608.19773](https://arxiv.org/abs/2608.19773),
submitted 20 August 2026. math.CO; MSC 05C15, 05C30, 05C31.

> **Status, 2026-08-23: done.** Theorem 6 is formalized in `NonPersistence/`, sorry-free, on
> exactly `propext`, `Classical.choice`, `Quot.sound`. `ListColoring.OpenProblem.question2` is
> gone; `not_question2` is a theorem. What follows is the original plan, kept for the record,
> with §2 rewritten to say what was actually built — it was much less than estimated, for two
> reasons recorded there.

**Why this repository cares.** The paper's Question 5 — *does `P(G,k) = P_ℓ(G,k) > 0` imply
`P(G,k+1) = P_ℓ(G,k+1)`?* — is Kirov–Naimi §6 Question 2 under a change of vocabulary, and the
paper says so: it "remains open since 2016". Their Theorem 6 answers it **negatively**. So this is
not only a formalization target; it settles a statement this repository currently carries as open.

---

## 0. Four places the repository was wrong — all now corrected

These were false as of 2026-08-20. All four have been fixed, and `question2` is no longer a
`sorry` but a refuted statement with a proof.

| file | what it says | what is now true |
|---|---|---|
| `OpenProblems.lean` module docstring | "Section 6 … poses two questions. Both are still open." | Question 1 is open; Question 2 is refuted |
| `OpenProblems.lean`, `question2` | `theorem question2 : Question2 := sorry`, "Unproved and unrefuted" | the proposition is **false**; the `sorry` now asserts a known falsehood |
| `provenance.md` §4 | "Whether `ν(G) = τ(G)` for every graph … is **open**" | refuted: Theorem 6 gives `ν(G) ≤ k < τ(G)` |
| `formalization.yaml`, `question-2` | `status: stated_open` | `status: refuted_elsewhere`, credit Zhang–Dong |

`README.md` §"Beyond the paper" does not appear to claim Question 2 is open, but should be re-read.

**The `question2` declaration is the urgent one.** Nothing imports `OpenProblems`, so no theorem
rests on it and soundness is unaffected — but the file's own contract is that a `sorry` there means
*nobody knows*, and that is no longer the case. The declaration should become

```lean
/-- **Refuted**, by Zhang–Dong 2026 (arXiv:2608.19773), Theorem 6. … -/
theorem not_question2 : ¬ Question2 := sorry
```

It now reads exactly that, with the `sorry` discharged: `not_question2 := ZhangDong.not_persistence`.

**A replacement open problem is available.** The paper closes with its Question 18 — *characterize
the graphs for which equality holds at every `k`* — which is exactly `SimpleGraph.ECC` and belongs
in `OpenProblems.lean` in Question 2's place.

---

## 1. What the paper proves

Notation matches the repo: `P(G,k) = G.colConst k`, `P_ℓ(G,k) = G.listColorFunction k`,
`P(G,k) = P_ℓ(G,k)` ⟺ `G.ECCAt k` (via `SimpleGraph.ecc_iff_listColorFunction_eq_eval`), and
`τ(G)` is the threshold whose existence is already `SimpleGraph.exists_ecc_forall_ge`.

**Theorem 6.** For each `k ≥ 3` there are infinitely many `G` with `P(G,k) = P_ℓ(G,k) > 0` and
`P(G,k+1) > P_ℓ(G,k+1)`.

**Theorem 7.** For each `k ≥ 3` and each `G` with `P(G,k) = P_ℓ(G,k) > 0`, an infinite family
`𝒢ⁿᵖ(G)` of such counterexamples can be manufactured from `G`.

### The construction `G_{k,t}`

`V = X_k ∪ S ∪ Y_t` with `X_k = {x_i : i ∈ [k]}`, `S = {s_1, s_2}`,
`Y_t = {y_{i,j} : i ∈ [4], j ∈ [t]}`, and edges

* `x_i x_j` for `i ≠ j` — so `X_k` is a `K_k`;
* `s_i x_j` for `i ≠ j` — so `s_i` misses exactly `x_i` and has `k−1` neighbours in the clique;
* `y_{i,j} s_r` for all `r ∈ [2]` — so `S ∪ Y_t` induces `K_{2,4t}`.

`s_1 ≁ s_2`, the `y`'s are pairwise non-adjacent, and no `y` meets `X_k`.

Worth noting for anyone who expects the repo's existing tools to apply: **`G_{k,t}` is not
chordal** — `s_1 y_{1,1} s_2 y_{2,1}` is an induced 4-cycle — so
`SimpleGraph.ecc_of_isChordal` cannot reach it, as it must not, since the graph fails ECC at `k+1`.

### The two sides

*At `k` (Lemma 8):* order `x_1 … x_k, s_1, s_2, y_{1,1} …`. Back-degrees are `i−1` for `x_i`,
`k−1` for each `s_i`, and `2` for each `y`. Greedily each vertex has at least `k − d` colours
available, and for the constant list exactly that many, giving

```
P(G_{k,t}, k) = P_ℓ(G_{k,t}, k) = k! · (k−2)^{4t} > 0.
```

The `s_i` factor is `1` and the `y` factor is `k−2` because the clique forces `θ(s_1) ≠ θ(s_2)`.

*At `k+1` (Lemmas 9–11, Prop 12):* a lower bound `P(G_{k,t},k+1) ≥ (k+1)! · k^{4t}` (colour
`s_1, s_2` alike first), against an **exact** count of `P(G_{k,t}, L)` for one specific bad
`(k+1)`-list assignment. With `C = {c_1,…,c_{k−1}}`, `B_1 = {b_{1,1},b_{1,2}}`,
`B_2 = {b_{2,1},b_{2,2}}` and `D_1..D_4` the four transversals `{b_{1,·}, b_{2,·}}`:

```
L(x_i) = C ∪ B_1,   L(s_i) = C ∪ B_i,   L(y_{i,j}) = C ∪ D_i.
```

Every list has size `(k−1) + 2 = k+1`. Since the `y`'s are independent and see only `S`, the
extension count factors as a product over `Y_t`, split by where `θ(s_1), θ(s_2)` land relative to
`C` (Lemma 10, four cases). Summing gives Lemma 11's closed form, and Proposition 12 compares it
against `(k+1)!k^{4t}`, reducing to `F_k(t) < 1` for an explicit `F_k` built from `r = 1 − 1/k` and
`s = 1 − 1/k²`.

> **Verification debt, resolved by not incurring it.** The exact shape of Lemma 11 and the
> threshold `t_0 = ⌈k² log((7k+1)/2)⌉` came from an automated extraction of the paper's HTML, not
> from reading the PDF line by line, and were never checked. They did not need to be: neither is
> used. Lemma 10's four-case structure *was* re-derived from scratch before being formalized, and
> agrees with the extraction. What the Lean depends on is only what was re-derived.

---

## 2. What was actually built

The 4–6 week estimate below was wrong by an order of magnitude, because two simplifications found
while reading the construction removed most of the work.

**The greedy bound (old M2) was never needed.** `ListColoring/Cone.lean` already proves
Kirov–Naimi's Lemma 1 for a cone over a *clique*, and the clique hypothesis enters in exactly one
place — `colConst_coneOn`, via `injOn_of_isClique`. Weakening "K is a clique" to "every colouring
from the constant list is injective on K" (`SimpleGraph.SeparatedAt`) is a twenty-line
generalization, and it is *precisely* the Zhang–Dong phenomenon: `{s₁, s₂}` is not an edge, but at
`k` colours the surrounding `K_k` separates it anyway, and at `k+1` it does not. Lemma 8 then
falls straight out of the existing tower machinery.

**Lemma 11 was never needed either.** The paper computes `P(G_{k,t}, L)` exactly and compares it
to `(k+1)!k^{4t}`. But the error term carries a factor `((k²-1)/k²)^t`, which vanishes, so *any*
positive gap between the two counts of agreeing base colourings suffices. That gap is one explicit
colouring — `fwit`, the clique coloured by index with both `sᵢ` on colour `m+3`, which the full
palette allows and `s₂`'s list forbids. `card_SbadA_lt` replaces the whole computation.

Together these also collapsed the analytic step: the comparison reduces to
`N · Q^t < (Q+1)^t` with `Q = k²-1`, which is Bernoulli, provable by induction in `ℕ`. No
logarithms, no exponentials, no reals.

| file | content |
|---|---|
| `Cone.lean` | `SeparatedAt`, and Lemma 1 with the clique hypothesis weakened |
| `Tower.lean` | `iterCone`, `towerListF`, and `sum_col_iterCone` — the collapse every count uses |
| `Graph.lean` | `H m`, `zd m t`, adjacency, `H m` is a clique tower |
| `AtK.lean` | **Lemma 8**: `separatedAt_sPair`, `ECCAt_zd`, `colorable_zd` |
| `BadList.lean` | the assignment (2.3), every list of size `k+1` |
| `Marginal.lean` | **Lemma 10**: `prod_four_le`, the nine-case marginal bound |
| `Arith.lean` | Bernoulli in `ℕ`; four-periodic products |
| `Compare.lean` | the two regimes, and `card_SbadA_lt` — the one colouring of slack |
| `Main.lean` | **Proposition 12**: `col_lt_colConst`, `not_ECCAt_succ` |
| `Statements.lean` | **Theorem 6**: `exists_ecc_not_ecc_succ`; `not_persistence` |

### Two deviations from the paper, both deliberate

* **The threshold.** `t₀ m = (m+2)(m+4)·|Sbad m|`, against the paper's `⌈k² log((7k+1)/2)⌉`. Very
  much worse, entirely elementary, and the theorem proved is identical — the statement quantifies
  over *some* threshold, not a sharp one.
* **Lemma 11 is not formalized**, for the reason above. Lemmas 8, 9, 10 and Proposition 12 are.

### Not done

**Theorem 7** (the transfer construction) is not formalized, and on reflection should not be
without a decision from the maintainer: it rests on Lemma 16, which Zhang–Dong *quote* from
Kaul–Mudrock rather than prove. Under this repository's attribution discipline that means either
formalizing a second paper or carrying an explicit hypothesis. It adds nothing to the answer —
Theorem 6 alone settles Question 2.

## 3. Where it lives

`NonPersistence/`, in the shape `Cacti/` already established: it imports `ListColoring`, and the
only thing that imports it is `OpenProblems.lean`, which uses it to discharge Question 2. It is in
`defaultTargets`.

The import runs that way round, rather than `NonPersistence` importing `OpenProblems`, so that the
new library never depends on a file containing `sorry`. `ZhangDong.Persistence` is therefore a
verbatim copy of `ListColoring.OpenProblem.Question2`; the two are definitionally equal, which is
what lets `not_question2 := ZhangDong.not_persistence` typecheck.

**Still worth doing:** the paper's Question 18 — characterize the graphs with equality at every
`k`, i.e. `SimpleGraph.ECC` — is a genuine open problem and belongs in `OpenProblems.lean` in
Question 2's place. It has not been added.

## 5. Attribution

This is Zhang and Dong's theorem. Under the discipline `provenance.md` sets out, the library is
credited to them throughout, `formalization.yaml` gets a `results` block naming them, and nothing
here is presented as an advance of this repository — the contribution is mechanization. The one
genuinely new artifact would be M2's greedy bound, which is classical mathematics but a reusable
gap, in the same category as the Mathlib `TODO` already discharged in `ListColoring/`.
