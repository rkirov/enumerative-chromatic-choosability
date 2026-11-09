/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ListColoring
import NonPersistence.Statements
import ProductCounterexample.Main

/-!
# The questions Kirov–Naimi left open

Section 6 of **Kirov–Naimi 2016** poses two questions. **Both are now answered, and both
negatively.** Question 1 is **refuted** (recorded here 2026-11-09) by the classical
clique-times-star construction of Borowiecki–Jendrol'–Král'–Miškuf 2006 and Kaul–Mudrock
(arXiv:1811.02420); see `not_question1`. Question 2 was **refuted in August 2026** by Zhang and
Dong; see `not_question2`. Both negations are proved, not assumed. This file states the two
questions in Lean, in the direction the paper conjectured, so that the statements are elaborated
and type-checked on every build.

## Read the `sorry` correctly

Neither question is asserted with `sorry` any more. The one `sorry` left in this file,
`not_ecc_two_boxProd_path_two_three`, is **not** an open problem: it is a known fact from the
paper that is merely unformalized here.

**Nothing in `ListColoring/` may depend on this file.** The dependency runs one way — this library
imports `ListColoring`, never the reverse — and `ListColoring/` remains free of `sorry`, `admit`
and `native_decide`, which CI checks by `grep` over that directory. That separation is the whole
reason these live in their own library rather than beside the theorems they are about.

## What is here

* `Question1` / `not_question1` — is the Cartesian product of two `n`-monophilic graphs
  `n`-monophilic, for `n ≥ 3`? The paper's "product" is `V(G) × V(H)` with `(g,h)` adjacent to
  `(g',h')` when `g = g'` and `h ~ h'`, or `h = h'` and `g ~ g'` — Mathlib's
  `SimpleGraph.boxProd`, `G □ H`.
  **Refuted**: `K₃` times the star with one leaf per permutation of three colours is not
  `3`-monophilic although both factors are chordal. Formalized in `ProductCounterexample/`; the
  construction is Borowiecki–Jendrol'–Král'–Miškuf's and Kaul–Mudrock's, not ours.
* `Question2` / `not_question2` — does `n`-monophilic propagate from `n` to `n+1` for an
  `n`-colourable graph? In modern language this asks whether `ν(G) = τ(G)` for every graph; it was
  Question 2 of Allred–Mudrock and Question 1 of Chi et al. 2026, both of which trace it to this
  paper. **Refuted** by Zhang–Dong 2026 (arXiv:2608.19773), Theorem 6, formalized in
  `NonPersistence/`. See `provenance.md` §4.
* `grid_of_question1` / `not_question1_of_not_gridTarget` — **proved, but now pointless**: the
  rectangular-grid conjecture of `ai_research_notes/` is the both-factors-are-paths instance of
  Question 1. Since Question 1 is refuted, these implications have a false hypothesis or an
  already-proved conclusion; `GridTarget` stands as a conjecture of its own.
* `not_ecc_two_boxProd_path_two_three` — **not open**, merely unformalized: the paper's own
  negative answer to Question 1 at `n = 2`.

## Two notes on §6 as printed

The restriction to `n ≥ 3` in `Question1` is the paper's: it observes that the answer at `n = 2` is
*No*, so the unrestricted statement is false and `Question1` would be a mis-statement without the
hypothesis.

The paper supports that observation with "by Theorem 3 every `Pᵢ` is 2-monophilic". **There is no
Theorem 3** — the paper has Theorems 1 and 2 only. The intended reference is the Kostochka–Sidorenko
corollary of §2, since paths are chordal (`SimpleGraph.ecc_of_isChordal`). A dangling
cross-reference, not a mathematical error; recorded in `formalization.yaml` under `fidelity`.
-/

open SimpleGraph

namespace ListColoring
namespace OpenProblem

/-! ### Question 1 -/

/-- **Kirov–Naimi 2016, §6, Question 1.** *Is the product of two `n`-monophilic graphs
`n`-monophilic?*

The paper motivates it as a counting analogue of the List Colouring Conjecture: the line graph of
`K_{n,n}` is `Kₙ □ Kₙ`, so a positive answer would be to Galvin's theorem what enumerative
chromatic-choosability is to choosability.

`n ≥ 3` is the paper's own restriction — see the module docstring and
`not_ecc_two_boxProd_path_two_three`. -/
def Question1 : Prop :=
  ∀ (n : ℕ), 3 ≤ n →
    ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
      (G : SimpleGraph α) [DecidableRel G.Adj] (H : SimpleGraph β) [DecidableRel H.Adj],
      G.ECCAt n → H.ECCAt n → (G □ H).ECCAt n

/-- **Refuted**, and so no longer a `sorry`. For `K₃` and the star whose six leaves are the
permutations of three colours — both chordal, hence enumeratively chromatic-choosable at every
list size — the Cartesian product is `3`-colourable but has a `3`-list assignment with no
colouring at all, so it is not enumeratively chromatic-choosable at `3`. The same construction
works at every `n ≥ 2` (`ProductCounterexample.not_ecc_top_boxProd_star`).

The construction is the standard proof that a clique times a large star is not
chromatic-choosable: Borowiecki, Jendrol', Král' and Miškuf, *List coloring of Cartesian products
of graphs*, Discrete Math. **306** (2006), and Kaul and Mudrock, *List coloring a Cartesian product
with a complete bipartite factor* ([arXiv:1811.02420](https://arxiv.org/abs/1811.02420)). The mathematics is theirs; what is
recorded here (2026-11-09) is only the observation that it answers Kirov–Naimi's Question 1.

`ProductCounterexample.ProductQuestion` is a verbatim copy of `Question1`, restated rather than
imported so that that library never depends on this file. -/
theorem not_question1 : ¬ Question1 := ProductCounterexample.not_productQuestion

/-! #### The rectangular-grid conjecture was an instance of Question 1

`ai_research_notes/` pursues, as its own conjecture, the statement that every rectangular grid
`P_m □ P_n` satisfies `P_ℓ = P` at every list size `k ≥ 3`. Both factors are paths, and paths are
enumeratively chromatic-choosable at every list size (`ListColoring.ecc_pathG`, itself immediate
from `SimpleGraph.ecc_of_isChordal`), so Question 1 would have implied it outright.

**Question 1 is refuted** (`not_question1`, 2026-11-09, by the clique-times-star construction), so
that derivation is gone: the grid conjecture is a standalone conjecture, no longer an instance of
an open question. The refutation says nothing about grids — its witness has a factor with a
vertex of degree `n!`, and neither factor is a path. The implications below remain true and are
kept for the record, but `grid_of_question1` and `gridTarget_of_question1` now have a false
hypothesis, and the conclusion of `not_question1_of_not_gridTarget` is known unconditionally.
Nothing here claims the grid statement is true. -/

/-- **Question 1 would imply the rectangular-grid conjecture.** Both hypotheses are discharged
unconditionally: a path is chordal, hence enumeratively chromatic-choosable at every list size.

Vacuous since 2026-11-09: the hypothesis `Question1` is false (`not_question1`). -/
theorem grid_of_question1 (h : Question1) (m n k : ℕ) (hk : 3 ≤ k) :
    (pathG m □ pathG n).ECCAt k :=
  h k hk (pathG m) (pathG n) (ecc_pathG m k) (ecc_pathG n k)

/-- The grid conjecture as `ai_research_notes/` states it, in the `P_ℓ = P` form. A standalone
conjecture: Question 1, of which it was an instance, is refuted (`not_question1`). -/
def GridTarget : Prop :=
  ∀ m n k : ℕ, 3 ≤ k →
    (pathG m □ pathG n).listColorFunction k = (pathG m □ pathG n).colConst k

/-- Vacuous since 2026-11-09: the hypothesis `Question1` is false (`not_question1`). -/
theorem gridTarget_of_question1 (h : Question1) : GridTarget := fun m n k hk =>
  (ecc_iff_listColorFunction_eq k).mp (grid_of_question1 h m n k hk)

/-- **Refuting the grid conjecture would refute Question 1.** True, but no longer useful: the
conclusion holds unconditionally (`not_question1`, 2026-11-09, by the clique-times-star
construction), so a grid counterexample would now be news about grids only. -/
theorem not_question1_of_not_gridTarget (h : ¬ GridTarget) : ¬ Question1 :=
  fun hq => h (gridTarget_of_question1 hq)

/-- **Not open — known, and merely unformalized here.** Kirov–Naimi's own negative answer to
Question 1 at `n = 2`: a grid can fail to be enumeratively chromatic-choosable at `2` even though
both its factors are (every path is, by `ListColoring.ecc_pathG`).

Mind the indexing. `pathG k` is the path of *length* `k`, on `k + 1` vertices, so the statement
below is about the **`3 × 4` grid on 12 vertices**. The paper's own witness is the smaller `2 × 3`
grid, which in this convention is `pathG 1 □ pathG 2`; that is not `2`-ECC either, and neither
version is formalized here.

The paper derives it from Theorem 2 — all cycles of the grid are even, and it contains two cycles
whose union is not `K₂,₃` — so `ListColoring.ecc_two_iff` is the route to a proof. -/
theorem not_ecc_two_boxProd_path_two_three : ¬ (pathG 2 □ pathG 3).ECCAt 2 := sorry

/-! ### Question 2 -/

/-- **Kirov–Naimi 2016, §6, Question 2.** *If a graph is `n`-colourable and `n`-monophilic, is it
necessarily `(n+1)`-monophilic?*

The paper poses it to decide whether the two natural definitions of a "monophilic number" agree:
the least `n` for which `G` is `n`-colourable and `n`-monophilic, versus the least `n` such that `G`
is `n'`-monophilic for every `n' ≥ n`. In the modern vocabulary those are `ν(G)` and `τ(G)`, and
this asks whether `ν = τ` always.

The `Colorable n` hypothesis is not decoration: below the chromatic number every graph is
enumeratively chromatic-choosable for free (`SimpleGraph.ecc_of_not_colorable`), so without it the
statement would have to survive a vacuous hypothesis at every `n < χ(G)`. -/
def Question2 : Prop :=
  ∀ (n : ℕ) {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj],
    G.Colorable n → G.ECCAt n → G.ECCAt (n + 1)

/-- **Refuted**, and so no longer a `sorry`: Zhang and Dong,
*Non-persistence of equality between chromatic polynomials and list-color functions*
([arXiv:2608.19773](https://arxiv.org/abs/2608.19773), 20 August 2026), Theorem 6, produce for
every `k ≥ 3` infinitely many `k`-colourable graphs that are enumeratively chromatic-choosable at
`k` and not at `k + 1`.

Their construction and this proof are `NonPersistence/`; `ZhangDong.Persistence` there is a
verbatim copy of `Question2`, restated rather than imported so that the new library never depends
on this file. Equivalently: `ν(G) = τ(G)` is **false** in general. -/
theorem not_question2 : ¬ Question2 := ZhangDong.not_persistence

/-- What Kirov–Naimi's Theorem 2 settles is `ν(G) = 2`, the *pointwise* property at `n = 2`.
Allred–Mudrock's Theorem 10 obtains the same classification for `τ(G) = 2`, so the `χ = 2` case of
Question 2 is true; `not_question2` shows the general case is not. This is why
`ListColoring.ecc_two_iff` is a statement about `ECCAt _ 2` and not about `SimpleGraph.ECC`. -/
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) :
    G.ECCAt 2 ↔ CoreIsVertex G ∨ CoreIsCycle G ∨ CoreIsK23 G ∨ HasOddCycle G :=
  ecc_two_iff G hG

end OpenProblem
end ListColoring
