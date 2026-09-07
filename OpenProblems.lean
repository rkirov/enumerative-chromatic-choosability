/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ListColoring
import NonPersistence.Statements

/-!
# The questions Kirov–Naimi leave open

Section 6 of **Kirov–Naimi 2016** poses two questions. Question 1 is still open. **Question 2 was
answered — negatively — in August 2026**, by Zhang and Dong; see `not_question2` below, which is
proved, not assumed. This file states both in Lean, and asserts the still-open one with `sorry`,
so that the statements are elaborated and type-checked on every build.

## Read the `sorry`s correctly

A `sorry` in this file means **nobody knows**, not "we did not get to it". These are not gaps in
the formalization of the paper; they are the paper's own open questions, and each is stated in the
direction the paper conjectures. A refutation would be just as good an answer, so proving the
negation of one of these is not a contradiction with anything asserted here.

**Nothing in `ListColoring/` may depend on this file.** The dependency runs one way — this library
imports `ListColoring`, never the reverse — and `ListColoring/` remains free of `sorry`, `admit`
and `native_decide`, which CI checks by `grep` over that directory. That separation is the whole
reason these live in their own library rather than beside the theorems they are about.

## What is here

* `Question1` / `question1` — is the Cartesian product of two `n`-monophilic graphs `n`-monophilic,
  for `n ≥ 3`? The paper's "product" is `V(G) × V(H)` with `(g,h)` adjacent to `(g',h')` when
  `g = g'` and `h ~ h'`, or `h = h'` and `g ~ g'` — Mathlib's `SimpleGraph.boxProd`, `G □ H`.
* `Question2` / `not_question2` — does `n`-monophilic propagate from `n` to `n+1` for an
  `n`-colourable graph? In modern language this asks whether `ν(G) = τ(G)` for every graph; it was
  Question 2 of Allred–Mudrock and Question 1 of Chi et al. 2026, both of which trace it to this
  paper. **Refuted** by Zhang–Dong 2026 (arXiv:2608.19773), Theorem 6, formalized in
  `NonPersistence/`. See `provenance.md` §4.
* `grid_of_question1` / `not_question1_of_not_gridTarget` — **proved**: the rectangular-grid
  conjecture of `ai_research_notes/` is the both-factors-are-paths instance of Question 1, so
  refuting it refutes Question 1.
* `not_ecc_two_boxProd_path_two_three` — **not open**, merely unformalized: the paper's own
  negative answer to Question 1 at `n = 2`.

## Two notes on §6 as printed

The restriction to `n ≥ 3` in `Question1` is the paper's: it observes that the answer at `n = 2` is
*No*, so the unrestricted statement is false and `Question1` would be a mis-statement without the
hypothesis.

The paper supports that observation with "by Theorem 3 every `Pᵢ` is 2-monophilic". **There is no
Theorem 3** — the paper has Theorems 1 and 2 only. The intended reference is the Kostochka–Sidorenko
corollary of §2, since paths are chordal (`SimpleGraph.ecc_of_isChordal`). A dangling
cross-reference, not a mathematical error; recorded in `formalization.yaml` under `errata`.
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

/-- **Open.** Question 1 of Kirov–Naimi §6, in the direction the paper conjectures. Unproved and
unrefuted; the `sorry` records that, and is not a gap in the formalization of the paper. -/
theorem question1 : Question1 := sorry

/-! #### The rectangular-grid conjecture is an instance of Question 1

`ai_research_notes/` pursues, as its own conjecture, the statement that every rectangular grid
`P_m □ P_n` satisfies `P_ℓ = P` at every list size `k ≥ 3`. It is not a separate problem: both
factors are paths, paths are enumeratively chromatic-choosable at every list size
(`ListColoring.ecc_pathG`, itself immediate from `SimpleGraph.ecc_of_isChordal`), so Question 1
implies it outright with nothing left over.

The useful direction is the contrapositive. A counterexample to the grid statement at any `k ≥ 3`
would refute Question 1 — a question open since 2016 — so the counterexample searches in
`ai_research_notes/` are worth more than the notes credit them with. Nothing here claims the grid
statement is true; `question1` above is stated in the direction Kirov–Naimi conjecture, and after
Zhang–Dong's answer to Question 2 that direction is no longer the safe bet it looked. -/

/-- **Question 1 implies the rectangular-grid conjecture.** Both hypotheses are discharged
unconditionally: a path is chordal, hence enumeratively chromatic-choosable at every list size. -/
theorem grid_of_question1 (h : Question1) (m n k : ℕ) (hk : 3 ≤ k) :
    (pathG m □ pathG n).ECCAt k :=
  h k hk (pathG m) (pathG n) (ecc_pathG m k) (ecc_pathG n k)

/-- The grid conjecture as `ai_research_notes/` states it, in the `P_ℓ = P` form. -/
def GridTarget : Prop :=
  ∀ m n k : ℕ, 3 ≤ k →
    (pathG m □ pathG n).listColorFunction k = (pathG m □ pathG n).colConst k

theorem gridTarget_of_question1 (h : Question1) : GridTarget := fun m n k hk =>
  (ecc_iff_listColorFunction_eq k).mp (grid_of_question1 h m n k hk)

/-- **Refuting the grid conjecture would refute Question 1.** -/
theorem not_question1_of_not_gridTarget (h : ¬ GridTarget) : ¬ Question1 :=
  fun hq => h (gridTarget_of_question1 hq)

/-- **Not open — known, and merely unformalized here.** Kirov–Naimi's negative answer to Question 1
at `n = 2`: a grid can fail to be enumeratively chromatic-choosable at `2` even though both its
factors are (every path is, by `ListColoring.ecc_pathG`).

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
