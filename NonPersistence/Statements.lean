/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import NonPersistence.Main

/-!
# The headline statements

**Zhang–Dong 2026** ([arXiv:2608.19773](https://arxiv.org/abs/2608.19773)), Theorem 6, and the
question it settles.

## What is claimed

* `exists_ecc_not_ecc_succ` — for every `k ≥ 3` and every bound `N`, a graph on more than `N`
  vertices that is `k`-colorable and enumeratively chromatic-choosable at `k`, but not at `k + 1`.
  "Infinitely many graphs" in the form that avoids quantifying over isomorphism classes.
* `not_persistence` — equality between the chromatic polynomial and the list-color function does
  **not** persist from `k` to `k + 1`.

`not_persistence` is the negation of Kirov–Naimi 2016, §6, Question 2, which
`OpenProblems.lean` states as `ListColoring.OpenProblem.Question2` in the direction that paper
conjectured. `Persistence` below is a verbatim copy of that statement; it is restated here rather
than imported, so that this library never depends on one that still asserts an open question
without a proof.

In the modern vocabulary (`provenance.md` §4) this says `ν(G) ≠ τ(G)` in general.

## Provenance

The mathematics is Zhang and Dong's. Nothing in this library is a contribution of this
repository beyond the mechanization; see `provenance.md`. Two deliberate deviations from the
paper, both recorded where they occur:

* the threshold `t₀` is `(m + 2)(m + 4) · |Sbad m|` rather than their `⌈k² log((7k+1)/2)⌉` — much
  worse, but elementary, and the statement proved is the same;
* their Lemma 11 (an exact formula for `P(G_{k,t}, L)`) is not formalized, because a strict
  inequality between two coloring *sets* — `card_SbadA_lt` — replaces the computation.
-/

open Finset SimpleGraph

namespace ZhangDong

/-! ### Size -/

theorem card_TowerV (V : Type) [Fintype V] :
    ∀ n : ℕ, Fintype.card (TowerV V n) = Fintype.card V + n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      have h : Fintype.card (TowerV V (n + 1)) = Fintype.card (TowerV V n) + 1 :=
        Fintype.card_option
      rw [h, ih]
      omega

theorem card_zd (m t : ℕ) :
    Fintype.card (TowerV (Option (Option (XV m))) (4 * t)) = m + 5 + 4 * t := by
  rw [card_TowerV]
  simp only [Fintype.card_option, Fintype.card_fin]

/-! ### Theorem 6 -/

/-- **Zhang–Dong 2026, Theorem 6.** For every `k ≥ 3` there are arbitrarily large graphs `G` with
`P(G, k) = P_ℓ(G, k) > 0` and `P(G, k + 1) > P_ℓ(G, k + 1)` — hence infinitely many. -/
theorem exists_ecc_not_ecc_succ (k : ℕ) (hk : 3 ≤ k) (N : ℕ) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      N < Fintype.card V ∧ G.Colorable k ∧ G.ECCAt k ∧ ¬ G.ECCAt (k + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  refine ⟨TowerV (Option (Option (XV m))) (4 * (t₀ m + N)), inferInstance, inferInstance,
    zd m (t₀ m + N), inferInstance, ?_, colorable_zd m _, ECCAt_zd m _,
    not_ECCAt_succ m _ (by omega)⟩
  rw [card_zd]
  omega

/-! ### The question it settles -/

/-- **Kirov–Naimi 2016, §6, Question 2**, verbatim: *if a graph is `n`-colorable and
`n`-monophilic, is it necessarily `(n+1)`-monophilic?*

A copy of `ListColoring.OpenProblem.Question2`. It is restated rather than imported because
`OpenProblems.lean` still asserts Question 1 without a proof, and nothing here may rest on
that. -/
def Persistence : Prop :=
  ∀ (n : ℕ) {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj],
    G.Colorable n → G.ECCAt n → G.ECCAt (n + 1)

/-- **The answer: no.** Enumerative chromatic-choosability does not propagate from `n` to `n + 1`,
even for `n`-colorable graphs. Equivalently `ν(G) = τ(G)` fails in general.

This refutes Kirov–Naimi §6 Question 2, open since 2016. -/
theorem not_persistence : ¬ Persistence := by
  intro h
  exact not_ECCAt_succ 0 (t₀ 0) le_rfl
    (h 3 (zd 0 (t₀ 0)) (colorable_zd 0 (t₀ 0)) (ECCAt_zd 0 (t₀ 0)))

/-! ### Axiom audit -/

#print axioms exists_ecc_not_ecc_succ
#print axioms not_persistence

end ZhangDong
