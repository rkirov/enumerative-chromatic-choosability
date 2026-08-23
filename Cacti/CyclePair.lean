/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Cacti.BalancedCore
import Cacti.Relabel
import Cacti.Peel

/-!
# The weighted cycle pair theorem

The single cycle input to the pair-invariant induction (`cactus_pair_bound`): on a cycle with
pair-dominant weights at every vertex, the weighted rooted profile is pair-bounded by the
uniform normalizer times the weight normalizers.

This is UM-106 (the bare pair bound, by the corrected inverse-orientation transfer expansion,
handoff §6.2–6.3) combined with UM-107's peeling (`pair_bound_of_bare`). The route:

* `exists_cyclic_index` — a graph isomorphic to `closePath m` enumerates as `Fin (m+1)` with
  cyclic adjacency, rotated to start at the root;
* `cycle_bare_pair` — for an EVEN cycle, the matrix model (`exists_matrix_model`) carries the
  root counts and the thread-split case analysis closes them (`cycle_cases_pair`); for an ODD
  cycle no model is needed, because the balanced core (UM-025, which exists at every `k ≥ 2`)
  makes every rooted count clear the uniform normalizer on its own;
* `cycle_pair_bound_index` — the weights peel off against that bare bound.
-/

namespace ListColoring

open SimpleGraph Finset

section CyclicIndex

variable {V : Type} {G : SimpleGraph V}

/-- **Cyclic indexing**: a graph isomorphic to `closePath m`, `m ≥ 2`, enumerates as
`Fin (m + 1)` with adjacency exactly cyclic successorship, and the enumeration can be rotated
to start at any prescribed vertex. -/
theorem exists_cyclic_index {m : ℕ} (hm : 2 ≤ m) (e : G ≃g closePath m) (r : V) :
    ∃ ix : Fin (m + 1) ≃ V, ix 0 = r ∧
      ∀ i j : Fin (m + 1), G.Adj (ix i) (ix j) ↔ (j = i + 1 ∨ i = j + 1) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  set iso : cycleGraph (m' + 3) ≃g G :=
    (cycleGraphIsoClosePath (m' + 2) (by omega)).trans e.symm with hiso
  have hsub : ∀ a b : Fin (m' + 3), a - b = 1 ↔ a = b + 1 := by
    intro a b
    rw [sub_eq_iff_eq_add, add_comm 1 b]
  have hadj0 : ∀ i j : Fin (m' + 3), G.Adj (iso i) (iso j) ↔ (j = i + 1 ∨ i = j + 1) := by
    intro i j
    rw [iso.map_rel_iff, cycleGraph_adj, hsub, hsub]
    exact or_comm
  set i₀ : Fin (m' + 3) := iso.toEquiv.symm r with hi₀
  refine ⟨(Equiv.addRight i₀).trans iso.toEquiv, ?_, ?_⟩
  · show iso (0 + i₀) = r
    rw [zero_add, hi₀]
    exact iso.apply_symm_apply r
  · intro i j
    show G.Adj (iso (i + i₀)) (iso (j + i₀)) ↔ _
    rw [hadj0]
    have hcancel : ∀ a b : Fin (m' + 3), (a + i₀ = b + i₀ + 1) ↔ a = b + 1 := by
      intro a b
      rw [add_right_comm b i₀ 1, add_left_inj]
    rw [hcancel, hcancel]

end CyclicIndex

section Pair

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **UM-106 on a graph**: the bare cycle pair bound. On a cyclically indexed graph with
`k`-lists, `k ≥ 4`, the rooted counts of two distinct root colours have product at least the
square of the uniform normalizer. -/
theorem cycle_bare_pair {m : ℕ} (hm : 2 ≤ m) (ix : Fin (m + 1) ≃ V)
    (hadj : ∀ i j : Fin (m + 1), G.Adj (ix i) (ix j) ↔ (j = i + 1 ∨ i = j + 1))
    {k : ℕ} (hk : 4 ≤ k) (L : ListAssignment V) (hL : IsNListAssignment L k) :
    ∀ c ∈ L (ix 0), ∀ d ∈ L (ix 0), c ≠ d →
      (rootedCol G (constList V k) (ix 0) 0) ^ 2 ≤
        rootedCol G L (ix 0) c * rootedCol G L (ix 0) d := by
  intro c hc d hd hcd
  rcases Nat.even_or_odd (m + 1) with hpar | hpar
  · -- an even cycle has at least four vertices; the thread splits close the twisted roots
    obtain ⟨Ts, P, dom, σ₀, hlen, hmem, hinj, hcount, hthread⟩ :=
      exists_matrix_model ix hadj L hL
    obtain ⟨c', rfl⟩ := enum_surj (hL (ix 0)) hmem hinj hc
    obtain ⟨d', rfl⟩ := enum_surj (hL (ix 0)) hmem hinj hd
    have hne : c' ≠ d' := fun h => hcd (by rw [h])
    have hlen' : Ts.length = m + 1 - 1 := by rw [hlen, Nat.add_sub_cancel]
    rw [hcount c', hcount d', rootedCol_constList_cycle (by omega) ix hadj]
    obtain ⟨t, ht⟩ := hpar
    exact cycle_cases_pair hk (by omega) ⟨t, ht⟩ hlen' hthread hne
  · -- odd: the balanced core hits every vertex-colour pair exactly `A` times, so every rooted
    -- count clears `A` on its own and the pair bound is immediate
    obtain ⟨S, hS, hbal⟩ := exists_balanced_core_odd_gen (by omega) (by omega) ix hadj hpar L hL
    have hge : ∀ e ∈ L (ix 0),
        rootedCol G (constList V k) (ix 0) 0 ≤ rootedCol G L (ix 0) e := by
      intro e he
      have hcard : (S.filter (fun f => f (ix 0) = e)).card ≤ rootedCol G L (ix 0) e :=
        (Finset.card_le_card fun f hf => by
          rw [Finset.mem_filter] at hf ⊢
          exact ⟨hS hf.1, hf.2⟩)
      rwa [hbal (ix 0) e he] at hcard
    rw [pow_two]
    exact Nat.mul_le_mul (hge c hc) (hge d hd)

/-- **The weighted cycle pair theorem from a cyclic index** (UM-106 + UM-107, `k ≥ 4`): the
form the cactus induction consumes, where a cycle arrives as an indexing of its vertices
rather than as an isomorphism. -/
theorem cycle_pair_bound_index {m : ℕ} (hm : 2 ≤ m) (ix : Fin (m + 1) ≃ V)
    (hadj : ∀ i j : Fin (m + 1), G.Adj (ix i) (ix j) ↔ (j = i + 1 ∨ i = j + 1))
    {k : ℕ} (hk : 4 ≤ k) (L : ListAssignment V) (hL : IsNListAssignment L k)
    (w : V → ℕ → ℕ) (W : V → ℕ)
    (hdom : ∀ v, ∀ c ∈ L v, ∀ d ∈ L v, c ≠ d → (W v) ^ 2 ≤ w v c * w v d) :
    ∀ c ∈ L (ix 0), ∀ d ∈ L (ix 0), c ≠ d →
      (rootedCol G (constList V k) (ix 0) 0 * ∏ v, W v) ^ 2 ≤
        (rootedWcol G L w (ix 0) c) * (rootedWcol G L w (ix 0) d) := by
  -- on a cycle every vertex has exactly two neighbours, which is all the peeling needs
  have hnbr : ∀ u : V, u ≠ ix 0 → ∃ n₁ n₂, ∀ y, G.Adj u y → y = n₁ ∨ y = n₂ := by
    intro u _
    refine ⟨ix (ix.symm u + 1), ix (ix.symm u - 1), fun y hy => ?_⟩
    have h := (hadj (ix.symm u) (ix.symm y)).mp (by
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact hy)
    rcases h with h | h
    · exact Or.inl (by rw [← h, Equiv.apply_symm_apply])
    · exact Or.inr (by rw [← eq_sub_of_add_eq h.symm, Equiv.apply_symm_apply])
  exact pair_bound_of_bare hk L hL hnbr w W hdom (cycle_bare_pair hm ix hadj hk L hL)

end Pair

end ListColoring
