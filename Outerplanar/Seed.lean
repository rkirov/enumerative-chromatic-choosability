/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.Graph

/-!
# The graph induction, started from a seed

`EarBuiltFrom G m₀ S₀ S` says that the induced subgraph on `S` is built from the one on `S₀` by
pendant vertices and ears of at least `m₀` vertices on edges, exactly as in `EarBuilt` (which is
the case `S₀ = ∅`).

`ZGBound G k S` is the weighted lower bound that the induction of `Outerplanar/Graph.lean`
carries. `ZG_ge_from` propagates it from the seed, by the same three steps, and
`ecc_of_earBuiltFrom` concludes that the graph is `k`-ECC when the seed satisfies the bound.
-/

set_option linter.unusedSectionVars false

namespace Outerplanar

open Finset

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The induced subgraph on `S` is built from the one on `S₀` by pendant vertices and by ears
of at least `m₀` vertices on edges. -/
inductive EarBuiltFrom (m₀ : ℕ) (S₀ : Finset V) : Finset V → Prop
  | seed : EarBuiltFrom m₀ S₀ S₀
  | pendant (S : Finset V) (x : V) (hx : x ∉ S) (hS : EarBuiltFrom m₀ S₀ S)
      (hdeg : (S.filter (G.Adj x)).card ≤ 1) : EarBuiltFrom m₀ S₀ (insert x S)
  | ear (S : Finset V) (m : ℕ) (hm : 1 ≤ m) (hm₀ : m₀ ≤ m) (u v : V) (hu : u ∈ S) (hv : v ∈ S)
      (huv : G.Adj u v) (x : Fin m → V) (hinj : Function.Injective x) (hxS : ∀ j, x j ∉ S)
      (hS : EarBuiltFrom m₀ S₀ S)
      (hold : ∀ j, ∀ y ∈ S, G.Adj (x j) y ↔ (j.val = 0 ∧ y = u) ∨ (j.val + 1 = m ∧ y = v))
      (hnew : ∀ j j', G.Adj (x j) (x j') ↔ j.val + 1 = j'.val ∨ j'.val + 1 = j.val) :
      EarBuiltFrom m₀ S₀ (S ∪ univ.image x)

/-- The weighted lower bound on the vertex set `S`: for lists of `k` colours, positive vertex
weights and pair profiles satisfying the invariant, the weighted partition function is at least
the constant-list count times the geometric means of the weights and the constants of the
profiles. -/
def ZGBound (k : ℕ) (S : Finset V) : Prop :=
  ∀ (L : V → Finset ℕ) (ω : V → ℕ → ℝ) (Ω : V → V → ℕ → ℕ → ℝ) (A : V → V → ℝ),
    (∀ x ∈ S, (L x).card = k) → (∀ x ∈ S, ∀ c ∈ L x, 0 < ω x c) →
    (∀ x y c d, 0 ≤ Ω x y c d) → (∀ x y, 0 < A x y) →
    (∀ x ∈ S, ∀ y ∈ S, G.Adj x y → HasPot (L x) (L y) (Ω x y) (A x y)) →
    ZG G S (fun _ => range k) (fun _ _ => 1) neProfile
        * (∏ x ∈ S, gmean (L x) (ω x)) * ∏ p ∈ adjPairs G S, A p.1 p.2
      ≤ ZG G S L ω Ω

/-- `EarBuilt` is `EarBuiltFrom` the empty set. -/
theorem earBuiltFrom_empty_iff {m₀ : ℕ} {S : Finset V} :
    EarBuiltFrom G m₀ ∅ S ↔ EarBuilt G m₀ S := by
  constructor
  · intro h
    induction h with
    | seed => exact EarBuilt.empty
    | pendant S x hx _ hdeg ih => exact EarBuilt.pendant S x hx ih hdeg
    | ear S m hm hm₀ u v hu hv huv x hinj hxS _ hold hnew ih =>
      exact EarBuilt.ear S m hm hm₀ u v hu hv huv x hinj hxS ih hold hnew
  · intro h
    induction h with
    | empty => exact EarBuiltFrom.seed
    | pendant S x hx _ hdeg ih => exact EarBuiltFrom.pendant S x hx ih hdeg
    | ear S m hm hm₀ u v hu hv huv x hinj hxS _ hold hnew ih =>
      exact EarBuiltFrom.ear S m hm hm₀ u v hu hv huv x hinj hxS ih hold hnew

/-- The weighted lower bound, propagated from a seed along pendant vertices and ears. -/
theorem ZG_ge_from {k m₀ : ℕ} (hk : 3 ≤ k) (hface : ∀ m, 1 ≤ m → m₀ ≤ m → FaceClosed k m)
    {S₀ S : Finset V} (hseed : ZGBound G k S₀) (hS : EarBuiltFrom G m₀ S₀ S) :
    ZGBound G k S := by
  induction hS with
  | seed => exact hseed
  | pendant S x hx hS hdeg ih =>
    intro L ω Ω A hcard hω hΩ hA hpot
    have hsub : ∀ z ∈ S, z ∈ insert x S := fun z hz => mem_insert_of_mem hz
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hdeg with h0 | h1
    · have hiso : ∀ z ∈ S, ¬ G.Adj x z := by
        intro z hz hadj
        have : z ∈ S.filter (G.Adj x) := mem_filter.mpr ⟨hz, hadj⟩
        rw [Finset.card_eq_zero.mp h0] at this
        exact absurd this (Finset.notMem_empty z)
      exact step_isolated hk hx hiso L ω Ω A (hcard x (mem_insert_self x S))
        (hω x (mem_insert_self x S)) hA
        (ih L ω Ω A (fun z hz => hcard z (hsub z hz)) (fun z hz => hω z (hsub z hz)) hΩ hA
          fun a ha b hb => hpot a (hsub a ha) b (hsub b hb))
    · obtain ⟨y, hy⟩ := Finset.card_eq_one.mp h1
      have hyS : y ∈ S ∧ G.Adj x y := by
        have : y ∈ S.filter (G.Adj x) := by rw [hy]; exact mem_singleton_self y
        exact mem_filter.mp this
      have huniq : ∀ z ∈ S, G.Adj x z → z = y := by
        intro z hz hadj
        have : z ∈ S.filter (G.Adj x) := mem_filter.mpr ⟨hz, hadj⟩
        rw [hy] at this
        exact mem_singleton.mp this
      exact step_pendant hk hx hyS.1 hyS.2 huniq L ω Ω A hcard hω hΩ hA hpot
        fun ω' hω' => ih L ω' Ω A (fun z hz => hcard z (hsub z hz)) hω' hΩ hA
          fun a ha b hb => hpot a (hsub a ha) b (hsub b hb)
  | ear S m hm hm₀ u v hu hv huv x hinj hxS hS hold hnew ih =>
    intro L ω Ω A hcard hω hΩ hA hpot
    have he : IsEar G S u v x := ⟨hm, hu, hv, huv, hinj, hxS, hold, hnew⟩
    exact step_ear hk (hface m hm hm₀) he L ω Ω A hcard hω hΩ hA hpot
      fun Ω' A' hΩ' hA' hpot' => ih L ω Ω' A'
        (fun z hz => hcard z (mem_union_left _ hz)) (fun z hz => hω z (mem_union_left _ hz))
        hΩ' hA' hpot'

/-- A graph built from a seed by pendant vertices and ears on edges is `k`-ECC, given closure
under faces and the weighted lower bound on the seed. -/
theorem ecc_of_earBuiltFrom {k m₀ : ℕ} (hk : 3 ≤ k)
    (hface : ∀ m, 1 ≤ m → m₀ ≤ m → FaceClosed k m) {S₀ : Finset V} (hseed : ZGBound G k S₀)
    (h : EarBuiltFrom G m₀ S₀ univ) : G.ECCAt k := by
  intro L hL
  have key := ZG_ge_from G hk hface hseed h L (fun _ _ => 1) neProfile (fun _ _ => 1)
    (fun x _ => hL x) (fun _ _ _ _ => one_pos)
    (fun _ _ c d => by unfold neProfile; split_ifs <;> norm_num)
    (fun _ _ => one_pos) (fun x _ y _ _ => hasPot_ne (L x) (L y))
  have hg : ∀ x ∈ (univ : Finset V), gmean (L x) (fun _ => (1 : ℝ)) = 1 := fun x _ =>
    gmean_eq_one (fun _ _ => one_pos) (by simp)
  rw [Finset.prod_congr rfl hg, Finset.prod_const_one, Finset.prod_const_one, mul_one, mul_one,
    ZG_univ_eq_col, ZG_univ_eq_col] at key
  have key' : (G.colConst k : ℝ) ≤ (G.col L : ℝ) := key
  exact_mod_cast key'

end Outerplanar
