/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ListColoring

/-!
# Cone attachments over a set that colorings separate

`ListColoring/Cone.lean` proves Kirov–Naimi's Lemma 1: coning a new vertex onto a **clique** `K`
preserves enumerative chromatic-choosability, because a proper coloring is injective on a clique
and so the apex sees exactly `|K|` forbidden colors.

The clique hypothesis is stronger than the proof needs. What `colConst_coneOn` actually uses is
that *every proper coloring from the constant list is injective on `K`* — and a set can have that
property without being a clique, if the rest of the graph forces its vertices apart. That is
exactly the situation in Zhang–Dong's construction: the pair `{s₁, s₂}` is **not** an edge, but at
`k` colors the surrounding `K_k` forces `f s₁ ≠ f s₂` anyway. At `k + 1` colors it does not, and
that gap is the whole counterexample.

* `colConst_coneOn_of_injOn` — the exact count, from separation rather than adjacency;
* `ECCAt.coneOn_of_injOn` — Lemma 1 with the same weakening.

`SimpleGraph.mul_col_le_col_coneOn`, the lower bound for arbitrary lists, already needs no
hypothesis at all, so it is reused unchanged.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable (K : Finset V)

/-- **`K` is separated at `n`**: every proper coloring of `G` from the constant list of size `n`
gives distinct colors to distinct vertices of `K`.

A clique is separated at every `n` (`separatedAt_of_isClique`), but the converse fails, and the
failure is the point: separation can hold at one list size and fail at the next. -/
def SeparatedAt (n : ℕ) : Prop :=
  ∀ f ∈ G.colorings (constList V n), Set.InjOn f (K : Set V)

variable {G K}

theorem separatedAt_of_isClique (hK : G.IsClique (K : Set V)) (n : ℕ) : G.SeparatedAt K n :=
  fun _ hf => injOn_of_isClique hK hf

/-- **Constant lists give equality**, from separation rather than from `K` being a clique. Coning
off a set that colorings separate at `n` multiplies the number of colorings from the constant list
of size `n` by exactly `n - |K|`.

This is `SimpleGraph.colConst_coneOn` with `IsClique` weakened to `SeparatedAt`; the proof is the
same, since the clique hypothesis was only ever used to get injectivity on `K`. -/
theorem colConst_coneOn_of_injOn {n : ℕ} (hsep : G.SeparatedAt K n) :
    (coneOn G K).colConst n = (n - K.card) * G.colConst n := by
  rw [colConst, col_coneOn]
  have key : ∀ f ∈ G.colorings (constList (Option V) n ∘ some),
      (constList (Option V) n none \ K.image f).card = n - K.card := by
    intro f hf
    have hf' : f ∈ G.colorings (constList V n) := hf
    have hsub : K.image f ⊆ range n := by
      intro c hc
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hc
      exact mem_list_of_mem_colorings hf' v
    rw [show constList (Option V) n none = range n from rfl,
      Finset.card_sdiff_of_subset hsub, Finset.card_range,
      Finset.card_image_of_injOn (hsep f hf')]
  rw [Finset.sum_congr rfl key, Finset.sum_const, smul_eq_mul, mul_comm]
  rfl

/-- **Kirov–Naimi's Lemma 1, with the clique hypothesis weakened to separation.** If `G` is
enumeratively chromatic-choosable at `n` and every proper coloring of `G` from `range n` is
injective on `K`, then coning a new vertex onto `K` preserves the property at `n`.

Unlike the clique form, this is genuinely a statement about one `n` at a time. -/
theorem ECCAt.coneOn_of_injOn {n : ℕ} (hG : G.ECCAt n) (hsep : G.SeparatedAt K n) :
    (SimpleGraph.coneOn G K).ECCAt n := by
  intro M hM
  rw [colConst_coneOn_of_injOn hsep]
  exact le_trans (Nat.mul_le_mul le_rfl (hG (M ∘ some) fun v => hM (some v)))
    (mul_col_le_col_coneOn hM)

end SimpleGraph
