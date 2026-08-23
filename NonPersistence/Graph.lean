/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import NonPersistence.Tower

/-!
# Zhang–Dong's graph

The construction of arXiv:2608.19773 §2. Writing `k = m + 3` throughout, so that `k ≥ 3` is
automatic and `Fin k` has honest numerals:

* `X = K_k`, a clique on `Fin (m + 3)`;
* `s₁`, joined to every `xⱼ` except `x₀`;
* `s₂`, joined to every `xⱼ` except `x₁` — and **not** to `s₁`;
* `4t` further vertices, each joined to both `s₁` and `s₂` and to nothing else.

`H m` is the graph before the last step. It is a clique tower — both attachment sets are subsets
of the clique `X` — so it is enumeratively chromatic-choosable at every list size. The whole
phenomenon lives in the last step: the pair `{s₁, s₂}` is not an edge, but

* at `k` colors the clique forces `f s₁ ≠ f s₂` (`separatedAt_sPair`), so the `4t` vertices behave
  as if coned onto an edge and `zd` inherits the property;
* at `k + 1` colors it does not, and the extra colorings with `f s₁ = f s₂` are what a list
  assignment can be designed to destroy.
-/

open Finset SimpleGraph

namespace ZhangDong

/-! ### The graph -/

/-- The clique's vertex type. `k = m + 3`, so `k ≥ 3` needs no hypothesis. -/
abbrev XV (m : ℕ) := Fin (m + 3)

/-- The clique vertex `s₁` misses. Written out rather than as the numeral `0`, so that no `Fin`
literal arithmetic is ever needed. -/
def x₀ (m : ℕ) : XV m := ⟨0, by omega⟩

/-- The clique vertex `s₂` misses. -/
def x₁ (m : ℕ) : XV m := ⟨1, by omega⟩

theorem x₀_ne_x₁ (m : ℕ) : x₀ m ≠ x₁ m := by
  simp [x₀, x₁, Fin.ext_iff]

/-- The neighbourhood of `s₁` in the clique: everything but `x₀`. -/
def K₁ (m : ℕ) : Finset (XV m) := Finset.univ.erase (x₀ m)

/-- The neighbourhood of `s₂`, once `s₁` has been added: everything but `x₁`, and not `s₁`. -/
def K₂ (m : ℕ) : Finset (Option (XV m)) := (Finset.univ.erase (x₁ m)).image some

/-- `H m`: the clique `K_{m+3}` with `s₁` and `s₂` attached. -/
def H (m : ℕ) : SimpleGraph (Option (Option (XV m))) :=
  coneOn (coneOn (⊤ : SimpleGraph (XV m)) (K₁ m)) (K₂ m)

instance instDecidableRelH (m : ℕ) : DecidableRel (H m).Adj := by
  unfold H; infer_instance

/-- `s₁`, the vertex added first. -/
def s₁ (m : ℕ) : Option (Option (XV m)) := some none

/-- `s₂`, the vertex added second. -/
def s₂ (m : ℕ) : Option (Option (XV m)) := none

/-- The pair the last `4t` vertices are coned onto. It is **not** an edge of `H m`. -/
def sPair (m : ℕ) : Finset (Option (Option (XV m))) := {s₁ m, s₂ m}

/-- A clique vertex, seen inside `H m`. -/
def xv (m : ℕ) (i : XV m) : Option (Option (XV m)) := some (some i)

theorem s₁_ne_s₂ (m : ℕ) : s₁ m ≠ s₂ m := by simp [s₁, s₂]

theorem card_sPair (m : ℕ) : (sPair m).card = 2 := by
  rw [sPair, Finset.card_insert_of_notMem (by simp [s₁, s₂]), Finset.card_singleton]

theorem card_K₁ (m : ℕ) : (K₁ m).card = m + 2 := by
  rw [K₁, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  omega

theorem card_K₂ (m : ℕ) : (K₂ m).card = m + 2 := by
  rw [K₂, Finset.card_image_of_injective _ (Option.some_injective _),
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  omega

/-- **Zhang–Dong's graph `G_{k,t}`**, `k = m + 3`: `H m` with `4t` vertices coned onto the
non-adjacent pair `{s₁, s₂}`. -/
def zd (m t : ℕ) : SimpleGraph (TowerV (Option (Option (XV m))) (4 * t)) :=
  iterCone (H m) (sPair m) (4 * t)

instance instDecidableRelZd (m t : ℕ) : DecidableRel (zd m t).Adj := by
  unfold zd; infer_instance

/-! ### Adjacency -/

@[simp] theorem H_adj_xv (m : ℕ) (i j : XV m) : (H m).Adj (xv m i) (xv m j) ↔ i ≠ j := by
  simp [H, xv, coneOn_adj_some_some, top_adj]

@[simp] theorem H_adj_s₁_xv (m : ℕ) (i : XV m) : (H m).Adj (s₁ m) (xv m i) ↔ i ≠ x₀ m := by
  simp [H, s₁, xv, K₁]

@[simp] theorem H_adj_s₂_xv (m : ℕ) (i : XV m) : (H m).Adj (s₂ m) (xv m i) ↔ i ≠ x₁ m := by
  simp [H, s₂, xv, K₂]

@[simp] theorem H_not_adj_s₁_s₂ (m : ℕ) : ¬ (H m).Adj (s₁ m) (s₂ m) := by
  simp [H, s₁, s₂, K₂]

/-! ### `H m` is a clique tower -/

theorem isClique_K₁ (m : ℕ) : (⊤ : SimpleGraph (XV m)).IsClique (K₁ m : Set (XV m)) :=
  fun _ _ _ _ h => h

theorem isClique_K₂ (m : ℕ) :
    (coneOn (⊤ : SimpleGraph (XV m)) (K₁ m)).IsClique (K₂ m : Set (Option (XV m))) := by
  intro a ha b hb hab
  obtain ⟨a', -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp ha)
  obtain ⟨b', -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hb)
  exact (coneOn_adj_some_some _ _ _ _).mpr fun h => hab (congrArg some h)

/-- `H m` is enumeratively chromatic-choosable at every list size: it is a clique tower, so
Kirov–Naimi's Lemma 1 applies twice over the complete graph. -/
theorem ECCAt_H (m n : ℕ) : (H m).ECCAt n :=
  ((ecc_top (XV m) n).coneOn (isClique_K₁ m)).coneOn (isClique_K₂ m)

end ZhangDong
