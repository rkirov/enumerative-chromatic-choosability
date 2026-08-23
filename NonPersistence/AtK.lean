/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import NonPersistence.Graph

/-!
# Equality at `k` (Zhang–Dong, Lemma 8)

`zd m t` is enumeratively chromatic-choosable at `k = m + 3`, and `k`-colorable, so
`P(G, k) = P_ℓ(G, k) > 0`.

The whole content is `separatedAt_sPair`: with exactly `k` colors available, a proper coloring of
`H m` **cannot** give `s₁` and `s₂` the same color. The clique `X` uses up all `k` colors; `s₁`
sees all of it but `x₀` and so is forced onto `f x₀`, and `s₂` likewise onto `f x₁`. A common
color would be a `(k + 1)`-st color, and there is none.

With that, the pair `{s₁, s₂}` behaves exactly like an edge as far as `k`-colorings are concerned,
so the `4t` vertices coned onto it are simplicial *in effect*, and `ECCAt.iterCone` applies.
-/

open Finset SimpleGraph

namespace ZhangDong

/-- **The forcing.** At `k = m + 3` colors, `s₁` and `s₂` get different colors in every proper
coloring of `H m` from the full palette — even though they are not adjacent. -/
theorem f_s₁_ne_f_s₂ {m : ℕ} {f : Option (Option (XV m)) → ℕ}
    (hf : f ∈ (H m).colorings (constList (Option (Option (XV m))) (m + 3))) :
    f (s₁ m) ≠ f (s₂ m) := by
  intro hcon
  have hmem : ∀ v, f v ∈ Finset.range (m + 3) := fun v => mem_list_of_mem_colorings hf v
  have hproper : (H m).IsProperColoring f := isProperColoring_of_mem_colorings hf
  have hs₁ : ∀ i : XV m, i ≠ x₀ m → f (s₁ m) ≠ f (xv m i) := fun i hi =>
    hproper ((H_adj_s₁_xv m i).mpr hi)
  have hs₂ : ∀ i : XV m, i ≠ x₁ m → f (s₁ m) ≠ f (xv m i) := fun i hi => by
    rw [hcon]; exact hproper ((H_adj_s₂_xv m i).mpr hi)
  -- every clique color differs from the common color, and the clique colors are distinct
  have hall : ∀ i : XV m, f (s₁ m) ≠ f (xv m i) := by
    intro i
    by_cases hi : i = x₀ m
    · exact hs₂ i (hi ▸ x₀_ne_x₁ m)
    · exact hs₁ i hi
  -- this function reads off the `k` clique colors together with the common color of `s₁`, `s₂`
  have hginj : Function.Injective
      (fun o : Option (XV m) => o.elim (f (s₁ m)) (fun i => f (xv m i))) := by
    rintro (_ | a) (_ | b) hab
    · rfl
    · exact absurd hab (hall b)
    · exact absurd hab.symm (hall a)
    · by_cases hab' : a = b
      · rw [hab']
      · exact absurd hab (hproper ((H_adj_xv m a b).mpr hab'))
  -- `g` is an injection of `m + 4` vertices into `m + 3` colors
  have hcard : (Finset.univ : Finset (Option (XV m))).card ≤ (Finset.range (m + 3)).card := by
    refine Finset.card_le_card_of_injOn
      (fun o : Option (XV m) => o.elim (f (s₁ m)) (fun i => f (xv m i)))
      (fun o _ => ?_) (Set.injOn_of_injective hginj)
    rcases o with _ | i
    · exact hmem _
    · exact hmem _
  rw [Finset.card_univ, Fintype.card_option, Fintype.card_fin, Finset.card_range] at hcard
  omega

/-- The pair `{s₁, s₂}` is separated at `k = m + 3`: `SimpleGraph.SeparatedAt` is exactly what
`f_s₁_ne_f_s₂` says, packaged for `ECCAt.iterCone`. -/
theorem separatedAt_sPair (m : ℕ) : (H m).SeparatedAt (sPair m) (m + 3) := by
  intro f hf a ha b hb hab
  have hne := f_s₁_ne_f_s₂ hf
  simp only [sPair, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · rfl
  · exact absurd hab hne
  · exact absurd hab hne.symm
  · rfl

/-- **Zhang–Dong, Lemma 8** (the equality half): `P_ℓ(G_{k,t}, k) = P(G_{k,t}, k)`. -/
theorem ECCAt_zd (m t : ℕ) : (zd m t).ECCAt (m + 3) :=
  ECCAt.iterCone (H m) (sPair m) (ECCAt_H m (m + 3)) (separatedAt_sPair m) (4 * t)

/-! ### Positivity -/

theorem colorable_top_fin (N : ℕ) : (⊤ : SimpleGraph (Fin N)).Colorable N :=
  ⟨SimpleGraph.Coloring.mk id fun {_ _} h => h⟩

theorem colConst_H (m n : ℕ) :
    (H m).colConst n = (n - (m + 2)) * ((n - (m + 2)) * (⊤ : SimpleGraph (XV m)).colConst n) := by
  have h1 : (H m).colConst n
      = (n - (K₂ m).card) * (coneOn (⊤ : SimpleGraph (XV m)) (K₁ m)).colConst n :=
    colConst_coneOn (isClique_K₂ m) n
  rw [h1, colConst_coneOn (isClique_K₁ m), card_K₁, card_K₂]

/-- **Zhang–Dong, Lemma 8** (the positivity half): `P(G_{k,t}, k) > 0`. -/
theorem colorable_zd (m t : ℕ) : (zd m t).Colorable (m + 3) := by
  rw [← colConst_pos_iff_colorable]
  have hzd : (zd m t).colConst (m + 3)
      = (m + 3 - (sPair m).card) ^ (4 * t) * (H m).colConst (m + 3) :=
    colConst_iterCone (H m) (sPair m) (separatedAt_sPair m) (4 * t)
  rw [hzd, card_sPair]
  have htop : 0 < (⊤ : SimpleGraph (XV m)).colConst (m + 3) :=
    colConst_pos_iff_colorable.mpr (colorable_top_fin (m + 3))
  have hH : 0 < (H m).colConst (m + 3) := by
    rw [colConst_H]
    have : m + 3 - (m + 2) = 1 := by omega
    rw [this, one_mul, one_mul]
    exact htop
  exact Nat.mul_pos (pow_pos (by omega) (4 * t)) hH

end ZhangDong
