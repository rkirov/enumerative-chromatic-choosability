/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Seven.Order7
import GridGen.Gauge.Seam

/-!
# The covers along the lookahead process

During a seam the keys of the old column are moved by the global moves `O` and the stars in `Del`
are unpaired: `cov k β O Del v a` is `k` for a deleted star, and otherwise the old label `β v a`
moved by the moves acting on row `v`. Appending a move is `moveKey` (`cov_snoc`), deleting a star
is `unpair` (`cov_insert`). A label is a *hole* of row `r` if no colour of row `r` is keyed with
it; the current label of a deleted star is a hole (`hole_of_del`).
-/

open Finset

set_option linter.unusedSectionVars false

namespace GridGen.Gauge

variable {m : ℕ}

/-- The keys after the moves `O`, with the stars of `Del` unpaired. -/
def cov (k : ℕ) (β : ℕ → ℕ → ℕ) (O : List GOp) (Del : Finset (Fin m × ℕ)) : Fin m → ℕ → ℕ :=
  fun v a => if (v, a) ∈ Del then k else curL O v.val (β v.val a)

/-- Every move of `O` has labels below `k`. -/
def OpsSmall (k : ℕ) (O : List GOp) : Prop := ∀ o ∈ O, o.2.1 < k ∧ o.2.2 < k

theorem small_actOn {k : ℕ} {O : List GOp} (h : OpsSmall k O) (u : ℕ) : Small k (actOn O u) := by
  intro p hp
  simp only [actOn, List.mem_map, List.mem_filter] at hp
  obtain ⟨o, ⟨ho, -⟩, rfl⟩ := hp
  exact h o ho

theorem curL_lt {k : ℕ} {O : List GOp} (h : OpsSmall k O) (u : ℕ) {z : ℕ} (hz : z < k) :
    curL O u z < k := by
  unfold curL
  rw [← comp_reverse]
  exact comp_lt (fun p hp => small_actOn h u p (List.mem_reverse.mp hp)) hz

theorem curL_ge {k : ℕ} {O : List GOp} (h : OpsSmall k O) (u : ℕ) {z : ℕ} (hz : k ≤ z) :
    curL O u z = z := by
  unfold curL
  rw [← comp_reverse]
  exact comp_of_ge (fun p hp => small_actOn h u p (List.mem_reverse.mp hp)) hz

/-- **Appending a move is `moveKey`.** -/
theorem cov_snoc {k : ℕ} (β : ℕ → ℕ → ℕ) (O : List GOp) (Del : Finset (Fin m × ℕ))
    {e x y : ℕ} (hx : x < k) (hy : y < k) :
    cov k β (O ++ [(e, x, y)]) Del = moveKey (cov k β O Del) e x y := by
  funext v a
  unfold cov moveKey
  beta_reduce
  by_cases hd : (v, a) ∈ Del
  · rw [ite_eq_left hd, ite_eq_left hd]
    split_ifs
    · exact (Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)).symm
    · rfl
  · rw [ite_eq_right hd, ite_eq_right hd, curL_snoc]

/-- **Deleting a star is `unpair`.** -/
theorem cov_insert {k : ℕ} (β : ℕ → ℕ → ℕ) (O : List GOp) (Del : Finset (Fin m × ℕ))
    (v : Fin m) (a : ℕ) : cov k β O (insert (v, a) Del) = unpair k (cov k β O Del) v a := by
  funext v' a'
  unfold cov unpair
  beta_reduce
  by_cases h : v' = v ∧ a' = a
  · obtain ⟨rfl, rfl⟩ := h
    rw [ite_eq_left (mem_insert_self _ _), ite_eq_left ⟨rfl, rfl⟩]
  · rw [ite_eq_right h]
    have : (v', a') ∈ insert (v, a) Del ↔ (v', a') ∈ Del := by
      rw [mem_insert]
      exact ⟨fun h' => h'.resolve_left fun e => h ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩,
        Or.inr⟩
    by_cases hd : (v', a') ∈ Del
    · rw [ite_eq_left (this.mpr hd), ite_eq_left hd]
    · rw [ite_eq_right (fun h' => hd (this.mp h')), ite_eq_right hd]

/-- The starting cover is the old keys. -/
theorem cov_nil {k : ℕ} (β : ℕ → ℕ → ℕ) : cov (m := m) k β [] ∅ = fun v a => β v.val a := by
  funext v a; simp [cov, curL, actOn, compA]

/-- **The keys stay injective.** -/
theorem keyInj_cov {k : ℕ} {A : Fin m → Finset ℕ} {β : ℕ → ℕ → ℕ}
    (hβ : ∀ v : Fin m, Set.InjOn (β v.val) (A v)) {O : List GOp} (Del : Finset (Fin m × ℕ)) :
    KeyInj k A (cov k β O Del) := by
  intro v a a' ha ha' e hlt
  unfold cov at e hlt
  split_ifs at e hlt with h1 h2 h2
  · omega
  · omega
  · omega
  · exact hβ v ha ha' (compA_injective _ e)

/-- **The current label of a deleted star is a hole**: no colour of its row is keyed with it. -/
theorem hole_of_del {k : ℕ} {A : Fin m → Finset ℕ} {β : ℕ → ℕ → ℕ}
    (hβ : ∀ v : Fin m, Set.InjOn (β v.val) (A v) ∧ ∀ a ∈ A v, β v.val a < k)
    {O : List GOp} (hO : OpsSmall k O) {Del : Finset (Fin m × ℕ)} {r : Fin m} {s : ℕ}
    (hs : s ∈ A r) (hdel : (r, s) ∈ Del) :
    ∀ a ∈ A r, cov k β O Del r a ≠ curL O r.val (β r.val s) := by
  intro a ha e
  unfold cov at e
  by_cases hd : (r, a) ∈ Del
  · rw [ite_eq_left hd] at e
    have := curL_lt hO r.val ((hβ r).2 s hs)
    omega
  · rw [ite_eq_right hd] at e
    have := (hβ r).1 ha hs (compA_injective _ e)
    subst this
    exact hd hdel

end GridGen.Gauge
