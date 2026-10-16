/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Box

/-!
# The Kempe wall lemma

A *lower-part move* applies a label transposition `(x y)` to the seam keys of every row below
`w`. It changes the slab count by at most the *bad* solutions (`card_le_move_add_bad`).

Write `T` for the union of the `{x, y}`-coloured components of the future that contain a *seed*.
A seed is a first future cell `(2, v)` with `v > w` whose seam key and colour both lie in
`{x, y}`. Swapping `x ↔ y` on `T` turns a solution for the old keys into a solution for the
moved ones. The only failure is that some component of `T` also reaches a first future cell
`(2, v₂)`, `v₂ ≤ w`, whose seam key is in `{x, y}`: that is the bad event. The swap preserves
the `{x, y}` cells and the seeds, so applying it twice gives back the solution. Hence the map is
injective. This is Kempe's argument, applied to a DP cover.
-/

open Finset
open scoped Classical

set_option linter.unusedSectionVars false

namespace GridGen.Gauge

variable {c m k : ℕ} {P A : Fin m → Finset ℕ}

/-- The lower-part move: transpose `x, y` in the keys of the rows below `w`. -/
def moveKey (M : Fin m → ℕ → ℕ) (w x y : ℕ) : Fin m → ℕ → ℕ :=
  fun v a => if w < v.val then Equiv.swap x y (M v a) else M v a

section Swap

variable (hc : 1 ≤ c) (M : Fin m → ℕ → ℕ) (w x y : ℕ)

/-- A future cell carrying `x` or `y`. -/
def XY (f : Cell c m → ℕ) (u : Cell c m) : Prop := 2 ≤ u.1.val ∧ (f u = x ∨ f u = y)

/-- The graph of `{x, y}`-coloured future cells. -/
def kG (f : Cell c m → ℕ) : SimpleGraph (Cell c m) where
  Adj u u' := slabAdj u u' ∧ XY x y f u ∧ XY x y f u'
  symm := ⟨fun _ _ h => ⟨slabAdj_symm h.1, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => slabAdj_irrefl h.1⟩

/-- A seed: a first future cell below `w` whose key and colour are in `{x, y}`. -/
def Seed (f : Cell c m → ℕ) (u : Cell c m) : Prop :=
  ∃ v : Fin m, w < v.val ∧ u = (fut0 hc, v) ∧ (M v (f (1, v)) = x ∨ M v (f (1, v)) = y) ∧
    XY x y f u

/-- The swapped region: everything reachable from a seed. -/
def InT (f : Cell c m → ℕ) (u : Cell c m) : Prop :=
  ∃ s, Seed hc M w x y f s ∧ (kG x y f).Reachable s u

/-- The Kempe swap. -/
noncomputable def kswap (f : Cell c m → ℕ) : Cell c m → ℕ :=
  fun u => if InT hc M w x y f u then Equiv.swap x y (f u) else f u

/-- The bad event: a seed's component reaches a first future cell above `w` with key in
`{x, y}`. -/
def Bad (f : Cell c m → ℕ) : Prop :=
  ∃ s, Seed hc M w x y f s ∧ ∃ v₂ : Fin m, v₂.val ≤ w ∧
    (M v₂ (f (1, v₂)) = x ∨ M v₂ (f (1, v₂)) = y) ∧ (kG x y f).Reachable s (fut0 hc, v₂)

variable {hc M w x y}

theorem swap_mem_xy {z : ℕ} : (Equiv.swap x y z = x ∨ Equiv.swap x y z = y) ↔ (z = x ∨ z = y) := by
  constructor
  · intro h
    rcases h with h | h
    · have := congrArg (Equiv.swap x y) h
      rw [Equiv.swap_apply_self, Equiv.swap_apply_left] at this
      exact Or.inr this
    · have := congrArg (Equiv.swap x y) h
      rw [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
      exact Or.inl this
  · rintro (rfl | rfl)
    · right; exact Equiv.swap_apply_left _ _
    · left; exact Equiv.swap_apply_right _ _

theorem swap_of_not_xy {z : ℕ} (h : ¬ (z = x ∨ z = y)) : Equiv.swap x y z = z :=
  Equiv.swap_apply_of_ne_of_ne (fun e => h (Or.inl e)) (fun e => h (Or.inr e))

/-- Reachable cells are `{x, y}`-coloured future cells. -/
theorem xy_of_reachable {f : Cell c m → ℕ} {s u : Cell c m} (hs : XY x y f s)
    (h : (kG x y f).Reachable s u) : XY x y f u := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact hs
  | tail _ hab _ => exact hab.2.2

theorem xy_of_inT {f : Cell c m → ℕ} {u : Cell c m} (h : InT hc M w x y f u) : XY x y f u := by
  obtain ⟨s, hs, hr⟩ := h
  obtain ⟨_, _, _, _, hxy⟩ := hs
  exact xy_of_reachable hxy hr

theorem fut_of_inT {f : Cell c m → ℕ} {u : Cell c m} (h : InT hc M w x y f u) : 2 ≤ u.1.val :=
  (xy_of_inT h).1

theorem kswap_of_lt {f : Cell c m → ℕ} {u : Cell c m} (h : u.1.val < 2) :
    kswap hc M w x y f u = f u := by
  unfold kswap; rw [if_neg (fun h' => by have := fut_of_inT h'; omega)]

/-- The swap preserves the `{x, y}` cells. -/
theorem xy_kswap {f : Cell c m → ℕ} {u : Cell c m} :
    XY x y (kswap hc M w x y f) u ↔ XY x y f u := by
  unfold XY kswap
  split_ifs
  · rw [swap_mem_xy]
  · rfl

theorem kG_kswap (f : Cell c m → ℕ) : kG x y (kswap hc M w x y f) = kG x y f := by
  ext u u'
  simp only [kG, xy_kswap]

/-- The swap preserves the seeds of the moved keys. -/
theorem seed_kswap {f : Cell c m → ℕ} {u : Cell c m} :
    Seed hc (moveKey M w x y) w x y (kswap hc M w x y f) u ↔ Seed hc M w x y f u := by
  unfold Seed
  refine exists_congr fun v => ?_
  constructor
  · rintro ⟨hw, hu, hk, hxy⟩
    refine ⟨hw, hu, ?_, xy_kswap.mp hxy⟩
    rw [moveKey, if_pos hw, kswap_of_lt (show (1 : Fin (c + 2)).val < 2 by
      rw [Fin.val_one]; omega)] at hk
    exact swap_mem_xy.mp hk
  · rintro ⟨hw, hu, hk, hxy⟩
    refine ⟨hw, hu, ?_, xy_kswap.mpr hxy⟩
    rw [moveKey, if_pos hw, kswap_of_lt (show (1 : Fin (c + 2)).val < 2 by
      rw [Fin.val_one]; omega)]
    exact swap_mem_xy.mpr hk

theorem inT_kswap {f : Cell c m → ℕ} {u : Cell c m} :
    InT hc (moveKey M w x y) w x y (kswap hc M w x y f) u ↔ InT hc M w x y f u := by
  unfold InT
  simp only [seed_kswap, kG_kswap]

/-- **The swap is an involution** (back with the moved keys). -/
theorem kswap_kswap (f : Cell c m → ℕ) :
    kswap hc (moveKey M w x y) w x y (kswap hc M w x y f) = f := by
  funext u
  have e : kswap hc (moveKey M w x y) w x y (kswap hc M w x y f) u =
      if InT hc (moveKey M w x y) w x y (kswap hc M w x y f) u
      then Equiv.swap x y (kswap hc M w x y f u) else kswap hc M w x y f u := rfl
  rw [e, inT_kswap]
  unfold kswap
  split_ifs <;> first | rfl | exact Equiv.swap_apply_self _ _ _

end Swap

section Valid

variable {hc : 1 ≤ c} {M : Fin m → ℕ → ℕ} {w x y : ℕ}

theorem inT_of_adj {f : Cell c m → ℕ} {u u' : Cell c m} (hu : InT hc M w x y f u)
    (h : (kG x y f).Adj u u') : InT hc M w x y f u' := by
  obtain ⟨s, hs, hr⟩ := hu
  exact ⟨s, hs, hr.trans h.reachable⟩

/-- On an edge of the future, the swap keeps distinct colours distinct. -/
theorem kswap_ne {f : Cell c m → ℕ} {u u' : Cell c m} (hu2 : 2 ≤ u.1.val) (hu2' : 2 ≤ u'.1.val)
    (hadj : slabAdj u u') (hne : f u ≠ f u') :
    kswap hc M w x y f u ≠ kswap hc M w x y f u' := by
  unfold kswap
  by_cases h : InT hc M w x y f u <;> by_cases h' : InT hc M w x y f u'
  · rw [if_pos h, if_pos h']; exact fun e => hne ((Equiv.swap x y).injective e)
  · rw [if_pos h, if_neg h']
    have hxy := (xy_of_inT h).2
    have hxy' : ¬ (f u' = x ∨ f u' = y) := fun hm =>
      h' (inT_of_adj h ⟨hadj, xy_of_inT h, hu2', hm⟩)
    intro e
    exact hxy' (e ▸ swap_mem_xy.mpr hxy)
  · rw [if_neg h, if_pos h']
    have hxy := (xy_of_inT h').2
    have hxy' : ¬ (f u = x ∨ f u = y) := fun hm =>
      h (inT_of_adj h' ⟨slabAdj_symm hadj, xy_of_inT h', hu2, hm⟩)
    intro e
    exact hxy' (e.symm ▸ swap_mem_xy.mpr hxy)
  · rw [if_neg h, if_neg h']; exact hne

theorem kswap_lt {f : Cell c m → ℕ} {u : Cell c m} (hx : x < k) (hy : y < k)
    (hf : f u < k) : kswap hc M w x y f u < k := by
  unfold kswap
  split_ifs with h
  · rcases swap_mem_xy.mpr (xy_of_inT h).2 with e | e <;> rw [e] <;> assumption
  · exact hf

theorem colOf_kswap_zero (f : Cell c m → ℕ) : colOf (kswap hc M w x y f) 0 = colOf f 0 := by
  funext v; exact kswap_of_lt (show (0 : Fin (c + 2)).val < 2 by simp)

theorem colOf_kswap_one (f : Cell c m → ℕ) : colOf (kswap hc M w x y f) 1 = colOf f 1 := by
  funext v; exact kswap_of_lt (show (1 : Fin (c + 2)).val < 2 by rw [Fin.val_one]; omega)

/-- **The swap is valid for the moved keys**, outside the bad event. -/
theorem valid_kswap (hx : x < k) (hy : y < k) {f : Cell c m → ℕ}
    (hf : (slab c m k P A M).Valid f) (hb : ¬ Bad hc M w x y f) :
    (slab c m k P A (moveKey M w x y)).Valid (kswap hc M w x y f) := by
  rw [valid_iff] at hf ⊢
  obtain ⟨h0, h1, h01, hψ⟩ := hf
  rw [colOf_kswap_zero, colOf_kswap_one]
  refine ⟨h0, h1, h01, ?_, ?_, ?_⟩
  · intro t
    have ht := (mem_states (rowG m)).mp (hψ.1 t)
    rw [mem_states]
    refine ⟨fun v => ?_, fun u v huv => ?_⟩
    · have := ht.1 v; simp only [unif, mem_range] at this ⊢
      exact kswap_lt hx hy this
    · exact kswap_ne (show 2 ≤ t.val + 2 by omega) (show 2 ≤ t.val + 2 by omega)
        (Or.inl ⟨rfl, huv⟩) (ht.2 huv)
  · intro t ht v
    have hv := hψ.2.1 t ht v
    simp only [keyed, moveKey, futOf] at hv ⊢
    -- the first future cell of row `v`
    set z : Cell c m := (fut0 hc, v) with hz
    have hz' : (⟨t.val + 2, by omega⟩, v) = z := by
      rw [hz]; exact Prod.ext (Fin.ext (by simp [fut0, ht])) rfl
    rw [hz'] at hv ⊢
    by_cases hw : w < v.val
    · rw [if_pos hw]
      unfold kswap
      split_ifs with hT
      · exact fun e => hv ((Equiv.swap x y).injective e)
      · by_cases hm : M v (colOf f 1 v) = x ∨ M v (colOf f 1 v) = y
        · have hzxy : ¬ (f z = x ∨ f z = y) := fun hm' =>
            hT ⟨z, ⟨v, hw, rfl, hm, ⟨by rw [hz]; rfl, hm'⟩⟩, SimpleGraph.Reachable.refl _⟩
          intro e; exact hzxy (e ▸ swap_mem_xy.mpr hm)
        · rw [swap_of_not_xy hm]; exact hv
    · rw [if_neg hw]
      unfold kswap
      split_ifs with hT
      · by_cases hm : M v (colOf f 1 v) = x ∨ M v (colOf f 1 v) = y
        · exfalso
          obtain ⟨s, hs, hr⟩ := hT
          exact hb ⟨s, hs, v, by omega, hm, hr⟩
        · intro e
          exact hm (e ▸ swap_mem_xy.mpr (xy_of_inT hT).2)
      · exact hv
  · intro t t' htt v
    exact kswap_ne (show 2 ≤ t.val + 2 by omega) (show 2 ≤ t'.val + 2 by omega)
      (Or.inr ⟨rfl, Or.inl (show t.val + 2 + 1 = t'.val + 2 by omega)⟩) (hψ.2.2 t t' htt v)

/-- **The Kempe wall lemma.** -/
theorem card_le_move_add_bad (hx : x < k) (hy : y < k) :
    (slab c m k P A M).Ω.card ≤ (slab c m k P A (moveKey M w x y)).Ω.card +
      ((slab c m k P A M).Ω.filter (Bad hc M w x y)).card := by
  rw [← card_filter_add_card_filter_not (s := (slab c m k P A M).Ω) (Bad hc M w x y), add_comm]
  refine Nat.add_le_add_right ?_ _
  refine card_le_card_of_injOn (kswap hc M w x y) (fun f hf => ?_) (fun f _ f' _ he => ?_)
  · rw [mem_coe, mem_filter, CSP.mem_Ω] at hf
    rw [mem_coe, CSP.mem_Ω]
    exact valid_kswap hx hy hf.1 hf.2
  · have := congrArg (kswap hc (moveKey M w x y) w x y) he
    rwa [kswap_kswap, kswap_kswap] at this

end Valid

end GridGen.Gauge
