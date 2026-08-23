/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import NonPersistence.Cone

/-!
# Iterated cones over one fixed set

Zhang–Dong's graph attaches `4t` new vertices to the *same* pair `{s₁, s₂}`. This file builds that
operation — `iterCone G K m`, the result of coning `m` new vertices onto `K`, one after another —
and computes what it does to coloring counts.

The one theorem everything else rests on is `sum_col_iterCone`: a weighted sum over the colorings
of the tower collapses to a weighted sum over the colorings of the base, with the tower
contributing exactly the product of the apexes' free-color counts. Taking the weight `Φ = 1` gives
the count itself.

* `iterCone`, `liftV`, `liftF` — the construction and the transport of a vertex / a set up the
  tower;
* `towerListF Lb A m` — the list assignment giving the base vertices their old lists and the apex
  added at step `i` the list `A i`; unlike a general assignment on `TowerV V m` this one is built
  by the same recursion as the tower, so both projections hold by `rfl`;
* `sum_col_iterCone` — the collapse;
* `colConst_iterCone`, `ECCAt.iterCone` — the constant-list specializations, through
  `SeparatedAt`.

Following the `PathV` / `Option` transparency note in `plan.md`: every step lemma is stated for an
honest `coneOn _ _` on `Option _`, and the crossing into `TowerV V (m + 1)` is done with
`exact`/`refine`, never `rw`.
-/

open Finset

namespace SimpleGraph

universe u

variable {V : Type u}

/-! ### Transporting a vertex and a set up the tower -/

/-- The image of a base vertex at height `m` of the tower. -/
def liftV : (m : ℕ) → V → TowerV V m
  | 0, v => v
  | m + 1, v => some (liftV m v)

@[simp] theorem liftV_zero (v : V) : liftV 0 v = v := rfl

@[simp] theorem liftV_succ (m : ℕ) (v : V) : liftV (m + 1) v = some (liftV m v) := rfl

theorem liftV_injective : ∀ (m : ℕ), Function.Injective (liftV (V := V) m)
  | 0 => fun _ _ h => h
  | m + 1 => fun _ _ h => liftV_injective m (Option.some_injective _ h)

variable [DecidableEq V]

/-- The image of a base set at height `m` of the tower. -/
def liftF (K : Finset V) : (m : ℕ) → Finset (TowerV V m)
  | 0 => K
  | m + 1 =>
      letI := instDecidableEqTowerV (V := V) m
      (liftF K m).image some

@[simp] theorem liftF_zero (K : Finset V) : liftF K 0 = K := rfl

@[simp] theorem liftF_succ (K : Finset V) (m : ℕ) :
    liftF K (m + 1) = (liftF K m).image some := rfl

theorem card_liftF (K : Finset V) : ∀ m : ℕ, (liftF K m).card = K.card
  | 0 => rfl
  | m + 1 =>
      Eq.trans (Finset.card_image_of_injective _ (Option.some_injective _)) (card_liftF K m)

/-- Pushing a function on the tower back to the base commutes with lifting a set. -/
theorem image_liftF (K : Finset V) : ∀ (m : ℕ) (F : TowerV V m → ℕ),
    (liftF K m).image F = K.image (F ∘ liftV m)
  | 0, _ => rfl
  | m + 1, F => Eq.trans Finset.image_image (image_liftF K m (F ∘ some))

/-! ### The tower -/

variable (G : SimpleGraph V) (K : Finset V)

/-- **`m` cones over the same set.** `iterCone G K m` adds `m` new vertices to `G`, each joined to
exactly the (lifted) set `K` and to nothing else — in particular the new vertices form an
independent set. -/
def iterCone : (m : ℕ) → SimpleGraph (TowerV V m)
  | 0 => G
  | m + 1 => coneOn (iterCone m) (liftF K m)

@[simp] theorem iterCone_zero : iterCone G K 0 = G := rfl

@[simp] theorem iterCone_succ (m : ℕ) :
    iterCone G K (m + 1) = coneOn (iterCone G K m) (liftF K m) := rfl

instance instDecidableRelIterCone [DecidableRel G.Adj] :
    (m : ℕ) → DecidableRel (iterCone G K m).Adj
  | 0 => inferInstanceAs (DecidableRel G.Adj)
  | m + 1 =>
      letI := instDecidableEqTowerV (V := V) m
      letI := instDecidableRelIterCone m
      coneOn.instDecidableRel (iterCone G K m) (liftF K m)

/-- **The list assignment on a tower.** Base vertices keep `Lb`; the apex added at step `i` gets
the list `A i`. Built by the same recursion as `iterCone`, so that restricting along `some` and
reading off the apex list are both definitional. -/
def towerListF (Lb : ListAssignment V) (A : ℕ → Finset ℕ) :
    (m : ℕ) → ListAssignment (TowerV V m)
  | 0 => Lb
  | m + 1 => fun v => v.elim (A m) (towerListF Lb A m)

omit [DecidableEq V] in
@[simp] theorem towerListF_zero (Lb : ListAssignment V) (A : ℕ → Finset ℕ) :
    towerListF Lb A 0 = Lb := rfl

omit [DecidableEq V] in
@[simp] theorem towerListF_succ_none (Lb : ListAssignment V) (A : ℕ → Finset ℕ) (m : ℕ) :
    towerListF Lb A (m + 1) none = A m := rfl

omit [DecidableEq V] in
@[simp] theorem towerListF_succ_some (Lb : ListAssignment V) (A : ℕ → Finset ℕ) (m : ℕ)
    (v : TowerV V m) : towerListF Lb A (m + 1) (some v) = towerListF Lb A m v := rfl

omit [DecidableEq V] in
theorem towerListF_succ_comp_some (Lb : ListAssignment V) (A : ℕ → Finset ℕ) (m : ℕ) :
    towerListF Lb A (m + 1) ∘ some = towerListF Lb A m := rfl

omit [DecidableEq V] in
theorem isNListAssignment_towerListF {Lb : ListAssignment V} {A : ℕ → Finset ℕ} {n : ℕ}
    (hLb : IsNListAssignment Lb n) (hA : ∀ i, (A i).card = n) :
    ∀ m : ℕ, IsNListAssignment (towerListF Lb A m) n
  | 0 => hLb
  | m + 1 => by
      rintro (_ | v)
      · exact hA m
      · exact isNListAssignment_towerListF hLb hA m v

/-- The constant list assignment on a tower is the tower assignment built from constant data. -/
theorem towerListF_constList (n : ℕ) : ∀ m : ℕ,
    towerListF (constList V n) (fun _ => range n) m = constList (TowerV V m) n
  | 0 => rfl
  | m + 1 => by
      funext v
      rcases v with _ | v
      · rfl
      · exact congrFun (towerListF_constList n m) v

/-! ### The collapse -/

section Counting

variable [Fintype V] [DecidableRel G.Adj]

/-- **The weighted fibre sum over a cone.** `SimpleGraph.col_coneOn` is the case `Ψ = 1`: the
summand may depend on the coloring of the base, since every coloring in one fibre restricts to the
same base coloring. -/
theorem sum_col_coneOn {W : Type u} [Fintype W] [DecidableEq W] {H : SimpleGraph W}
    [DecidableRel H.Adj] {J : Finset W} (M : ListAssignment (Option W)) (Ψ : (W → ℕ) → ℕ) :
    ∑ F ∈ (coneOn H J).colorings M, Ψ (F ∘ some)
      = ∑ f ∈ H.colorings (M ∘ some), (M none \ J.image f).card * Ψ f := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun F => F ∘ some)
    (fun F hF => comp_some_mem_colorings hF) (fun F => Ψ (F ∘ some))]
  refine Finset.sum_congr rfl fun f hf => ?_
  have hconst : ∀ F ∈ ((coneOn H J).colorings M).filter (fun F => F ∘ some = f),
      Ψ (F ∘ some) = Ψ f := fun F hF => by rw [(Finset.mem_filter.mp hF).2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, card_filter_comp_some hf]

/-- **The collapse.** A weighted sum over the colorings of a tower, where the weight depends only
on the restriction to the base, equals the same weight summed over the base colorings against the
product of the apexes' free-color counts.

This is the only counting fact the whole development needs: `Φ = 1` gives the coloring count, and a
`Φ` supported on the base colorings of one shape isolates that shape's contribution. -/
theorem sum_col_iterCone (Lb : ListAssignment V) (A : ℕ → Finset ℕ) :
    ∀ (m : ℕ) (Φ : (V → ℕ) → ℕ),
      ∑ F ∈ (iterCone G K m).colorings (towerListF Lb A m), Φ (F ∘ liftV m)
        = ∑ f ∈ G.colorings Lb, (∏ i ∈ range m, (A i \ K.image f).card) * Φ f
  | 0, Φ => by
      simp only [Finset.prod_range_zero, one_mul]
      exact Finset.sum_congr rfl fun _ _ => rfl
  | m + 1, Φ => by
      refine Eq.trans (sum_col_coneOn (H := iterCone G K m) (J := liftF K m)
        (towerListF Lb A (m + 1)) (fun f' => Φ (f' ∘ liftV m))) ?_
      have hstep : ∀ f' ∈ (iterCone G K m).colorings (towerListF Lb A m),
          (A m \ (liftF K m).image f').card * Φ (f' ∘ liftV m)
            = (fun f => (A m \ K.image f).card * Φ f) (f' ∘ liftV m) := by
        intro f' _
        rw [image_liftF]
      refine Eq.trans (Finset.sum_congr rfl hstep) ?_
      refine Eq.trans (sum_col_iterCone Lb A m (fun f => (A m \ K.image f).card * Φ f)) ?_
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [Finset.prod_range_succ]
      ring

/-! ### Constant lists -/

set_option maxHeartbeats 1000000 in
/-- One cone step preserves separation: the apex is not in the lifted set, and a coloring of the
cone restricts to a coloring of the base. -/
theorem separatedAt_coneOn {W : Type u} [Fintype W] [DecidableEq W] {H : SimpleGraph W}
    [DecidableRel H.Adj] {J J' : Finset W} {n : ℕ} (hsep : H.SeparatedAt J n) :
    (coneOn H J').SeparatedAt (J.image some) n := by
  intro F hF
  have hF' : F ∘ some ∈ H.colorings (constList W n) := comp_some_mem_colorings hF
  rintro a ha b hb hab
  obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp ha)
  obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hb)
  exact congrArg some (hsep (F ∘ some) hF' (Finset.mem_coe.mpr ha') (Finset.mem_coe.mpr hb') hab)

/-- Separation propagates up the tower. -/
theorem separatedAt_iterCone {n : ℕ} (hsep : G.SeparatedAt K n) (m : ℕ) :
    (iterCone G K m).SeparatedAt (liftF K m) n := by
  induction m with
  | zero => exact hsep
  | succ m ih => exact separatedAt_coneOn ih

/-- **The exact count from a constant list.** Each of the `m` apexes contributes exactly
`n - |K|`, provided colorings of the base separate `K` at `n`. -/
theorem colConst_iterCone {n : ℕ} (hsep : G.SeparatedAt K n) (m : ℕ) :
    (iterCone G K m).colConst n = (n - K.card) ^ m * G.colConst n := by
  induction m with
  | zero =>
      rw [pow_zero, one_mul]
      exact rfl
  | succ m ih =>
      refine Eq.trans
        (colConst_coneOn_of_injOn (separatedAt_iterCone G K hsep m)) ?_
      rw [card_liftF, ih, pow_succ]
      ring

/-- **Kirov–Naimi's Lemma 1 along a tower**, with separation in place of the clique hypothesis. -/
theorem ECCAt.iterCone {n : ℕ} (hG : G.ECCAt n) (hsep : G.SeparatedAt K n) (m : ℕ) :
    (SimpleGraph.iterCone G K m).ECCAt n := by
  induction m with
  | zero => exact hG
  | succ m ih => exact ECCAt.coneOn_of_injOn ih (separatedAt_iterCone G K hsep m)

end Counting

end SimpleGraph
