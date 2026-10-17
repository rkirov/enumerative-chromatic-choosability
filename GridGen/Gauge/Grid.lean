/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Main

/-!
# From row paths to the project's paths

The gauge telescope is run on `rowG m`, the path on `Fin m`. This file transports it to the
project's paths `pathG r` (on `PathV r`, with `r + 1` vertices). The isomorphism
`pathG r ≃g rowG (r + 1)` sends the last-attached vertex `none` to the last index;
`ecc_boxProd_pathG_of_nine` (`Nine/Main.lean`) uses it.
-/

open SimpleGraph ListColoring
open scoped SimpleGraph

namespace GridGen.Gauge

/-- Attaching a pendant vertex to the last index of a row path extends the isomorphism. -/
def extendIso {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {r : ℕ} (e : G ≃g rowG (r + 1)) (v₀ : V)
    (h₀ : e v₀ = Fin.last r) : G.addPendant v₀ ≃g rowG (r + 2) where
  toFun x := match x with
    | none => Fin.last (r + 1)
    | some y => (e y).castSucc
  invFun i := if h : i.val = r + 1 then none else some (e.symm ⟨i.val, by omega⟩)
  left_inv x := by
    match x with
    | none => simp
    | some y =>
        have h : (e y).val ≠ r + 1 := by have := (e y).isLt; omega
        simp only [Fin.val_castSucc, dite_eq_right h, Option.some.injEq]
        rw [show (⟨(e y).val, _⟩ : Fin (r + 1)) = e y from Fin.ext rfl]
        exact e.symm_apply_apply y
  right_inv i := by
    by_cases h : i.val = r + 1
    · simp only [dite_eq_left h]; exact Fin.ext h.symm
    · simp only [dite_eq_right h, Equiv.apply_symm_apply]
      rw [RelIso.apply_symm_apply]
      exact Fin.ext rfl
  map_rel_iff' := by
    intro x y
    have hinj : ∀ a b : V, e a = e b → a = b := fun a b h => e.injective h
    match x, y with
    | none, none =>
        show (rowG (r + 2)).Adj (Fin.last (r + 1)) (Fin.last (r + 1)) ↔ False
        exact ⟨fun h => (rowG (r + 2)).irrefl h, False.elim⟩
    | none, some b =>
        simp only [Equiv.coe_fn_mk, rowG_adj, Fin.val_last, Fin.val_castSucc,
          SimpleGraph.addPendant_adj_none_some]
        constructor
        · intro h
          apply hinj; rw [h₀]
          have := (e b).isLt
          exact Fin.ext (by simp; omega)
        · rintro rfl; rw [h₀]; simp
    | some a, none =>
        simp only [Equiv.coe_fn_mk, rowG_adj, Fin.val_last, Fin.val_castSucc]
        show _ ↔ a = v₀
        constructor
        · intro h
          apply hinj; rw [h₀]
          have := (e a).isLt
          exact Fin.ext (by simp; omega)
        · rintro rfl; rw [h₀]; simp
    | some a, some b =>
        simp only [Equiv.coe_fn_mk, SimpleGraph.addPendant_adj_some_some]
        rw [← e.map_rel_iff]
        simp only [rowG_adj, Fin.val_castSucc]

/-- The isomorphisms `pathG r ≃g rowG (r + 1)`, sending the end to the last index. -/
def pathIsoAux : (r : ℕ) → {e : pathG r ≃g rowG (r + 1) // e (pathEnd r) = Fin.last r}
  | 0 => ⟨{ toFun := fun _ => 0
            invFun := fun _ => ()
            left_inv := fun _ => rfl
            right_inv := fun i => (Fin.fin_one_eq_zero i).symm
            map_rel_iff' := by
              intro x y
              simp only [Equiv.coe_fn_mk, rowG_adj]
              constructor
              · intro h; simp at h
              · intro h; exact absurd h (show ¬ (pathG 0).Adj x y from id) }, rfl⟩
  | r + 1 => ⟨extendIso (pathIsoAux r).1 (pathEnd r) (pathIsoAux r).2, rfl⟩

/-- The isomorphism `pathG r ≃g rowG (r + 1)`. -/
def pathIso (r : ℕ) : pathG r ≃g rowG (r + 1) := (pathIsoAux r).1

/-- A graph isomorphism of the first factor of a box product. -/
def boxProdIsoLeft {α α' β : Type*} {G : SimpleGraph α} {G' : SimpleGraph α'} (H : SimpleGraph β)
    (e : G ≃g G') : G □ H ≃g G' □ H where
  toEquiv := Equiv.prodCongr e.toEquiv (Equiv.refl β)
  map_rel_iff' := by
    intro x y
    simp only [Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_apply, id_eq, boxProd_adj]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inl ⟨e.map_rel_iff.mp h1, h2⟩
      · exact Or.inr ⟨h1, e.injective h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inl ⟨e.map_rel_iff.mpr h1, h2⟩
      · exact Or.inr ⟨h1, by show e.toEquiv x.1 = e.toEquiv y.1; rw [h2]⟩

end GridGen.Gauge
