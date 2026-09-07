import k3_entropy.ModelAssembly
import Grid3.Main
import ListColoring.Iso

/-!
# From the indexed entropy model to the repository's grid graph

The path vertices in `ListColoring.Path` are nested `Option`s; the entropy model uses `Fin`.
`pathEquiv` preserves their left-to-right order and `gridIso` identifies the two adjacency
relations. `col_eq_properC` is the count bridge. `colConst_three_eq_a` identifies the entropy
baseline recurrence with the actual uniform-colouring count.
-/

namespace Grid3.Three.Model

open SimpleGraph ListColoring Finset
open scoped SimpleGraph

def pathEquiv : (n : ℕ) → PathV n ≃ Fin (n + 1)
  | 0 =>
    { toFun := fun _ => ⟨0, by omega⟩
      invFun := fun _ => ()
      left_inv := fun v => by cases v; rfl
      right_inv := fun v => by apply Fin.ext; have := v.isLt; omega }
  | n + 1 => (Equiv.optionCongr (pathEquiv n)).trans
      (finSuccEquiv' (Fin.last (n + 1))).symm

@[simp] theorem pathEquiv_none (n : ℕ) :
    pathEquiv (n + 1) none = Fin.last (n + 1) := by
  change (finSuccEquiv' (Fin.last (n + 1))).symm none = _
  exact finSuccEquiv'_symm_none _

@[simp] theorem pathEquiv_some (n : ℕ) (v : PathV n) :
    pathEquiv (n + 1) (some v) = (pathEquiv n v).castSucc := by
  change (finSuccEquiv' (Fin.last (n + 1))).symm (some (pathEquiv n v)) = _
  rw [finSuccEquiv'_symm_some, Fin.succAbove_last]

@[simp] theorem pathEquiv_end (n : ℕ) : pathEquiv n (pathEnd n) = Fin.last n := by
  cases n with
  | zero => apply Fin.ext; have := (pathEquiv 0 (pathEnd 0)).isLt; simp only [Fin.val_last]; omega
  | succ n => exact pathEquiv_none n

theorem pathEquiv_adj : ∀ (n : ℕ) (v w : PathV n),
    (pathG n).Adj v w ↔
      (pathEquiv n v).val + 1 = (pathEquiv n w).val ∨
      (pathEquiv n w).val + 1 = (pathEquiv n v).val := by
  intro n
  induction n with
  | zero =>
    intro v w
    simp [pathG]
  | succ n ih =>
    intro v w
    cases v with
    | none =>
      cases w with
      | none => simp [pathG, SimpleGraph.addPendant, SimpleGraph.addPendantAdj]
      | some w =>
        change w = pathEnd n ↔ _
        simp only [pathEquiv_none, pathEquiv_some, Fin.val_last, Fin.val_castSucc]
        have hw := (pathEquiv n w).isLt
        have he : w = pathEnd n ↔ (pathEquiv n w).val = n := by
          rw [← (pathEquiv n).injective.eq_iff, pathEquiv_end, Fin.ext_iff, Fin.val_last]
        rw [he]; omega
    | some v =>
      cases w with
      | none =>
        change v = pathEnd n ↔ _
        simp only [pathEquiv_none, pathEquiv_some, Fin.val_last, Fin.val_castSucc]
        have hv := (pathEquiv n v).isLt
        have he : v = pathEnd n ↔ (pathEquiv n v).val = n := by
          rw [← (pathEquiv n).injective.eq_iff, pathEquiv_end, Fin.ext_iff, Fin.val_last]
        rw [he]; omega
      | some w =>
        change (pathG n).Adj v w ↔ _
        simp only [pathEquiv_some, Fin.val_castSucc]
        exact ih v w

def indexedGrid (n : ℕ) : SimpleGraph (Vtx (n + 1)) where
  Adj := gridAdj (n + 1)
  symm := ⟨by intro u v h; unfold gridAdj at *; rcases h with h | h <;> tauto⟩
  loopless := ⟨by intro v h; unfold gridAdj at h; rcases h with ⟨_, h⟩ | ⟨_, h⟩ <;> omega⟩

instance (n : ℕ) : DecidableRel (indexedGrid n).Adj :=
  inferInstanceAs (DecidableRel (gridAdj (n + 1)))

def gridIso (n : ℕ) : (pathG 2 □ pathG n) ≃g indexedGrid n where
  toEquiv := Equiv.prodCongr (pathEquiv 2) (pathEquiv n)
  map_rel_iff' := by
    intro u v
    change gridAdj (n + 1) (pathEquiv 2 u.1, pathEquiv n u.2)
      (pathEquiv 2 v.1, pathEquiv n v.2) ↔ _
    rw [boxProd_adj]
    simp only [gridAdj, (pathEquiv n).injective.eq_iff, (pathEquiv 2).injective.eq_iff,
      ← pathEquiv_adj]
    tauto

theorem indexedGrid_colorings (n : ℕ) (L : Vtx (n + 1) → Finset ℕ) :
    (indexedGrid n).colorings L = properC (gridAdj (n + 1)) L := by
  ext f
  rw [mem_colorings, mem_properC]
  rfl

/-- Count actual grid colourings using the finite-index model. -/
theorem col_eq_properC (n : ℕ) (L : ListAssignment (PathV 2 × PathV n)) :
    (pathG 2 □ pathG n).col L =
      (properC (gridAdj (n + 1)) (L ∘ (gridIso n).symm)).card := by
  rw [← SimpleGraph.col_comp_iso (gridIso n).symm L, SimpleGraph.col,
    indexedGrid_colorings]

/-- The entropy recurrence is exactly the `k = 3` uniform transfer count. -/
theorem a_eq_uniform_transfer (n : ℕ) :
    a n = 12 * (Grid3.Fne 3 n : ℤ) + 6 * (Grid3.Dp 3 n : ℤ) := by
  have step (j : ℕ) :
      (12 * (Grid3.Fne 3 (j + 2) : ℤ) + 6 * (Grid3.Dp 3 (j + 2) : ℤ)) =
      5 * (12 * (Grid3.Fne 3 (j + 1) : ℤ) + 6 * (Grid3.Dp 3 (j + 1) : ℤ)) -
        2 * (12 * (Grid3.Fne 3 j : ℤ) + 6 * (Grid3.Dp 3 j : ℤ)) := by
    simp only [show j + 2 = (j + 1) + 1 by omega, Grid3.Fne_succ, Grid3.Dp_succ]
    norm_num [Grid3.ene, Grid3.gam, Grid3.del]
    ring
  suffices ∀ j, (a j = 12 * (Grid3.Fne 3 j : ℤ) + 6 * (Grid3.Dp 3 j : ℤ)) ∧
      (a (j + 1) = 12 * (Grid3.Fne 3 (j + 1) : ℤ) + 6 * (Grid3.Dp 3 (j + 1) : ℤ))
      from (this n).1
  intro j
  induction j with
  | zero => norm_num [a, Grid3.Fne, Grid3.Dp, Grid3.ene, Grid3.gam, Grid3.del]
  | succ j ih =>
    refine ⟨ih.2, ?_⟩
    change a (j + 2) = _
    rw [a, ih.1, ih.2, ← step]

theorem colConst_three_eq_a (n : ℕ) :
    ((pathG 2 □ pathG n).colConst 3 : ℝ) = (a n : ℝ) := by
  rw [Grid3.colConst_eq (by decide : 2 ≤ 3), a_eq_uniform_transfer]
  norm_num
  ring

end Grid3.Three.Model
