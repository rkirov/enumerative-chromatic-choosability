/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.GraphSum

/-!
# The graph induction of the outerplanar ECC proof: counting the colourings of a path

This file is part of the graph induction of the outerplanar ECC proof, a result of this
repository's 2026-11 AI research collaboration. `pathCount k m c d` is the face profile of the
constant data: the number of proper colourings from `k` colours of a path with `m` interior
vertices whose ends are coloured `c` and `d`. By the transfer-matrix recursion it equals
`((k - 1) ^ (m + 1) - (-1) ^ (m + 1)) / k` when `c ≠ d` (`pathCount_of_ne`).
-/

set_option linter.unusedSectionVars false

namespace Outerplanar

open Finset

/-- The face profile of the constant data. -/
noncomputable def pathCount (k m : ℕ) (c d : ℕ) : ℝ :=
  faceSum (fun _ : Fin m => range k) (fun _ _ => 1)
    (fun _ c d => (if c ≠ d then 1 else 0) * (if d ≠ c then 1 else 0)) c d

theorem pathCol_cons_succ {m : ℕ} (c d : ℕ) (g : Fin (m + 1) → ℕ) (i : Fin (m + 2)) :
    pathCol c d g i.succ = pathCol (g 0) d (Fin.tail g) i := by
  unfold pathCol
  rw [Fin.cons_succ, Fin.cons_snoc_eq_snoc_cons, Fin.cons_self_tail]

theorem pathCount_succ (k m : ℕ) (c d : ℕ) :
    pathCount k (m + 1) c d = ∑ e ∈ range k,
      ((if c ≠ e then 1 else 0) * (if e ≠ c then 1 else 0)) * pathCount k m e d := by
  unfold pathCount faceSum
  simp only [Finset.prod_const_one, one_mul]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun g => (g 0, Fin.tail g)) (fun p => Fin.cons p.1 p.2) ?_ ?_ ?_ ?_ ?_
  · intro g hg
    rw [Fintype.mem_piFinset] at hg
    rw [mem_product, Fintype.mem_piFinset]
    exact ⟨hg 0, fun j => hg j.succ⟩
  · rintro ⟨e, g⟩ hp
    rw [mem_product, Fintype.mem_piFinset] at hp
    rw [Fintype.mem_piFinset]
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa using hp.1
    · simpa using hp.2 j
  · intro g _
    exact Fin.cons_self_tail g
  · rintro ⟨e, g⟩ _
    simp
  · intro g _
    rw [Fin.prod_univ_succ]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← Fin.succ_castSucc, pathCol_cons_succ, pathCol_cons_succ]

theorem sum_neSq_ite {k : ℕ} {c d : ℕ} (hc : c ∈ range k) (hd : d ∈ range k) (a b : ℝ) :
    ∑ e ∈ range k, ((if c ≠ e then (1 : ℝ) else 0) * (if e ≠ c then 1 else 0))
        * (if e = d then a else b)
      = if c = d then ((k : ℝ) - 1) * b else a + ((k : ℝ) - 2) * b := by
  by_cases hcd : c = d
  · subst hcd
    rw [ite_eq_left rfl]
    have h1 : ∀ e ∈ range k, ((if c ≠ e then (1 : ℝ) else 0) * (if e ≠ c then 1 else 0))
        * (if e = c then a else b) = b - (if e = c then b else 0) := by
      intro e _
      by_cases he : e = c
      · subst he; simp
      · simp [he, Ne.symm he]
    rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, Finset.sum_ite_eq', ite_eq_left hc]
    simp only [Finset.sum_const, card_range, nsmul_eq_mul]
    ring
  · rw [ite_eq_right hcd]
    have h1 : ∀ e ∈ range k, ((if c ≠ e then (1 : ℝ) else 0) * (if e ≠ c then 1 else 0))
        * (if e = d then a else b)
        = (b - (if e = c then b else 0)) + (if e = d then a - b else 0) := by
      intro e _
      by_cases he : e = c
      · subst he; simp [hcd]
      · by_cases hed : e = d
        · subst hed; simp [he, Ne.symm he]
        · simp [he, Ne.symm he, hed]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', Finset.sum_ite_eq', ite_eq_left hc, ite_eq_left hd]
    simp only [Finset.sum_const, card_range, nsmul_eq_mul]
    ring

theorem sum_neSq {k : ℕ} {d : ℕ} (hd : d ∈ range k) :
    ∑ c ∈ range k, ((if d ≠ c then (1 : ℝ) else 0) * (if c ≠ d then 1 else 0)) * 1
      = (k : ℝ) - 1 := by
  have h := sum_neSq_ite hd hd 1 1
  simpa using h

/-- The number of proper colourings of a path with given end colours. -/
theorem pathCount_eq {k : ℕ} (hk : 1 ≤ k) (m : ℕ) :
    ∀ c ∈ range k, ∀ d ∈ range k, pathCount k m c d =
      if c = d then (((k : ℝ) - 1) ^ (m + 1) + ((k : ℝ) - 1) * (-1) ^ (m + 1)) / k
      else (((k : ℝ) - 1) ^ (m + 1) - (-1) ^ (m + 1)) / k := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  induction m with
  | zero =>
    intro c _ d _
    have h0 : pathCount k 0 c d = (if c ≠ d then 1 else 0) * (if d ≠ c then 1 else 0) := by
      unfold pathCount faceSum
      have hl : ∀ g : Fin 0 → ℕ, (Fin.snoc g d : Fin 1 → ℕ) 0 = d := by
        intro g
        exact Fin.snoc_last _ _
      simp [pathCol, hl, eq_comm]
    rw [h0]
    by_cases hcd : c = d
    · subst hcd; simp
    · simp only [ne_eq, hcd, not_false_eq_true, ite_true, Ne.symm hcd, ite_false]
      field_simp
      ring
  | succ m ih =>
    intro c hc d hd
    rw [pathCount_succ, Finset.sum_congr rfl fun e he => by rw [ih e he d hd],
      sum_neSq_ite hc hd]
    by_cases hcd : c = d
    · rw [ite_eq_left hcd, ite_eq_left hcd]
      field_simp
      ring
    · rw [ite_eq_right hcd, ite_eq_right hcd]
      field_simp
      ring

theorem pathCount_of_ne {k : ℕ} (hk : 1 ≤ k) (m : ℕ) {c d : ℕ} (hc : c ∈ range k)
    (hd : d ∈ range k) (hcd : c ≠ d) :
    pathCount k m c d = (((k : ℝ) - 1) ^ (m + 1) - (-1) ^ (m + 1)) / k := by
  rw [pathCount_eq hk m c hc d hd, ite_eq_right hcd]

end Outerplanar
