/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Six.Fibre

/-!
# Height six at `k = 6`: the mismatch class `(0,0,0,0,0)`

`GridGen/Five/K5/Zero.lean` with six rows. When all six next lists coincide, every previous column
is relabelled, pattern-preservingly, into the common `6`-list, fixing the colours already in it;
the weighted count only grows (the weights of the cone are nonnegative), so `GU ≤ GB` state by
state (`seam_zero66`).
-/

namespace GridGen.Six

open Finset

/-- Weighted counts are monotone in the lists. -/
theorem G_mono66 {w : Wt6} (hw : InCone6 w) {A B C D E F A' B' C' D' E' F' : Finset ℕ}
    (hA : A ⊆ A') (hB : B ⊆ B') (hC : C ⊆ C') (hD : D ⊆ D') (hE : E ⊆ E') (hF : F ⊆ F') :
    G w A B C D E F ≤ G w A' B' C' D' E' F' := by
  unfold G
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun t _ _ => ?_)
  · intro t ht
    rw [mem_sts] at ht ⊢
    obtain ⟨h1, h2, h3, h4, h5, h6, p⟩ := ht
    exact ⟨hA h1, hB h2, hC h3, hD h4, hE h5, hF h6, p⟩
  · exact cone_nonneg hw _

/-- A pattern-preserving relabelling of a proper column into a `6`-list, fixing the colours
already in the list. -/
theorem exists_relabel6 {B : Finset ℕ} (hB : B.card = 6) {s : T6} (hs : Proper s) :
    ∃ s' : T6, Proper s' ∧ SamePat s' s ∧ RowsIn s' B ∧
      (r1 s ∈ B → r1 s' = r1 s) ∧ (r2 s ∈ B → r2 s' = r2 s) ∧ (r3 s ∈ B → r3 s' = r3 s) ∧
      (r4 s ∈ B → r4 s' = r4 s) ∧ (r5 s ∈ B → r5 s' = r5 s) ∧ (r6 s ∈ B → r6 s' = r6 s) := by
  classical
  set O := rowSet s \ B with hO
  set K := rowSet s ∩ B with hK
  have hcard : O.card ≤ (B \ K).card := by
    have h1 : O.card + K.card = (rowSet s).card := by
      rw [hO, hK, Finset.card_sdiff_add_card_inter]
    have h2 : (rowSet s).card ≤ 6 := by
      unfold rowSet
      refine (Finset.card_insert_le _ _).trans ?_
      refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
      refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
      refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
      refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
      simp
    have h3 : (B \ K).card = 6 - K.card := by
      rw [Finset.card_sdiff_of_subset inter_subset_right, hB]
    omega
  obtain ⟨e⟩ : Nonempty ({x // x ∈ O} ↪ {x // x ∈ B \ K}) :=
    Function.Embedding.nonempty_of_card_le (by rw [Fintype.card_coe, Fintype.card_coe]; exact hcard)
  let f : ℕ → ℕ := fun x => if hx : x ∈ O then (e ⟨x, hx⟩ : ℕ) else x
  have fO : ∀ x (hx : x ∈ O), f x ∈ B \ K := fun x hx => by
    simp only [f, hx, dite_true]; exact (e ⟨x, hx⟩).2
  have fK : ∀ x, x ∉ O → f x = x := fun x hx => by simp only [f, hx, dite_false]
  have hinj : Set.InjOn f ↑(rowSet s) := by
    intro x hx y hy hxy
    simp only [Finset.mem_coe] at hx hy
    by_cases hxO : x ∈ O <;> by_cases hyO : y ∈ O
    · have h' : (e ⟨x, hxO⟩ : ℕ) = e ⟨y, hyO⟩ := by
        simpa only [f, hxO, hyO, dite_true] using hxy
      have := e.injective (Subtype.ext h')
      exact congrArg Subtype.val this
    · exfalso
      have h1 := fO x hxO
      rw [hxy, fK y hyO] at h1
      have : y ∈ K := by
        rw [hK, Finset.mem_inter]; refine ⟨hy, ?_⟩
        by_contra hyB; exact hyO (by rw [hO, Finset.mem_sdiff]; exact ⟨hy, hyB⟩)
      exact (Finset.mem_sdiff.mp h1).2 this
    · exfalso
      have h1 := fO y hyO
      rw [← hxy, fK x hxO] at h1
      have : x ∈ K := by
        rw [hK, Finset.mem_inter]; refine ⟨hx, ?_⟩
        by_contra hxB; exact hxO (by rw [hO, Finset.mem_sdiff]; exact ⟨hx, hxB⟩)
      exact (Finset.mem_sdiff.mp h1).2 this
    · rwa [fK x hxO, fK y hyO] at hxy
  have hrows : RowsIn s (rowSet s) := by
    unfold RowsIn rowSet; simp
  refine ⟨mapT f s, ?_, samePat_mapT hinj hrows, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨p1, p2, p3, p4, p5⟩ := hs
    obtain ⟨m1, m2, m3, m4, m5, m6⟩ := hrows
    exact ⟨fun h => p1 (hinj m1 m2 h), fun h => p2 (hinj m2 m3 h), fun h => p3 (hinj m3 m4 h),
      fun h => p4 (hinj m4 m5 h), fun h => p5 (hinj m5 m6 h)⟩
  · have hin : ∀ x ∈ rowSet s, f x ∈ B := by
      intro x hx
      by_cases hxO : x ∈ O
      · exact (Finset.mem_sdiff.mp (fO x hxO)).1
      · rw [fK x hxO]
        by_contra hxB; exact hxO (by rw [hO, Finset.mem_sdiff]; exact ⟨hx, hxB⟩)
    obtain ⟨m1, m2, m3, m4, m5, m6⟩ := hrows
    exact ⟨hin _ m1, hin _ m2, hin _ m3, hin _ m4, hin _ m5, hin _ m6⟩
  all_goals
    intro hm
    show f _ = _
    apply fK
    rw [hO, Finset.mem_sdiff]; exact fun h => h.2 hm

/-- **The seam inequality at `(0,0,0,0,0)`**, state by state. -/
theorem GB_ge_GU_zero6 {w : Wt6} (hw : InCone6 w) {B : Finset ℕ} (hB : B.card = 6) {s : T6}
    (hs : Proper s) : GU 6 w s ≤ GB w B B B B B B s := by
  obtain ⟨s', hs', hsame, hrows, e1, e2, e3, e4, e5, e6⟩ := exists_relabel6 hB hs
  have hsub : ∀ (c c' : ℕ), (c ∈ B → c' = c) → B.erase c' ⊆ B.erase c := by
    intro c c' h
    by_cases hc : c ∈ B
    · rw [h hc]
    · rw [Finset.erase_eq_of_notMem hc]; exact Finset.erase_subset _ _
  have hmono := G_mono66 hw (hsub _ _ e1) (hsub _ _ e2) (hsub _ _ e3) (hsub _ _ e4) (hsub _ _ e5)
    (hsub _ _ e6)
  rw [G_erase_eq_GU w (by norm_num) hs' hB hrows, GU_congr 6 w (canon_congr hsame)] at hmono
  exact hmono

theorem seam_zero66 {w : Wt6} (hw : InCone6 w) {X₁ X₂ X₃ X₄ X₅ X₆ B : Finset ℕ}
    (hB : B.card = 6) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, GU 6 w s ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, GB w B B B B B B s :=
  Finset.sum_le_sum fun _ hs => GB_ge_GU_zero6 hw hB (proper_of_mem_sts hs)

end GridGen.Six
