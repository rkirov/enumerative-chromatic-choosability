/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.State5

/-!
# Height four, `k = 5`: the seam inequality at zero mismatch

`ai_research_notes/H4_K5_REVIEW_2026-10-24.md` fix 2. With `μ = (0,0,0)` the four lists are one
list `B` of five colours, and the inequality holds state by state (`zero_state5`): the colours of
a column `s` that miss `B` are moved, injectively, to colours of `B` that `s` does not use (there
are enough, as `s` has at most four colours); the moved column `s'` has the pattern of `s`, its
rows lie in `B`, so its successors in `B` are its uniform successors (`G_erase_eq_GU`), and they
are successors of `s` too, since `B.erase s'ᵢ ⊆ B.erase sᵢ` (`G` is monotone in the lists).
-/

namespace GridGen.Four

open Finset

theorem canon_congr5 {s t : T4} (h : SamePat s t) : canon s = canon t := by
  obtain ⟨h13, h24, h14⟩ := h
  have e1 : (r3 s = r1 s) ↔ (r3 t = r1 t) := by rw [eq_comm, h13, eq_comm]
  have e2 : (r4 s = r2 s) ↔ (r4 t = r2 t) := by rw [eq_comm, h24, eq_comm]
  have e3 : (r4 s = r1 s) ↔ (r4 t = r1 t) := by rw [eq_comm, h14, eq_comm]
  simp only [canon, e1, e2, e3]

theorem sts_mono {A A' B B' C C' D D' : Finset ℕ} (hA : A ⊆ A') (hB : B ⊆ B') (hC : C ⊆ C')
    (hD : D ⊆ D') : sts A B C D ⊆ sts A' B' C' D' := by
  intro t ht; rw [mem_sts] at ht ⊢
  exact ⟨hA ht.1, hB ht.2.1, hC ht.2.2.1, hD ht.2.2.2.1, ht.2.2.2.2⟩

/-- **The state bound at zero mismatch.** -/
theorem zero_state5 {w : Wt} (hw : InBox 5 w) {B : Finset ℕ} (hB : B.card = 5) {s : T4}
    (hs : Proper s) : GU 5 w s ≤ GB w B B B B s := by
  classical
  set S : Finset ℕ := {r1 s, r2 s, r3 s, r4 s} with hSdef
  set F := S \ B with hF
  have hS4 : S.card ≤ 4 := by
    rw [hSdef]; refine (Finset.card_insert_le _ _).trans ?_
    have := (Finset.card_insert_le (r2 s) {r3 s, r4 s}).trans
      (Nat.succ_le_succ (Finset.card_insert_le (r3 s) {r4 s}))
    simp only [Finset.card_singleton] at this; omega
  have hroom : F.card ≤ (B \ S).card := by
    have h1 := Finset.card_sdiff_add_card_inter S B
    have h2 := Finset.card_sdiff_add_card_inter B S
    rw [Finset.inter_comm] at h2
    rw [hF]; omega
  obtain ⟨E, hEsub, hEcard⟩ := Finset.exists_subset_card_eq hroom
  have hcard : Fintype.card {x // x ∈ F} = Fintype.card {x // x ∈ E} := by
    simp only [Fintype.card_coe, hEcard]
  let e : {x // x ∈ F} ≃ {x // x ∈ E} := Fintype.equivOfCardEq hcard
  let f : ℕ → ℕ := fun x => if h : x ∈ F then (e ⟨x, h⟩ : ℕ) else x
  have f_out : ∀ x (h : x ∈ F), f x = e ⟨x, h⟩ := fun x h => dif_pos h
  have f_in : ∀ x, x ∉ F → f x = x := fun x h => dif_neg h
  have fE : ∀ x (h : x ∈ F), f x ∈ B \ S := fun x h => by
    rw [f_out x h]; exact hEsub (e ⟨x, h⟩).2
  have hinj : Set.InjOn f ↑S := by
    intro x hx y hy hxy
    by_cases hxF : x ∈ F <;> by_cases hyF : y ∈ F
    · rw [f_out x hxF, f_out y hyF] at hxy
      have := e.injective (Subtype.ext hxy)
      exact congrArg Subtype.val this
    · exfalso
      have h1 := fE x hxF
      rw [hxy, f_in y hyF] at h1
      exact (Finset.mem_sdiff.mp h1).2 hy
    · exfalso
      have h1 := fE y hyF
      rw [← hxy, f_in x hxF] at h1
      exact (Finset.mem_sdiff.mp h1).2 hx
    · rwa [f_in x hxF, f_in y hyF] at hxy
  have fB : ∀ x ∈ S, f x ∈ B := fun x hx => by
    by_cases hxF : x ∈ F
    · exact (Finset.mem_sdiff.mp (fE x hxF)).1
    · rw [f_in x hxF]
      by_contra hxB
      exact hxF (Finset.mem_sdiff.mpr ⟨hx, hxB⟩)
  have hrows : RowsIn s S := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [hSdef]
  have hsame : SamePat (mapT f s) s := samePat_mapT hinj hrows
  obtain ⟨p12, p23, p34⟩ := hs
  have hprop : Proper (mapT f s) := by
    refine ⟨fun h => p12 (hinj hrows.1 hrows.2.1 h), fun h => p23 (hinj hrows.2.1 hrows.2.2.1 h),
      fun h => p34 (hinj hrows.2.2.1 hrows.2.2.2 h)⟩
  have hrowsB : RowsIn (mapT f s) B :=
    ⟨fB _ hrows.1, fB _ hrows.2.1, fB _ hrows.2.2.1, fB _ hrows.2.2.2⟩
  have hU : GU 5 w s = GU 5 w (mapT f s) := GU_congr 5 w (canon_congr5 hsame).symm
  rw [hU, ← G_erase_eq_GU w (by norm_num) hprop hB hrowsB]
  -- monotonicity
  have sub : ∀ x ∈ S, B.erase (f x) ⊆ B.erase x := by
    intro x hx
    by_cases hxF : x ∈ F
    · have hxB : x ∉ B := (Finset.mem_sdiff.mp hxF).2
      rw [Finset.erase_eq_of_notMem hxB]; exact Finset.erase_subset _ _
    · rw [f_in x hxF]
  have hgw : ∀ t, 0 ≤ gw w t := fun t =>
    le_trans (by rw [rho_five]; norm_num) (gw_mem hw t).1
  unfold GB G
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (sts_mono (sub _ hrows.1) (sub _ hrows.2.1) (sub _ hrows.2.2.1) (sub _ hrows.2.2.2))
    (fun t _ _ => hgw t)

theorem eq_of_inter_card {B C : Finset ℕ} (hB : B.card = 5) (hC : C.card = 5)
    (h : (B ∩ C).card + 0 = 5) : B = C := by
  have h1 : B ∩ C = B := Finset.eq_of_subset_of_card_le inter_subset_left (by omega)
  have h2 : B ∩ C = C := Finset.eq_of_subset_of_card_le inter_subset_right (by omega)
  rw [← h1, h2]

/-- **The seam inequality at `k = 5` and zero mismatch.** -/
theorem seam_zero5k {w : Wt} (hw : InBox 5 w) {X₁ X₂ X₃ X₄ B₁ B₂ B₃ B₄ : Finset ℕ}
    (hB₁ : B₁.card = 5) (hB₂ : B₂.card = 5) (hB₃ : B₃.card = 5) (hB₄ : B₄.card = 5)
    (c2 : (B₁ ∩ B₂).card + 0 = 5) (c3 : (B₂ ∩ B₃).card + 0 = 5) (c4 : (B₃ ∩ B₄).card + 0 = 5) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄, GU 5 w s ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄, GB w B₁ B₂ B₃ B₄ s := by
  have e2 := eq_of_inter_card hB₁ hB₂ c2
  have e3 := eq_of_inter_card hB₂ hB₃ c3
  have e4 := eq_of_inter_card hB₃ hB₄ c4
  subst e2 e3 e4
  exact Finset.sum_le_sum (fun s hs => zero_state5 hw hB₁ (proper_of_mem_sts hs))

end GridGen.Four
