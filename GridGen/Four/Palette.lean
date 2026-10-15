/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.Local
import GridGen.Four.Relabel

/-!
# Height four: the uniform data, and a reference palette next to the actual lists

* `uniform_data`: the canonical uniform successor lists `(range k).erase (canon s)ᵢ` have sizes
  `k - 1`, consecutive intersections `k - 2`, triple intersections `k - 3 + [s₁ = s₃]`,
  `k - 3 + [s₂ = s₄]` and quadruple intersection `k - 4 + [s₁ = s₃] + [s₂ = s₄] + [s₁ = s₄]`.
* `exists_palette`: a `k`-set `P` containing the colours of `s` that differs from `B₂` only by
  the colours of `s` missing from `B₂` (and as many colours of `B₂` dropped to make room). Over
  `P` the uniform successors of `s` give exactly `GU k w s` (`G_erase_eq_GU`), and their lists
  differ from the actual ones `Bᵢ.erase sᵢ` by at most `|Bᵢ ∖ B₂| + |F|` colours.
-/

namespace GridGen.Four

open Finset

/-- The pattern bits of a column. -/
noncomputable def c13 (s : T4) : ℝ := if r1 s = r3 s then 1 else 0
noncomputable def c24 (s : T4) : ℝ := if r2 s = r4 s then 1 else 0
noncomputable def c14 (s : T4) : ℝ := if r1 s = r4 s then 1 else 0

/-- **The uniform data.** -/
theorem uniform_data {k : ℕ} (hk : 4 ≤ k) {s : T4} (hs : Proper s) :
    let C₁ := (range k).erase (r1 (canon s)); let C₂ := (range k).erase (r2 (canon s))
    let C₃ := (range k).erase (r3 (canon s)); let C₄ := (range k).erase (r4 (canon s))
    (C₁.card : ℝ) = k - 1 ∧ (C₂.card : ℝ) = k - 1 ∧ (C₃.card : ℝ) = k - 1 ∧ (C₄.card : ℝ) = k - 1 ∧
    ((C₁ ∩ C₂).card : ℝ) = k - 2 ∧ ((C₂ ∩ C₃).card : ℝ) = k - 2 ∧ ((C₃ ∩ C₄).card : ℝ) = k - 2 ∧
    ((C₁ ∩ C₂ ∩ C₃).card : ℝ) = k - 3 + c13 s ∧ ((C₂ ∩ C₃ ∩ C₄).card : ℝ) = k - 3 + c24 s ∧
    ((C₁ ∩ C₂ ∩ C₃ ∩ C₄).card : ℝ) = k - 4 + c13 s + c24 s + c14 s := by
  intro C₁ C₂ C₃ C₄
  have hR : (range k).card = k := card_range k
  obtain ⟨h1, h2, h3, h4⟩ := rowsIn_canon hk s
  obtain ⟨p12, p23, p34⟩ := proper_canon hs
  obtain ⟨e13, e24, e14⟩ := samePat_canon hs
  have b13 : c13 s = if r1 (canon s) = r3 (canon s) then 1 else 0 := by
    unfold c13; by_cases h : r1 s = r3 s <;> simp [h, e13.mp, e13.mpr] <;> tauto
  have b24 : c24 s = if r2 (canon s) = r4 (canon s) then 1 else 0 := by
    unfold c24; by_cases h : r2 s = r4 s <;> simp [h, e24.mp, e24.mpr] <;> tauto
  have b14 : c14 s = if r1 (canon s) = r4 (canon s) then 1 else 0 := by
    unfold c14; by_cases h : r1 s = r4 s <;> simp [h, e14.mp, e14.mpr] <;> tauto
  refine ⟨?_, ?_, ?_, ?_, card_erase2 hR h1 h2 p12, card_erase2 hR h2 h3 p23,
    card_erase2 hR h3 h4 p34, ?_, ?_, ?_⟩
  · rw [card_erase_hb hR]; simp [hb, h1]
  · rw [card_erase_hb hR]; simp [hb, h2]
  · rw [card_erase_hb hR]; simp [hb, h3]
  · rw [card_erase_hb hR]; simp [hb, h4]
  · rw [card_erase3 hR h1 h2 h3 p12 p23, b13]
  · rw [card_erase3 hR h2 h3 h4 p23 p34, b24]
  · rw [card_erase4 hR h1 h2 h3 h4 p12 p23 p34, b13, b24, b14]

/-- Inserting a colour adds at most its own indicator to a difference. -/
theorem card_insert_sdiff_le (a : ℕ) (T B : Finset ℕ) :
    ((insert a T \ B).card : ℝ) ≤ (if a ∈ B then 0 else 1) + (T \ B).card := by
  by_cases ha : a ∈ B
  · have : insert a T \ B = T \ B := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hx, hxB⟩; exact absurd ha hxB; exact ⟨hx, hxB⟩
      · rintro ⟨hx, hxB⟩; exact ⟨Or.inr hx, hxB⟩
    rw [this]; simp [ha]
  · have hsub : insert a T \ B ⊆ insert a (T \ B) := by
      intro x; simp only [Finset.mem_sdiff, Finset.mem_insert]; tauto
    have := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
    simp only [ha, if_false]
    have : (((insert a T \ B).card : ℕ) : ℝ) ≤ ((T \ B).card + 1 : ℕ) := by exact_mod_cast this
    push_cast at this; linarith

/-- The colours of a column missing from `B`, counted with the rows. -/
noncomputable def jsum (B : Finset ℕ) (s : T4) : ℝ :=
  (if r1 s ∈ B then 0 else 1) + (if r2 s ∈ B then 0 else 1) + (if r3 s ∈ B then 0 else 1)
    + (if r4 s ∈ B then 0 else 1)

theorem card_rows_sdiff_le (B : Finset ℕ) (s : T4) :
    (({r1 s, r2 s, r3 s, r4 s} \ B).card : ℝ) ≤ jsum B s := by
  unfold jsum
  have h1 := card_insert_sdiff_le (r1 s) {r2 s, r3 s, r4 s} B
  have h2 := card_insert_sdiff_le (r2 s) {r3 s, r4 s} B
  have h3 := card_insert_sdiff_le (r3 s) {r4 s} B
  have h4 : (({r4 s} \ B).card : ℝ) ≤ (if r4 s ∈ B then 0 else 1) := by
    by_cases h : r4 s ∈ B
    · have : ({r4 s} : Finset ℕ) \ B = ∅ := by ext x; simp; intro hx; rw [hx]; exact h
      rw [this]; simp [h]
    · have := Finset.card_le_card (Finset.sdiff_subset (s := {r4 s}) (t := B))
      simp only [Finset.card_singleton] at this
      simp only [h, if_false]; exact_mod_cast this
  linarith

/-- **The reference palette.** -/
theorem exists_palette {k : ℕ} (hk : 4 ≤ k) {B₂ : Finset ℕ} (hB₂ : B₂.card = k) (s : T4) :
    ∃ P : Finset ℕ, ∃ f : ℕ, P.card = k ∧ RowsIn s P ∧ (f : ℝ) ≤ jsum B₂ s ∧
      ∀ (B : Finset ℕ) (c : ℕ),
        (((B.erase c) \ (P.erase c)).card : ℝ) ≤ (B \ B₂).card + f ∧
        (((P.erase c) \ (B.erase c)).card : ℝ) ≤ (B₂ \ B).card + f := by
  classical
  set S : Finset ℕ := {r1 s, r2 s, r3 s, r4 s} with hS
  set F := S \ B₂ with hF
  have hS4 : S.card ≤ 4 := by
    rw [hS]; refine (Finset.card_insert_le _ _).trans ?_
    have := (Finset.card_insert_le (r2 s) {r3 s, r4 s}).trans
      (Nat.succ_le_succ (Finset.card_insert_le (r3 s) {r4 s}))
    simp only [Finset.card_singleton] at this; omega
  have hF4 : F.card ≤ 4 := (Finset.card_le_card Finset.sdiff_subset).trans hS4
  have hroom : F.card ≤ (B₂ \ S).card := by
    have h1 := Finset.card_sdiff_add_card_inter S B₂
    have h2 := Finset.card_sdiff_add_card_inter B₂ S
    rw [Finset.inter_comm] at h2
    rw [hF]; omega
  obtain ⟨E, hEsub, hEcard⟩ := Finset.exists_subset_card_eq hroom
  refine ⟨(B₂ \ E) ∪ F, F.card, ?_, ?_, ?_, ?_⟩
  · have hdisj : Disjoint (B₂ \ E) F := by
      rw [Finset.disjoint_left]; intro x hx hxF
      exact (Finset.mem_sdiff.mp hxF).2 (Finset.mem_sdiff.mp hx).1
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_sdiff_of_subset
      (hEsub.trans Finset.sdiff_subset), hEcard, hB₂]
    omega
  · have hrow : ∀ x ∈ S, x ∈ (B₂ \ E) ∪ F := by
      intro x hx
      by_cases hxB : x ∈ B₂
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hxB, fun hxE =>
          (Finset.mem_sdiff.mp (hEsub hxE)).2 hx⟩)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx, hxB⟩)
    exact ⟨hrow _ (by simp [hS]), hrow _ (by simp [hS]), hrow _ (by simp [hS]),
      hrow _ (by simp [hS])⟩
  · exact card_rows_sdiff_le B₂ s
  · intro B c
    constructor
    · have hsub : (B.erase c) \ (((B₂ \ E) ∪ F).erase c) ⊆ (B \ B₂) ∪ E := by
        intro x hx
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_union] at hx ⊢
        by_cases hxB₂ : x ∈ B₂
        · right; by_contra hxE; exact hx.2 ⟨hx.1.1, Or.inl ⟨hxB₂, hxE⟩⟩
        · left; exact ⟨hx.1.2, hxB₂⟩
      have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      rw [hEcard] at this
      exact_mod_cast this
    · have hsub : (((B₂ \ E) ∪ F).erase c) \ (B.erase c) ⊆ (B₂ \ B) ∪ F := by
        intro x hx
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_union] at hx ⊢
        have hxB : x ∉ B := fun h => hx.2 ⟨hx.1.1, h⟩
        rcases hx.1.2 with ⟨hxB₂, -⟩ | hxF
        · left; exact ⟨hxB₂, hxB⟩
        · right; exact hxF
      have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      exact_mod_cast this

end GridGen.Four
