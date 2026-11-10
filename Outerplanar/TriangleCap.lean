/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.Thread

/-!
# The triangle with three colours has capacity six

For three lists of three colours on the triangle, with the identity matching on each of the
three edges, the weighted number of proper colourings is at least six times the product of the
geometric means of the weights (`triCover_capGE`). The proof is the thread theorem
`Cover.capGE_of_thread`, applied to

* a section that on every edge is constant or uses, at both ends, a colour missing from the
  other list (`exists_section`), and
* the uniform law on the three singletons.
-/

namespace Outerplanar

open Finset

/-! ### The section -/

/-- If `C` has a colour in neither `A` nor `B`, there is a section. -/
theorem section_of_private {A B C : Finset ℕ} (hA : A.card = 3) (hB : B.card = 3)
    (hC : C.card = 3) {z : ℕ} (hzC : z ∈ C) (hzA : z ∉ A) (hzB : z ∉ B) :
    ∃ a b c, a ∈ A ∧ b ∈ B ∧ c ∈ C ∧ (a = b ∨ (a ∉ B ∧ b ∉ A)) ∧ (b = c ∨ (b ∉ C ∧ c ∉ B)) ∧
      (c = a ∨ (c ∉ A ∧ a ∉ C)) := by
  have hne : ∀ D : Finset ℕ, D.card = 3 → z ∉ D → ∃ x ∈ D, x ∉ C := by
    intro D hD hzD
    by_contra h
    have hsub : D ⊆ C := fun x hx => by
      by_contra hxC
      exact h ⟨x, hx, hxC⟩
    have := Finset.eq_of_subset_of_card_le hsub (by rw [hC, hD])
    exact hzD (this ▸ hzC)
  obtain ⟨x, hxA, hxC⟩ := hne A hA hzA
  obtain ⟨y, hyB, hyC⟩ := hne B hB hzB
  by_cases h : ∃ x, x ∈ A ∧ x ∈ B ∧ x ∉ C
  · obtain ⟨x, hxA, hxB, hxC⟩ := h
    exact ⟨x, x, z, hxA, hxB, hzC, Or.inl rfl, Or.inr ⟨hxC, hzB⟩, Or.inr ⟨hzA, hxC⟩⟩
  · exact ⟨x, y, z, hxA, hyB, hzC, Or.inr ⟨fun hxB => h ⟨x, hxA, hxB, hxC⟩,
      fun hyA => h ⟨y, hyA, hyB, hyC⟩⟩, Or.inr ⟨hyC, hzB⟩, Or.inr ⟨hzA, hxC⟩⟩

/-- Three lists of three colours without a common colour: one of them has a private colour. -/
theorem exists_private {A B C : Finset ℕ} (hA : A.card = 3) (hB : B.card = 3) (hC : C.card = 3)
    (hno : ∀ x, x ∈ A → x ∈ B → x ∉ C) :
    (∃ z ∈ A, z ∉ B ∧ z ∉ C) ∨ (∃ z ∈ B, z ∉ C ∧ z ∉ A) ∨ (∃ z ∈ C, z ∉ A ∧ z ∉ B) := by
  by_contra hcon
  have key : ∀ X Y Z : Finset ℕ, (∀ x, x ∈ X → x ∈ Y → x ∉ Z) → (¬ ∃ z ∈ X, z ∉ Y ∧ z ∉ Z) →
      X.card = (X ∩ Y).card + (X ∩ Z).card := by
    intro X Y Z hXYZ hpriv
    have hdis : Disjoint (X ∩ Y) (X ∩ Z) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      exact hXYZ x (Finset.mem_inter.mp hx).1 (Finset.mem_inter.mp hx).2 (Finset.mem_inter.mp hx').2
    rw [← Finset.card_union_of_disjoint hdis]
    congr 1
    ext x
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · intro hx
      by_contra h
      exact hpriv ⟨x, hx, fun hy => h (Or.inl ⟨hx, hy⟩), fun hz => h (Or.inr ⟨hx, hz⟩)⟩
    · rintro (h | h) <;> exact h.1
  have h1 := key A B C hno fun h => hcon (Or.inl h)
  have h2 := key B C A (fun x hxB hxC hxA => hno x hxA hxB hxC) fun h => hcon (Or.inr (Or.inl h))
  have h3 := key C A B (fun x hxC hxA hxB => hno x hxA hxB hxC)
    fun h => hcon (Or.inr (Or.inr h))
  rw [Finset.inter_comm B A] at h2
  rw [Finset.inter_comm C A, Finset.inter_comm C B] at h3
  clear * - h1 h2 h3 hA hB hC
  omega

theorem exists_section_three {A B C : Finset ℕ} (hA : A.card = 3) (hB : B.card = 3)
    (hC : C.card = 3) :
    ∃ a b c, a ∈ A ∧ b ∈ B ∧ c ∈ C ∧ (a = b ∨ (a ∉ B ∧ b ∉ A)) ∧ (b = c ∨ (b ∉ C ∧ c ∉ B)) ∧
      (c = a ∨ (c ∉ A ∧ a ∉ C)) := by
  by_cases hcom : ∃ x, x ∈ A ∧ x ∈ B ∧ x ∈ C
  · obtain ⟨x, hxA, hxB, hxC⟩ := hcom
    exact ⟨x, x, x, hxA, hxB, hxC, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  · have hno : ∀ x, x ∈ A → x ∈ B → x ∉ C := fun x hxA hxB hxC => hcom ⟨x, hxA, hxB, hxC⟩
    rcases exists_private hA hB hC hno with ⟨z, hz, hz1, hz2⟩ | ⟨z, hz, hz1, hz2⟩ | ⟨z, hz, hz1, hz2⟩
    · obtain ⟨b, c, a, hb, hc, ha, h1, h2, h3⟩ := section_of_private hB hC hA hz hz1 hz2
      exact ⟨a, b, c, ha, hb, hc, h3, h1, h2⟩
    · obtain ⟨c, a, b, hc, ha, hb, h1, h2, h3⟩ := section_of_private hC hA hB hz hz1 hz2
      exact ⟨a, b, c, ha, hb, hc, h2, h3, h1⟩
    · exact section_of_private hA hB hC hz hz1 hz2

/-- **The section.** Three lists of three colours on the triangle have a section that on every
edge is constant, or uses at both ends a colour that is missing from the other list. -/
theorem exists_section (L : Fin 3 → Finset ℕ) (hL : ∀ i, (L i).card = 3) :
    ∃ b : Fin 3 → ℕ, (∀ i, b i ∈ L i) ∧
      ∀ i, b i = b (i + 1) ∨ (b i ∉ L (i + 1) ∧ b (i + 1) ∉ L i) := by
  obtain ⟨a, b, c, ha, hb, hc, h1, h2, h3⟩ := exists_section_three (hL 0) (hL 1) (hL 2)
  refine ⟨![a, b, c], fun i => ?_, fun i => ?_⟩
  · fin_cases i
    · exact ha
    · exact hb
    · exact hc
  · fin_cases i
    · exact h1
    · exact h2
    · exact h3

/-! ### The law -/

theorem sum_card_one (g : Finset (Fin 3) → ℝ) :
    ∑ J, (if J.card = 1 then g J else 0) = ∑ i, g {i} := by
  rw [← Finset.sum_filter]
  have h : (univ.filter fun J : Finset (Fin 3) => J.card = 1)
      = univ.image (fun i => ({i} : Finset (Fin 3))) := by
    ext J
    simp only [mem_filter, mem_univ, true_and, mem_image, Finset.card_eq_one]
    exact ⟨fun ⟨a, h⟩ => ⟨a, h.symm⟩, fun ⟨a, h⟩ => ⟨a, h.symm⟩⟩
  rw [h, Finset.sum_image fun a _ b _ h => Finset.singleton_injective h]

theorem arcW_two_singleton (i : Fin 3) : arcW 2 ({i} : Finset (Fin 3)) = 2 := by
  have e0 : (0 : Fin 3) - 1 = 2 := by decide
  have e1 : (1 : Fin 3) - 1 = 0 := by decide
  have e2 : (2 : Fin 3) - 1 = 1 := by decide
  have n1 : ¬ (2 : Fin 3) = 1 := by decide
  have n2 : ¬ (0 : Fin 3) = 2 := by decide
  have n3 : ¬ (1 : Fin 3) = 0 := by decide
  have n4 : ¬ (1 : Fin 3) = 2 := by decide
  have n5 : ¬ (2 : Fin 3) = 0 := by decide
  have n6 : ¬ (0 : Fin 3) = 1 := by decide
  have h0 : arcW 2 ({0} : Finset (Fin 3)) = 2 := by
    rw [arcW, show (({(0 : Fin 3)} : Finset (Fin 3))ᶜ) = {1, 2} from by decide]
    norm_num [Finset.prod_insert, e0, e1, e2, n1, n2, n3, n4, n5, n6]
  have h1 : arcW 2 ({1} : Finset (Fin 3)) = 2 := by
    rw [arcW, show (({(1 : Fin 3)} : Finset (Fin 3))ᶜ) = {2, 0} from by decide]
    norm_num [Finset.prod_insert, e0, e1, e2, n1, n2, n3, n4, n5, n6]
  have h2 : arcW 2 ({2} : Finset (Fin 3)) = 2 := by
    rw [arcW, show (({(2 : Fin 3)} : Finset (Fin 3))ᶜ) = {0, 1} from by decide]
    norm_num [Finset.prod_insert, e0, e1, e2, n1, n2, n3, n4, n5, n6]
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-! ### The capacity -/

/-- The cover of the triangle by the lists `L`, with the identity matching on every edge. -/
def triCover (L : Fin 3 → Finset ℕ) : Cover 3 := ⟨L, fun _ x y => x = y⟩

/-- **The triangle has capacity six**: three lists of three colours, any positive weights with
product one on each list. -/
theorem triCover_capGE (L : Fin 3 → Finset ℕ) (hL : ∀ i, (L i).card = 3) (b' : Fin 3 → ℕ) :
    (triCover L).CapGE univ b' 6 := by
  obtain ⟨b, hb1, hb2⟩ := exists_section L hL
  have hsucc : ∀ i : Fin 3, i + 1 ≠ i := by decide
  refine Cover.capGE_of_thread (triCover L) (k := 3) (le_refl 3) hL ?_ (b := b) hb1 ?_
    (by norm_num) (fun J => if J.card = 1 then 1 / 3 else 0) ?_ ?_ ?_ ?_ ?_ b'
  · exact fun i => ⟨fun x _ y _ y' _ h h' => h.symm.trans h', fun x _ x' _ y _ h h' => h.trans h'.symm⟩
  · intro i
    rcases hb2 i with h | h
    · exact Or.inl h
    · exact Or.inr ⟨fun y hy hby => h.1 (hby ▸ hy), fun x hx hxb => h.2 (hxb ▸ hx)⟩
  · intro J
    split_ifs <;> norm_num
  · intro J hJ
    have hc : J.card = 1 := by
      by_contra hc
      rw [ite_eq_right hc] at hJ
      exact lt_irrefl _ hJ
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hc
    refine ⟨Finset.singleton_ne_empty i, fun j hj hj1 => ?_, ?_⟩
    · rw [Finset.mem_singleton] at hj hj1
      rw [hj] at hj1
      exact hsucc i hj1
    · rw [show (3 - 1 : ℕ) = 2 from rfl, arcW_two_singleton]
      norm_num
  · rw [sum_card_one]
    simp
  · intro i
    rw [Finset.sum_filter]
    have h : ∀ J : Finset (Fin 3), (if i ∈ J then (if J.card = 1 then (1 / 3 : ℝ) else 0) else 0)
        = if J.card = 1 then (if i ∈ J then (1 / 3 : ℝ) else 0) else 0 := by
      intro J
      split_ifs <;> rfl
    rw [Finset.sum_congr rfl fun J _ => h J, sum_card_one]
    simp [Finset.mem_singleton, Finset.sum_ite_eq]
  · have h : ∀ J : Finset (Fin 3),
        (if J.card = 1 then (1 / 3 : ℝ) else 0)
          * Real.log (arcW (3 - 1) J / (if J.card = 1 then (1 / 3 : ℝ) else 0))
        = if J.card = 1 then (1 / 3 : ℝ) * Real.log (arcW 2 J / (1 / 3)) else 0 := by
      intro J
      split_ifs
      · rfl
      · rw [zero_mul]
    rw [Finset.sum_congr rfl fun J _ => h J, sum_card_one]
    simp only [arcW_two_singleton]
    rw [show (2 : ℝ) / (1 / 3) = 6 from by norm_num]
    simp

end Outerplanar
