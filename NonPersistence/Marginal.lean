/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import NonPersistence.BadList

/-!
# What the four kinds of apex offer (Zhang–Dong, Lemma 10)

Fix a proper `LH`-coloring `θ` of `H m` and let `Z = {θ s₁, θ s₂}`. Each apex of kind `j` may
take any color of `C ∪ D j` not in `Z`, and the four kinds together offer

`∏_{j < 4} |(C ∪ D j) \ Z|`

choices per block of four. With `k = m + 3` there are two regimes:

* `θ s₁ = θ s₂`. The common color is forced into `C` — it must lie in both `range (m + 4)` and
  `C ∪ B₂` — so it is missing from every one of the four lists, and each offers `k` colors:
  `k⁴` per block. This is the *large* regime, and it is the one the constant list also enjoys.
* `θ s₁ ≠ θ s₂`. Now `Z` meets the four lists unevenly, and the product is at most
  `k² (k - 1)(k + 1) = k²(k² - 1)` — strictly less than `k⁴`. This deficit, compounded over `t`
  blocks, is what destroys the count.
-/

open Finset SimpleGraph

namespace ZhangDong

/-! ### Removing one or two colors from a list of size `m + 4` -/

theorem card_sdiff_pair (S : Finset ℕ) (z₁ z₂ : ℕ) (h12 : z₁ ≠ z₂) :
    (S \ {z₁, z₂}).card
      = S.card - ((if z₁ ∈ S then 1 else 0) + (if z₂ ∈ S then 1 else 0)) := by
  have hsub : (S \ {z₁, z₂}).card + (S ∩ {z₁, z₂}).card = S.card :=
    Finset.card_sdiff_add_card_inter S {z₁, z₂}
  have hint : (S ∩ {z₁, z₂}).card
      = (if z₁ ∈ S then 1 else 0) + (if z₂ ∈ S then 1 else 0) := by
    by_cases h1 : z₁ ∈ S <;> by_cases h2 : z₂ ∈ S
    · rw [if_pos h1, if_pos h2]
      have : S ∩ {z₁, z₂} = {z₁, z₂} :=
        Finset.inter_eq_right.mpr (by
          intro c hc
          rcases Finset.mem_insert.mp hc with rfl | hc
          · exact h1
          · rw [Finset.mem_singleton] at hc; subst hc; exact h2)
      rw [this, Finset.card_insert_of_notMem (by simpa using h12), Finset.card_singleton]
    · rw [if_pos h1, if_neg h2]
      have : S ∩ {z₁, z₂} = {z₁} := by
        ext c
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hcS, rfl | rfl⟩
          · rfl
          · exact absurd hcS h2
        · rintro rfl; exact ⟨h1, Or.inl rfl⟩
      rw [this, Finset.card_singleton]
    · rw [if_neg h1, if_pos h2]
      have : S ∩ {z₁, z₂} = {z₂} := by
        ext c
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hcS, rfl | rfl⟩
          · exact absurd hcS h1
          · rfl
        · rintro rfl; exact ⟨h2, Or.inr rfl⟩
      rw [this, Finset.card_singleton]
    · rw [if_neg h1, if_neg h2]
      have : S ∩ {z₁, z₂} = ∅ := by
        ext c
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
          Finset.notMem_empty, iff_false, not_and]
        rintro hcS (rfl | rfl)
        · exact h1 hcS
        · exact h2 hcS
      rw [this, Finset.card_empty]
  omega

theorem card_sdiff_singleton_of_mem (S : Finset ℕ) {c : ℕ} (hc : c ∈ S) :
    (S \ {c}).card = S.card - 1 := by
  rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hc]

/-! ### The equal case -/

/-- With `θ s₁ = θ s₂ = c` and `c` one of the shared colors, every apex list loses exactly one
color: `k` choices apiece. -/
theorem mem_A_of_mem_C (m i : ℕ) {c : ℕ} (hc : c ∈ C m) : c ∈ A m i :=
  Finset.mem_union_left _ hc

theorem card_A_sdiff_single (m i : ℕ) {c : ℕ} (hc : c ∈ C m) :
    (A m i \ {c}).card = m + 3 := by
  rw [card_sdiff_singleton_of_mem _ (mem_A_of_mem_C m i hc), card_A]
  omega

/-! ### The unequal case -/

/-- **Zhang–Dong, Lemma 10, the bound that matters.** If `s₁` and `s₂` receive different colors,
one block of four apexes offers at most `k² (k - 1)(k + 1)` colorings, where `k = m + 3`. -/
theorem prod_four_le (m : ℕ) {z₁ z₂ : ℕ} (h12 : z₁ ≠ z₂)
    (h1 : z₁ ∈ Finset.range (m + 4)) (h2 : z₂ ∈ C m ∪ {m + 4, m + 5}) :
    ∏ j ∈ Finset.range 4, ((C m ∪ D m j) \ {z₁, z₂}).card
      ≤ (m + 3) ^ 2 * ((m + 2) * (m + 4)) := by
  rw [Finset.mem_range] at h1
  simp only [C, Finset.mem_union, Finset.mem_range, Finset.mem_insert,
    Finset.mem_singleton] at h2
  -- The four transversals, spelled out.
  have hD0 : D m 0 = {m + 2, m + 4} := rfl
  have hD1 : D m 1 = {m + 2, m + 5} := rfl
  have hD2 : D m 2 = {m + 3, m + 4} := rfl
  have hD3 : D m 3 = {m + 3, m + 5} := rfl
  -- Membership in each of the four lists, as a numeric condition.
  have e0 : ∀ z : ℕ, z ∈ C m ∪ D m 0 ↔ z < m + 2 ∨ z = m + 2 ∨ z = m + 4 := by
    intro z
    rw [hD0]
    simp only [C, Finset.mem_union, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
  have e1 : ∀ z : ℕ, z ∈ C m ∪ D m 1 ↔ z < m + 2 ∨ z = m + 2 ∨ z = m + 5 := by
    intro z
    rw [hD1]
    simp only [C, Finset.mem_union, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
  have e2 : ∀ z : ℕ, z ∈ C m ∪ D m 2 ↔ z < m + 2 ∨ z = m + 3 ∨ z = m + 4 := by
    intro z
    rw [hD2]
    simp only [C, Finset.mem_union, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
  have e3 : ∀ z : ℕ, z ∈ C m ∪ D m 3 ↔ z < m + 2 ∨ z = m + 3 ∨ z = m + 5 := by
    intro z
    rw [hD3]
    simp only [C, Finset.mem_union, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
  -- One list loses two colors, one, or none.
  have cb : ∀ j : ℕ, j < 4 → z₁ ∈ C m ∪ D m j → z₂ ∈ C m ∪ D m j →
      ((C m ∪ D m j) \ {z₁, z₂}).card = m + 2 := by
    intro j hj ha hb
    have h := card_sdiff_pair (C m ∪ D m j) z₁ z₂ h12
    rw [card_D m hj, if_pos ha, if_pos hb] at h
    omega
  have cl : ∀ j : ℕ, j < 4 → z₁ ∈ C m ∪ D m j → z₂ ∉ C m ∪ D m j →
      ((C m ∪ D m j) \ {z₁, z₂}).card = m + 3 := by
    intro j hj ha hb
    have h := card_sdiff_pair (C m ∪ D m j) z₁ z₂ h12
    rw [card_D m hj, if_pos ha, if_neg hb] at h
    omega
  have cr : ∀ j : ℕ, j < 4 → z₁ ∉ C m ∪ D m j → z₂ ∈ C m ∪ D m j →
      ((C m ∪ D m j) \ {z₁, z₂}).card = m + 3 := by
    intro j hj ha hb
    have h := card_sdiff_pair (C m ∪ D m j) z₁ z₂ h12
    rw [card_D m hj, if_neg ha, if_pos hb] at h
    omega
  have cn : ∀ j : ℕ, j < 4 → z₁ ∉ C m ∪ D m j → z₂ ∉ C m ∪ D m j →
      ((C m ∪ D m j) \ {z₁, z₂}).card = m + 4 := by
    intro j hj ha hb
    have h := card_sdiff_pair (C m ∪ D m j) z₁ z₂ h12
    rw [card_D m hj, if_neg ha, if_neg hb] at h
    omega
  -- Four factors, each at most `m + 4` and never two of them that big.
  have step : ∀ a b c d : ℕ, a ≤ m + 3 → b ≤ m + 3 → c ≤ m + 2 → d ≤ m + 4 →
      ∀ p : ℕ, p = a * b * c * d → p ≤ (m + 3) ^ 2 * ((m + 2) * (m + 4)) := by
    intro a b c d ha hb hc hd p hp
    subst hp
    calc a * b * c * d ≤ (m + 3) * (m + 3) * (m + 2) * (m + 4) :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul ha hb) hc) hd
      _ = (m + 3) ^ 2 * ((m + 2) * (m + 4)) := by ring
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  rcases (show z₁ < m + 2 ∨ z₁ = m + 2 ∨ z₁ = m + 3 by omega) with hz1 | hz1 | hz1 <;>
      rcases h2 with hz2 | hz2 | hz2
  -- `z₁ ∈ C`, `z₂ ∈ C`: both colors are missing from all four lists.
  · rw [cb 0 (by omega) ((e0 z₁).mpr (by omega)) ((e0 z₂).mpr (by omega)),
      cb 1 (by omega) ((e1 z₁).mpr (by omega)) ((e1 z₂).mpr (by omega)),
      cb 2 (by omega) ((e2 z₁).mpr (by omega)) ((e2 z₂).mpr (by omega)),
      cb 3 (by omega) ((e3 z₁).mpr (by omega)) ((e3 z₂).mpr (by omega))]
    refine step (m + 2) (m + 2) (m + 2) (m + 2) (by omega) (by omega) (by omega) (by omega) _ ?_
    ring
  -- `z₁ ∈ C`, `z₂ = m + 4`: the second color hits the lists `0` and `2`.
  · rw [cb 0 (by omega) ((e0 z₁).mpr (by omega)) ((e0 z₂).mpr (by omega)),
      cl 1 (by omega) ((e1 z₁).mpr (by omega)) (by simp only [e1]; omega),
      cb 2 (by omega) ((e2 z₁).mpr (by omega)) ((e2 z₂).mpr (by omega)),
      cl 3 (by omega) ((e3 z₁).mpr (by omega)) (by simp only [e3]; omega)]
    refine step (m + 3) (m + 3) (m + 2) (m + 2) (by omega) (by omega) (by omega) (by omega) _ ?_
    ring
  -- `z₁ ∈ C`, `z₂ = m + 5`: the second color hits the lists `1` and `3`.
  · rw [cl 0 (by omega) ((e0 z₁).mpr (by omega)) (by simp only [e0]; omega),
      cb 1 (by omega) ((e1 z₁).mpr (by omega)) ((e1 z₂).mpr (by omega)),
      cl 2 (by omega) ((e2 z₁).mpr (by omega)) (by simp only [e2]; omega),
      cb 3 (by omega) ((e3 z₁).mpr (by omega)) ((e3 z₂).mpr (by omega))]
    refine step (m + 3) (m + 3) (m + 2) (m + 2) (by omega) (by omega) (by omega) (by omega) _ ?_
    ring
  -- `z₁ = m + 2`, `z₂ ∈ C`: the first color hits the lists `0` and `1`.
  · rw [cb 0 (by omega) ((e0 z₁).mpr (by omega)) ((e0 z₂).mpr (by omega)),
      cb 1 (by omega) ((e1 z₁).mpr (by omega)) ((e1 z₂).mpr (by omega)),
      cr 2 (by omega) (by simp only [e2]; omega) ((e2 z₂).mpr (by omega)),
      cr 3 (by omega) (by simp only [e3]; omega) ((e3 z₂).mpr (by omega))]
    refine step (m + 3) (m + 3) (m + 2) (m + 2) (by omega) (by omega) (by omega) (by omega) _ ?_
    ring
  -- `z₁ = m + 2`, `z₂ = m + 4`: only list `0` loses both, and list `3` loses neither.
  · rw [cb 0 (by omega) ((e0 z₁).mpr (by omega)) ((e0 z₂).mpr (by omega)),
      cl 1 (by omega) ((e1 z₁).mpr (by omega)) (by simp only [e1]; omega),
      cr 2 (by omega) (by simp only [e2]; omega) ((e2 z₂).mpr (by omega)),
      cn 3 (by omega) (by simp only [e3]; omega) (by simp only [e3]; omega)]
    refine step (m + 3) (m + 3) (m + 2) (m + 4) (by omega) (by omega) (by omega) (by omega) _ ?_
    ring
  -- `z₁ = m + 2`, `z₂ = m + 5`: only list `1` loses both, and list `2` loses neither.
  · rw [cl 0 (by omega) ((e0 z₁).mpr (by omega)) (by simp only [e0]; omega),
      cb 1 (by omega) ((e1 z₁).mpr (by omega)) ((e1 z₂).mpr (by omega)),
      cn 2 (by omega) (by simp only [e2]; omega) (by simp only [e2]; omega),
      cr 3 (by omega) (by simp only [e3]; omega) ((e3 z₂).mpr (by omega))]
    refine step (m + 3) (m + 3) (m + 2) (m + 4) (by omega) (by omega) (by omega) (by omega) _ ?_
    ring
  -- `z₁ = m + 3`, `z₂ ∈ C`: the first color hits the lists `2` and `3`.
  · rw [cr 0 (by omega) (by simp only [e0]; omega) ((e0 z₂).mpr (by omega)),
      cr 1 (by omega) (by simp only [e1]; omega) ((e1 z₂).mpr (by omega)),
      cb 2 (by omega) ((e2 z₁).mpr (by omega)) ((e2 z₂).mpr (by omega)),
      cb 3 (by omega) ((e3 z₁).mpr (by omega)) ((e3 z₂).mpr (by omega))]
    refine step (m + 3) (m + 3) (m + 2) (m + 2) (by omega) (by omega) (by omega) (by omega) _ ?_
    ring
  -- `z₁ = m + 3`, `z₂ = m + 4`: only list `2` loses both, and list `1` loses neither.
  · rw [cr 0 (by omega) (by simp only [e0]; omega) ((e0 z₂).mpr (by omega)),
      cn 1 (by omega) (by simp only [e1]; omega) (by simp only [e1]; omega),
      cb 2 (by omega) ((e2 z₁).mpr (by omega)) ((e2 z₂).mpr (by omega)),
      cl 3 (by omega) ((e3 z₁).mpr (by omega)) (by simp only [e3]; omega)]
    refine step (m + 3) (m + 3) (m + 2) (m + 4) (by omega) (by omega) (by omega) (by omega) _ ?_
    ring
  -- `z₁ = m + 3`, `z₂ = m + 5`: only list `3` loses both, and list `0` loses neither.
  · rw [cn 0 (by omega) (by simp only [e0]; omega) (by simp only [e0]; omega),
      cr 1 (by omega) (by simp only [e1]; omega) ((e1 z₂).mpr (by omega)),
      cl 2 (by omega) ((e2 z₁).mpr (by omega)) (by simp only [e2]; omega),
      cb 3 (by omega) ((e3 z₁).mpr (by omega)) ((e3 z₂).mpr (by omega))]
    refine step (m + 3) (m + 3) (m + 2) (m + 4) (by omega) (by omega) (by omega) (by omega) _ ?_
    ring

end ZhangDong
