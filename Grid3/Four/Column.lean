/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Grid3.Four.Single

/-!
# The column inequalities at `k = 4`

From the conditional pair lemma (`pair_main`) and the regular-colour lemma (`single_main`):
for every near-`4` punctured column `(X, Y, Z)` and next column `(T, M, B)` of `4`-lists,

* the `(H1)` column sum is nonnegative (`colH_four`);
* the `(C1_r)` column sum is at least `-1` (`colC_neg`), and nonnegative unless the column is
  *Bad* — some irregular middle colour sits in a `BadU`/`BadF` configuration (`colC_or`);
* if some irregular middle colour is *not* Bad, the sum is at least `1` (`colC_gap`).
-/

open Finset

namespace Grid3
namespace Four

/-- A Bad column: some middle colour is irregular and in a Bad configuration. -/
def BadCol (X Y Z T M B : Finset ℕ) : Prop :=
  ∃ y₀ ∈ Y, y₀ ∈ M ∧ ¬ (y₀ ∈ T ∧ y₀ ∈ B) ∧ (BadU X Z T M B y₀ ∨ BadF X Z T M B y₀)

/-- The sum of the pair terms of `y₀` against the rest of `Y`. -/
theorem sum_pair_eq (q : ℕ → ℤ) {Y : Finset ℕ} {y₀ : ℕ} (h : y₀ ∈ Y) :
    ∑ y' ∈ Y.erase y₀, (q y₀ + 2 * q y') = ((Y.card : ℤ) - 3) * q y₀ + 2 * ∑ y ∈ Y, q y := by
  rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum, Finset.card_erase_of_mem h,
    ← Finset.add_sum_erase Y q h, nsmul_eq_mul]
  have hpos : 1 ≤ Y.card := Finset.card_pos.mpr ⟨y₀, h⟩
  push_cast [Nat.cast_sub hpos]
  ring

theorem card_three_or_four {Y : Finset ℕ} (hY : NearK 4 Y) : (Y.card : ℤ) = 3 ∨ (Y.card : ℤ) = 4 := by
  rcases hY with h | h <;> simp [h]

section
variable {X Y Z T M B : Finset ℕ} (hX : NearK 4 X) (hY : NearK 4 Y) (hZ : NearK 4 Z)
  (hT : T.card = 4) (hM : M.card = 4) (hB : B.card = 4)
include hX hZ hT hM hB

/-- A colour with a negative `(C1_r)` term is irregular. -/
theorem irregular_of_negC {y : ℕ} (h : QC 4 X Z T M B y < 0) : y ∈ M ∧ ¬ (y ∈ T ∧ y ∈ B) := by
  by_contra hc
  have hreg : Regular T M B y := by
    unfold Regular; tauto
  exact absurd (single_main hX hZ hT hM hB hreg).2 (not_le.mpr h)

theorem irregular_of_negH {y : ℕ} (h : QH 4 X Z T M B y < 0) : y ∈ M ∧ ¬ (y ∈ T ∧ y ∈ B) := by
  by_contra hc
  have hreg : Regular T M B y := by
    unfold Regular; tauto
  exact absurd (single_main hX hZ hT hM hB hreg).1 (not_le.mpr h)

/-- The two Bad configurations exclude every other irregular colour. -/
theorem irregular_unique {y₀ y₁ : ℕ} (h0 : y₀ ∈ M ∧ ¬ (y₀ ∈ T ∧ y₀ ∈ B))
    (h1 : BadU X Z T M B y₁ ∨ BadF X Z T M B y₁) (hne : y₀ ≠ y₁) : False := by
  obtain ⟨h0M, h0irr⟩ := h0
  rcases h1 with ⟨h1M, h1T, h1B, -, -, -, -, -, -, hMT, hMB, -⟩ | ⟨h1M, h1T, h1B, -, -, -, -, -, -, hMB, hMT, -⟩
  · -- `M \ T = {y₁}`, so `y₀ ∈ T`; then `y₀ ∉ B`, but `M ⊆ B`
    by_cases h0T : y₀ ∈ T
    · have h0B : y₀ ∉ B := fun hb => h0irr ⟨h0T, hb⟩
      have : y₀ ∈ M.filter (· ∉ B) := Finset.mem_filter.mpr ⟨h0M, h0B⟩
      have := Finset.card_pos.mpr ⟨y₀, this⟩
      omega
    · have hsub : ({y₀, y₁} : Finset ℕ) ⊆ M.filter (· ∉ T) := by
        intro a ha
        rw [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨h0M, h0T⟩
        · exact Finset.mem_filter.mpr ⟨h1M, h1T⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_pair hne] at this
      omega
  · by_cases h0B : y₀ ∈ B
    · have h0T : y₀ ∉ T := fun ht => h0irr ⟨ht, h0B⟩
      have : y₀ ∈ M.filter (· ∉ T) := Finset.mem_filter.mpr ⟨h0M, h0T⟩
      have := Finset.card_pos.mpr ⟨y₀, this⟩
      omega
    · have hsub : ({y₀, y₁} : Finset ℕ) ⊆ M.filter (· ∉ B) := by
        intro a ha
        rw [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨h0M, h0B⟩
        · exact Finset.mem_filter.mpr ⟨h1M, h1B⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_pair hne] at this
      omega

end

/-- Pairs at a fixed colour, summed over its partners: if every pair sum is at least `c`, then
`(|Y| - 1) c ≤ (|Y| - 3) q y + 2 ∑ q`. -/
theorem sum_ge_of_pairs (q : ℕ → ℤ) {Y : Finset ℕ} {y : ℕ} (hy : y ∈ Y) {c : ℤ}
    (h : ∀ y' ∈ Y.erase y, c ≤ q y + 2 * q y') :
    ((Y.card : ℤ) - 1) * c ≤ ((Y.card : ℤ) - 3) * q y + 2 * ∑ y' ∈ Y, q y' := by
  rw [← sum_pair_eq q hy]
  have := Finset.sum_le_sum h
  rw [Finset.sum_const, Finset.card_erase_of_mem hy, nsmul_eq_mul] at this
  have hpos : 1 ≤ Y.card := Finset.card_pos.mpr ⟨y, hy⟩
  push_cast [Nat.cast_sub hpos] at this
  exact this

section column
variable {X Y Z T M B : Finset ℕ} (hX : NearK 4 X) (hY : NearK 4 Y) (hZ : NearK 4 Z)
  (hT : T.card = 4) (hM : M.card = 4) (hB : B.card = 4)
include hX hY hZ hT hM hB

/-- **The `(H1)` column sum is nonnegative.** -/
theorem colH_four : 0 ≤ ∑ y ∈ Y, QH 4 X Z T M B y := by
  by_cases hall : ∀ y ∈ Y, 0 ≤ QH 4 X Z T M B y
  · exact Finset.sum_nonneg hall
  · push_neg at hall
    obtain ⟨y, hy, hneg⟩ := hall
    have hirr := irregular_of_negH hX hZ hT hM hB hneg
    have hp : ∀ y' ∈ Y.erase y, (0 : ℤ) ≤ QH 4 X Z T M B y + 2 * QH 4 X Z T M B y' :=
      fun y' hy' => (pair_main hX hZ hT hM hB hirr.1 hirr.2 (Finset.ne_of_mem_erase hy').symm).1
    have := sum_ge_of_pairs (QH 4 X Z T M B) hy hp
    rcases card_three_or_four hY with h | h <;> rw [h] at this <;> linarith

/-- At an irregular colour that is not Bad, every pair sum is at least `1`. -/
theorem pairs_irregular_noBad {y : ℕ} (hy : y ∈ Y) (hirr : y ∈ M ∧ ¬ (y ∈ T ∧ y ∈ B))
    (hnb : ¬ (BadU X Z T M B y ∨ BadF X Z T M B y)) :
    ((Y.card : ℤ) - 1) * 1
      ≤ ((Y.card : ℤ) - 3) * QC 4 X Z T M B y + 2 * ∑ y' ∈ Y, QC 4 X Z T M B y' := by
  refine sum_ge_of_pairs _ hy fun y' hy' => ?_
  rcases (pair_main hX hZ hT hM hB hirr.1 hirr.2 (Finset.ne_of_mem_erase hy').symm).2 with
    h | ⟨-, hb, -, -⟩ | ⟨-, hb, -, -⟩
  · exact h
  · exact absurd (Or.inl hb) hnb
  · exact absurd (Or.inr hb) hnb

/-- At any irregular colour, every pair sum is at least `-1`. -/
theorem pairs_irregular_neg {y : ℕ} (hy : y ∈ Y) (hirr : y ∈ M ∧ ¬ (y ∈ T ∧ y ∈ B)) :
    ((Y.card : ℤ) - 1) * (-1)
      ≤ ((Y.card : ℤ) - 3) * QC 4 X Z T M B y + 2 * ∑ y' ∈ Y, QC 4 X Z T M B y' := by
  refine sum_ge_of_pairs _ hy fun y' hy' => ?_
  rcases (pair_main hX hZ hT hM hB hirr.1 hirr.2 (Finset.ne_of_mem_erase hy').symm).2 with
    h | ⟨h, -, -, -⟩ | ⟨h, -, -, -⟩
  · linarith
  · exact h
  · exact h

/-- With no Bad colour, the `(C1_r)` column sum is nonnegative, and at least `1` if some colour
is irregular: for `|Y| = 4` every irregular `y` gives `QC y + 2 ∑ ≥ 3` and every regular `y` gives
`QC y ≥ 0`, so `(1 + 2 |I|) ∑ ≥ 3 |I|`. -/
theorem sum_QC_of_noBad
    (hnb : ∀ y ∈ Y, y ∈ M ∧ ¬ (y ∈ T ∧ y ∈ B) → ¬ (BadU X Z T M B y ∨ BadF X Z T M B y)) :
    0 ≤ ∑ y ∈ Y, QC 4 X Z T M B y ∧
      ((∃ y ∈ Y, y ∈ M ∧ ¬ (y ∈ T ∧ y ∈ B)) → 1 ≤ ∑ y ∈ Y, QC 4 X Z T M B y) := by
  classical
  have hreg : ∀ y ∈ Y, ¬ (y ∈ M ∧ ¬ (y ∈ T ∧ y ∈ B)) → 0 ≤ QC 4 X Z T M B y := fun y _ h =>
    (single_main hX hZ hT hM hB (by unfold Regular; tauto)).2
  rcases card_three_or_four hY with h3 | h4
  · by_cases hex : ∃ y ∈ Y, y ∈ M ∧ ¬ (y ∈ T ∧ y ∈ B)
    · obtain ⟨y, hy, hirr⟩ := hex
      have := pairs_irregular_noBad hX hY hZ hT hM hB hy hirr (hnb y hy hirr)
      rw [h3] at this
      exact ⟨by linarith, fun _ => by linarith⟩
    · have h0 : 0 ≤ ∑ y ∈ Y, QC 4 X Z T M B y :=
        Finset.sum_nonneg fun y hy => hreg y hy fun h => hex ⟨y, hy, h⟩
      exact ⟨h0, fun h => absurd h hex⟩
  · have hIb : ∀ y ∈ Y.filter (fun y => y ∈ M ∧ ¬ (y ∈ T ∧ y ∈ B)),
        3 - 2 * ∑ y' ∈ Y, QC 4 X Z T M B y' ≤ QC 4 X Z T M B y := by
      intro y hy
      obtain ⟨hyY, hirr⟩ := Finset.mem_filter.mp hy
      have := pairs_irregular_noBad hX hY hZ hT hM hB hyY hirr (hnb y hyY hirr)
      rw [h4] at this
      linarith
    have hRb : 0 ≤ ∑ y ∈ Y.filter (fun y => ¬ (y ∈ M ∧ ¬ (y ∈ T ∧ y ∈ B))), QC 4 X Z T M B y :=
      Finset.sum_nonneg fun y hy => hreg y (Finset.mem_filter.mp hy).1 (Finset.mem_filter.mp hy).2
    have hsplit := Finset.sum_filter_add_sum_filter_not Y (fun y => y ∈ M ∧ ¬ (y ∈ T ∧ y ∈ B))
      (QC 4 X Z T M B)
    have hIs := Finset.sum_le_sum hIb
    rw [Finset.sum_const, nsmul_eq_mul] at hIs
    set k : ℤ := ((Y.filter (fun y => y ∈ M ∧ ¬ (y ∈ T ∧ y ∈ B))).card : ℤ) with hk
    set s := ∑ y' ∈ Y, QC 4 X Z T M B y' with hs
    have hk0 : 0 ≤ k := by positivity
    have key : 3 * k ≤ (1 + 2 * k) * s := by linarith
    refine ⟨?_, fun hex => ?_⟩
    · by_contra hneg
      push_neg at hneg
      nlinarith [mul_nonneg hk0 (by linarith : (0 : ℤ) ≤ -1 - s)]
    · obtain ⟨y, hy, hirr⟩ := hex
      have hk1 : (1 : ℤ) ≤ k := by
        rw [hk]
        exact_mod_cast Finset.card_pos.mpr ⟨y, Finset.mem_filter.mpr ⟨hy, hirr⟩⟩
      by_contra hneg
      push_neg at hneg
      nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ k - 1) (by linarith : (0 : ℤ) ≤ -s)]

/-- **The `(C1_r)` column sum is at least `-1`.** -/
theorem colC_neg : -1 ≤ ∑ y ∈ Y, QC 4 X Z T M B y := by
  classical
  by_cases hbad : ∃ y₀ ∈ Y, y₀ ∈ M ∧ ¬ (y₀ ∈ T ∧ y₀ ∈ B) ∧ (BadU X Z T M B y₀ ∨ BadF X Z T M B y₀)
  · obtain ⟨y₀, hy₀, hM₀, hirr₀, hb₀⟩ := hbad
    -- `y₀` is the only irregular colour, so every other colour has a nonnegative term
    have hreg : ∀ y ∈ Y.erase y₀, 0 ≤ QC 4 X Z T M B y := by
      intro y hy
      refine (single_main hX hZ hT hM hB ?_).2
      by_contra hr
      have hirr : y ∈ M ∧ ¬ (y ∈ T ∧ y ∈ B) := by unfold Regular at hr; tauto
      exact irregular_unique hX hZ hT hM hB hirr hb₀ (Finset.ne_of_mem_erase hy)
    have hp := pairs_irregular_neg hX hY hZ hT hM hB hy₀ ⟨hM₀, hirr₀⟩
    have hsum : ∑ y ∈ Y, QC 4 X Z T M B y
        = QC 4 X Z T M B y₀ + ∑ y ∈ Y.erase y₀, QC 4 X Z T M B y :=
      (Finset.add_sum_erase Y _ hy₀).symm
    have hR := Finset.sum_nonneg hreg
    rcases card_three_or_four hY with h | h <;> rw [h] at hp <;> linarith
  · have hnb : ∀ y ∈ Y, y ∈ M ∧ ¬ (y ∈ T ∧ y ∈ B) → ¬ (BadU X Z T M B y ∨ BadF X Z T M B y) :=
      fun y hy hirr hb => hbad ⟨y, hy, hirr.1, hirr.2, hb⟩
    have := (sum_QC_of_noBad hX hY hZ hT hM hB hnb).1
    linarith

/-- **The `(C1_r)` column sum is nonnegative unless the column is Bad.** -/
theorem colC_or : 0 ≤ ∑ y ∈ Y, QC 4 X Z T M B y ∨ BadCol X Y Z T M B := by
  classical
  by_cases hbad : ∃ y₀ ∈ Y, y₀ ∈ M ∧ ¬ (y₀ ∈ T ∧ y₀ ∈ B) ∧ (BadU X Z T M B y₀ ∨ BadF X Z T M B y₀)
  · exact Or.inr hbad
  · have hnb : ∀ y ∈ Y, y ∈ M ∧ ¬ (y ∈ T ∧ y ∈ B) → ¬ (BadU X Z T M B y ∨ BadF X Z T M B y) :=
      fun y hy hirr hb => hbad ⟨y, hy, hirr.1, hirr.2, hb⟩
    exact Or.inl (sum_QC_of_noBad hX hY hZ hT hM hB hnb).1

/-- **If some irregular colour is not Bad, the `(C1_r)` column sum is at least `1`.** -/
theorem colC_gap {y₀ : ℕ} (hy₀ : y₀ ∈ Y) (hM₀ : y₀ ∈ M) (hirr₀ : ¬ (y₀ ∈ T ∧ y₀ ∈ B))
    (hnb₀ : ¬ (BadU X Z T M B y₀ ∨ BadF X Z T M B y₀)) : 1 ≤ ∑ y ∈ Y, QC 4 X Z T M B y := by
  have hnb : ∀ y ∈ Y, y ∈ M ∧ ¬ (y ∈ T ∧ y ∈ B) → ¬ (BadU X Z T M B y ∨ BadF X Z T M B y) := by
    intro y hy hirr hb
    by_cases hne : y₀ = y
    · subst hne; exact hnb₀ hb
    · exact irregular_unique hX hZ hT hM hB ⟨hM₀, hirr₀⟩ hb hne
  exact (sum_QC_of_noBad hX hY hZ hT hM hB hnb).2 ⟨y₀, hy₀, hM₀, hirr₀⟩

end column

end Four
end Grid3
