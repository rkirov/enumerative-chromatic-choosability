/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Grid3.Four.Regions

/-!
# Punctured quantities in terms of the unpunctured lists

Each cardinality of a punctured list `X \ y` used in `Grid3.Four.Bounds` is the corresponding
unpunctured cardinality minus the indicator of `y`.
-/

open Finset

namespace Grid3
namespace Four

theorem pc_eq (X : Finset ℕ) (y : ℕ) : pc X y = (X.card : ℤ) - ind (y ∈ X) := by
  unfold pc; exact card_erase_int X y

theorem out_eq (X T : Finset ℕ) (y : ℕ) :
    out X T y = ((X.filter (· ∉ T)).card : ℤ) - ind (y ∈ X ∧ y ∉ T) := by
  unfold out
  rw [Finset.filter_erase, card_erase_int]
  congr 1
  unfold ind; simp only [Finset.mem_filter]

theorem erase_inter_erase (X Z : Finset ℕ) (y : ℕ) :
    (X.erase y) ∩ (Z.erase y) = (X ∩ Z).erase y := by
  ext c; simp only [Finset.mem_inter, Finset.mem_erase]; tauto

theorem out2_eq (X Z T : Finset ℕ) (y : ℕ) :
    out2 X Z T y = (((X ∩ Z).filter (· ∉ T)).card : ℤ) - ind (y ∈ X ∧ y ∈ Z ∧ y ∉ T) := by
  unfold out2
  rw [erase_inter_erase, Finset.filter_erase, card_erase_int]
  congr 1
  unfold ind; simp only [Finset.mem_filter, Finset.mem_inter, and_assoc]

theorem in2_eq (X Z W : Finset ℕ) (y : ℕ) :
    in2 X Z W y = (((X ∩ Z).filter (· ∈ W)).card : ℤ) - ind (y ∈ X ∧ y ∈ Z ∧ y ∈ W) := by
  unfold in2
  rw [erase_inter_erase, Finset.filter_erase, card_erase_int]
  congr 1
  unfold ind; simp only [Finset.mem_filter, Finset.mem_inter, and_assoc]

theorem xz_eq (X Z : Finset ℕ) (y : ℕ) :
    (((X.erase y) ∩ (Z.erase y)).card : ℤ) = ((X ∩ Z).card : ℤ) - ind (y ∈ X ∧ y ∈ Z) := by
  rw [erase_inter_erase, card_erase_int]
  congr 1
  unfold ind; simp only [Finset.mem_inter]

theorem outIn_eq (M T X : Finset ℕ) (y : ℕ) :
    outIn M T X y = (((M.filter (· ∉ T)).filter (· ∈ X)).card : ℤ) - ind (y ∈ M ∧ y ∉ T ∧ y ∈ X) := by
  unfold outIn
  have h : ((M.erase y).filter (· ∉ T)).filter (· ∈ X.erase y)
      = ((M.filter (· ∉ T)).filter (· ∈ X)).erase y := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_erase]
    tauto
  rw [h, card_erase_int]
  congr 1
  unfold ind; simp only [Finset.mem_filter, and_assoc]

theorem ind_mem_filter (s : Finset ℕ) (p : ℕ → Prop) [DecidablePred p] (a : ℕ) :
    ind (a ∈ s.filter p) = ind (a ∈ s) * ind (p a) := by
  rw [← ind_and]; unfold ind; simp only [Finset.mem_filter]

theorem ind_mem_inter (s t : Finset ℕ) (a : ℕ) : ind (a ∈ s ∩ t) = ind (a ∈ s) * ind (a ∈ t) := by
  rw [← ind_and]; unfold ind; simp only [Finset.mem_inter]

/-- `ind` of a conjunction with a decided part. -/
theorem ind_and_true {p q : Prop} [Decidable p] [Decidable q] (hq : q) : ind (p ∧ q) = ind p := by
  unfold ind; simp [hq]
theorem ind_and_false {p q : Prop} [Decidable p] [Decidable q] (hq : ¬ q) : ind (p ∧ q) = 0 := by
  unfold ind; simp [hq]

end Four
end Grid3
