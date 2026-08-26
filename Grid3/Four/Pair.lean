/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Grid3.Four.Expand
import Grid3.Four.ArithPair

/-!
# The conditional pair lemma at `k = 4`, in set form

For an *irregular* colour `y ∈ M \ (T ∩ B)` and any other colour `y'`, the per-colour terms
satisfy `QC y + 2 QC y' ≥ 1`, except in the two mirror-image *Bad* configurations, where the sum
is still `≥ -1` and the configuration is pinned down (`BadU`, `BadF`). The `(H1)` version holds
without exception.
-/

open Finset

namespace Grid3
namespace Four

/-- The unflipped Bad configuration around an irregular colour `y`: `Z ⊆ T ∩ M` has three
colours, `M \ T` is the single colour `y`, `M ⊆ B`, and some colour of `X` is outside `M`. -/
def BadU (X Z T M B : Finset ℕ) (y : ℕ) : Prop :=
  y ∈ M ∧ y ∉ T ∧ y ∈ B ∧ y ∉ X ∧ y ∉ Z ∧ X.card = 3 ∧ Z.card = 3 ∧ (Z.filter (· ∉ T)).card = 0
    ∧ (Z.filter (· ∉ M)).card = 0 ∧ (M.filter (· ∉ T)).card = 1 ∧ (M.filter (· ∉ B)).card = 0
    ∧ 1 ≤ (X.filter (· ∉ M)).card

/-- The mirror image: top and bottom exchanged. -/
def BadF (X Z T M B : Finset ℕ) (y : ℕ) : Prop :=
  y ∈ M ∧ y ∈ T ∧ y ∉ B ∧ y ∉ X ∧ y ∉ Z ∧ X.card = 3 ∧ Z.card = 3 ∧ (X.filter (· ∉ B)).card = 0
    ∧ (X.filter (· ∉ M)).card = 0 ∧ (M.filter (· ∉ B)).card = 1 ∧ (M.filter (· ∉ T)).card = 0
    ∧ 1 ≤ (Z.filter (· ∉ M)).card

theorem ind_dichot (p : Prop) [Decidable p] : ind p = 0 ∨ ind p = 1 := by
  unfold ind; split_ifs <;> simp
theorem ind_eq_one_iff {p : Prop} [Decidable p] : ind p = 1 ↔ p := by
  unfold ind; split_ifs with h <;> simp [h]
theorem ind_eq_zero_iff {p : Prop} [Decidable p] : ind p = 0 ↔ ¬ p := by
  unfold ind; split_ifs with h <;> simp [h]
theorem ind_mul_le_left (p q : Prop) [Decidable p] [Decidable q] : ind p * ind q ≤ ind p := by
  unfold ind; split_ifs <;> simp
theorem ind_mul_le_right (p q : Prop) [Decidable p] [Decidable q] : ind p * ind q ≤ ind q := by
  unfold ind; split_ifs <;> simp
theorem ind_mul_ge (p q : Prop) [Decidable p] [Decidable q] : ind p + ind q - 1 ≤ ind p * ind q := by
  unfold ind; split_ifs <;> simp
theorem ind_mul_nonneg (p q : Prop) [Decidable p] [Decidable q] : 0 ≤ ind p * ind q := by
  unfold ind; split_ifs <;> simp
theorem ind_mul_le_one (p q : Prop) [Decidable p] [Decidable q] : ind p * ind q ≤ 1 := by
  unfold ind; split_ifs <;> simp

theorem card_filter_notMem_ge_one (M T : Finset ℕ) (y : ℕ) (hyT : y ∉ T) (hyM : y ∈ M) :
    (1 : ℤ) ≤ (M.filter (· ∉ T)).card := by
  have : y ∈ M.filter (· ∉ T) := Finset.mem_filter.mpr ⟨hyM, hyT⟩
  exact_mod_cast Finset.card_pos.mpr ⟨y, this⟩

theorem nearK_card {X : Finset ℕ} (hX : NearK 4 X) : (X.card : ℤ) = 3 ∨ (X.card : ℤ) = 4 := by
  rcases hX with h | h <;> simp [h]

/-- `cc 4 = 14`, so `QC = 14 QH + RC`. -/
theorem QC_four (X Z T M B : Finset ℕ) (y : ℕ) :
    QC 4 X Z T M B y = 14 * QH 4 X Z T M B y + RC 4 X Z T M B y := by
  rw [QC_eq]; norm_num [cc]

/-- **The conditional pair lemma.** -/
theorem pair_main {X Z T M B : Finset ℕ} (hX : NearK 4 X) (hZ : NearK 4 Z) (hT : T.card = 4)
    (hM : M.card = 4) (hB : B.card = 4) {y y' : ℕ} (hyM : y ∈ M) (hirr : ¬ (y ∈ T ∧ y ∈ B))
    (hne : y ≠ y') :
    0 ≤ QH 4 X Z T M B y + 2 * QH 4 X Z T M B y' ∧
    (1 ≤ QC 4 X Z T M B y + 2 * QC 4 X Z T M B y'
      ∨ (-1 ≤ QC 4 X Z T M B y + 2 * QC 4 X Z T M B y' ∧ BadU X Z T M B y ∧ y' ∈ X ∧ y' ∈ M)
      ∨ (-1 ≤ QC 4 X Z T M B y + 2 * QC 4 X Z T M B y' ∧ BadF X Z T M B y ∧ y' ∈ Z ∧ y' ∈ M)) := by
  have hyW : ind (y ∈ T) * ind (y ∈ B) = 0 := by
    rw [← ind_and]; exact ind_eq_zero_iff.mpr hirr
  have hTB : ind (y ∈ T) + ind (y ∈ B) ≤ 1 := by
    have := ind_dichot (y ∈ T); have := ind_dichot (y ∈ B)
    have h3 : ¬ (ind (y ∈ T) = 1 ∧ ind (y ∈ B) = 1) := by
      rintro ⟨h1, h2⟩; exact hirr ⟨ind_eq_one_iff.mp h1, ind_eq_one_iff.mp h2⟩
    omega
  have key := Arith.pair_all (atom X Z T M B {y, y'} 1) (atom X Z T M B {y, y'} 2) (atom X Z T M B {y, y'} 3) (atom X Z T M B {y, y'} 4) (atom X Z T M B {y, y'} 5) (atom X Z T M B {y, y'} 6) (atom X Z T M B {y, y'} 7) (atom X Z T M B {y, y'} 8) (atom X Z T M B {y, y'} 9) (atom X Z T M B {y, y'} 10) (atom X Z T M B {y, y'} 11) (atom X Z T M B {y, y'} 12) (atom X Z T M B {y, y'} 13) (atom X Z T M B {y, y'} 14) (atom X Z T M B {y, y'} 15) (atom X Z T M B {y, y'} 16) (atom X Z T M B {y, y'} 17) (atom X Z T M B {y, y'} 18) (atom X Z T M B {y, y'} 19) (atom X Z T M B {y, y'} 20) (atom X Z T M B {y, y'} 21) (atom X Z T M B {y, y'} 22) (atom X Z T M B {y, y'} 23) (atom X Z T M B {y, y'} 24) (atom X Z T M B {y, y'} 25) (atom X Z T M B {y, y'} 26) (atom X Z T M B {y, y'} 27) (atom X Z T M B {y, y'} 28) (atom X Z T M B {y, y'} 29) (atom X Z T M B {y, y'} 30) (atom X Z T M B {y, y'} 31)
    (X.card : ℤ) (Z.card : ℤ) (ind (y ∈ X)) (ind (y ∈ Z)) (ind (y ∈ T)) (ind (y ∈ M)) (ind (y ∈ B)) (ind (y ∈ T) * ind (y ∈ B)) (ind (y' ∈ X)) (ind (y' ∈ Z)) (ind (y' ∈ T)) (ind (y' ∈ M)) (ind (y' ∈ B)) (ind (y' ∈ T) * ind (y' ∈ B))
    (((X.filter (· ∉ T)).card : ℤ)) (((X.filter (· ∉ M)).card : ℤ)) (((X.filter (· ∉ T ∩ B)).card : ℤ)) (((X.filter (· ∉ T ∩ B ∩ M)).card : ℤ)) (((Z.filter (· ∉ B)).card : ℤ)) (((Z.filter (· ∉ M)).card : ℤ)) (((Z.filter (· ∉ T ∩ B)).card : ℤ)) (((Z.filter (· ∉ T ∩ B ∩ M)).card : ℤ)) (((M.filter (· ∉ T)).card : ℤ)) (((M.filter (· ∉ B)).card : ℤ)) (((M.filter (· ∉ T ∩ B)).card : ℤ)) ((((M.filter (· ∉ T)).filter (· ∈ X)).card : ℤ)) ((((M.filter (· ∉ B)).filter (· ∈ Z)).card : ℤ)) (((X ∩ Z).card : ℤ)) ((((X ∩ Z).filter (· ∉ M)).card : ℤ)) ((((X ∩ Z).filter (· ∈ T ∩ B)).card : ℤ)) ((((X ∩ Z).filter (· ∈ T ∩ B ∩ M)).card : ℤ)) (((T.filter (· ∉ B)).card : ℤ)) (((Z.filter (· ∉ T)).card : ℤ)) (((X.filter (· ∉ B)).card : ℤ))
    (atom_nonneg X Z T M B {y, y'} 1) (atom_nonneg X Z T M B {y, y'} 2) (atom_nonneg X Z T M B {y, y'} 3) (atom_nonneg X Z T M B {y, y'} 4) (atom_nonneg X Z T M B {y, y'} 5) (atom_nonneg X Z T M B {y, y'} 6) (atom_nonneg X Z T M B {y, y'} 7) (atom_nonneg X Z T M B {y, y'} 8) (atom_nonneg X Z T M B {y, y'} 9) (atom_nonneg X Z T M B {y, y'} 10) (atom_nonneg X Z T M B {y, y'} 11) (atom_nonneg X Z T M B {y, y'} 12) (atom_nonneg X Z T M B {y, y'} 13) (atom_nonneg X Z T M B {y, y'} 14) (atom_nonneg X Z T M B {y, y'} 15) (atom_nonneg X Z T M B {y, y'} 16) (atom_nonneg X Z T M B {y, y'} 17) (atom_nonneg X Z T M B {y, y'} 18) (atom_nonneg X Z T M B {y, y'} 19) (atom_nonneg X Z T M B {y, y'} 20) (atom_nonneg X Z T M B {y, y'} 21) (atom_nonneg X Z T M B {y, y'} 22) (atom_nonneg X Z T M B {y, y'} 23) (atom_nonneg X Z T M B {y, y'} 24) (atom_nonneg X Z T M B {y, y'} 25) (atom_nonneg X Z T M B {y, y'} 26) (atom_nonneg X Z T M B {y, y'} 27) (atom_nonneg X Z T M B {y, y'} 28) (atom_nonneg X Z T M B {y, y'} 29) (atom_nonneg X Z T M B {y, y'} 30) (atom_nonneg X Z T M B {y, y'} 31)
    (nearK_card hX) (nearK_card hZ) (ind_dichot _) (ind_dichot _)
    (ind_eq_one_iff.mpr hyM) hyW (ind_dichot _) (ind_dichot _) hTB (ind_dichot _) (ind_dichot _)
    (ind_dichot _) (ind_dichot _) (ind_dichot _) (ind_mul_le_left _ _) (ind_mul_le_right _ _)
    (ind_mul_ge _ _) (ind_mul_nonneg _ _) (ind_mul_le_one _ _)
    (dec_xT X Z T M B hne) (dec_xM X Z T M B hne) (dec_xW X Z T M B hne) (dec_xWM X Z T M B hne) (dec_zB X Z T M B hne) (dec_zM X Z T M B hne) (dec_zW X Z T M B hne) (dec_zWM X Z T M B hne) (dec_mT X Z T M B hne) (dec_mB X Z T M B hne) (dec_mW X Z T M B hne) (dec_mXT X Z T M B hne) (dec_mZB X Z T M B hne) (dec_xz X Z T M B hne) (dec_xzM X Z T M B hne) (dec_xzW X Z T M B hne) (dec_xzWM X Z T M B hne) (dec_om X Z T M B hne) (dec_zT X Z T M B hne) (dec_xB X Z T M B hne)
    (size_X X Z T M B hne) (size_Z X Z T M B hne) (size_T X Z T M B hT hne) (size_M X Z T M B hM hne) (size_B X Z T M B hB hne)
  obtain ⟨kH, kC⟩ := key
  have eC := pair_expand_C X Z T M B hM y y'
  have eH := pair_expand_H X Z T M B hM y y'
  have bH := betaH_le_QH (M := M) hT hB X Z y
  have bH' := betaH_le_QH (M := M) hT hB X Z y'
  have rC := RC_eq_RC4 (M := M) (B := B) hT X Z y
  have rC' := RC_eq_RC4 (M := M) (B := B) hT X Z y'
  have qC := QC_four X Z T M B y
  have qC' := QC_four X Z T M B y'
  refine ⟨by linarith, ?_⟩
  rcases kC with h | ⟨h, hb⟩ | ⟨h, hb⟩
  · left; linarith
  · right; left
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hb
    refine ⟨by linarith, ⟨hyM, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · exact ind_eq_zero_iff.mp h5
    · exact ind_eq_one_iff.mp h6
    · exact ind_eq_zero_iff.mp h3
    · exact ind_eq_zero_iff.mp h4
    · exact_mod_cast h1
    · exact_mod_cast h2
    · have := Nat.cast_nonneg (α := ℤ) (Z.filter (· ∉ T)).card; omega
    · have := Nat.cast_nonneg (α := ℤ) (Z.filter (· ∉ M)).card; omega
    · have := card_filter_notMem_ge_one M T y (ind_eq_zero_iff.mp h5) hyM; omega
    · have := Nat.cast_nonneg (α := ℤ) (M.filter (· ∉ B)).card; omega
    · omega
    · exact ind_eq_one_iff.mp h7
    · exact ind_eq_one_iff.mp h10
  · right; right
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hb
    refine ⟨by linarith, ⟨hyM, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · exact ind_eq_one_iff.mp h5
    · exact ind_eq_zero_iff.mp h6
    · exact ind_eq_zero_iff.mp h3
    · exact ind_eq_zero_iff.mp h4
    · exact_mod_cast h1
    · exact_mod_cast h2
    · have := Nat.cast_nonneg (α := ℤ) (X.filter (· ∉ B)).card; omega
    · have := Nat.cast_nonneg (α := ℤ) (X.filter (· ∉ M)).card; omega
    · have := card_filter_notMem_ge_one M B y (ind_eq_zero_iff.mp h6) hyM; omega
    · have := Nat.cast_nonneg (α := ℤ) (M.filter (· ∉ T)).card; omega
    · omega
    · exact ind_eq_one_iff.mp h8
    · exact ind_eq_one_iff.mp h10

end Four
end Grid3
