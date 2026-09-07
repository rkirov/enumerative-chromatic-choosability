/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Grid3.Four.ExpandSingle
import Grid3.Four.ArithSingle
import Grid3.Four.Pair

/-!
# Regular colours have nonnegative per-colour terms at `k = 4`, in set form
-/

open Finset

namespace Grid3
namespace Four

/-- A colour is *regular* if it is outside `M`, or in all three of `T, M, B`. -/
def Regular (T M B : Finset ℕ) (y : ℕ) : Prop := y ∉ M ∨ (y ∈ T ∧ y ∈ B)

theorem single_main {X Z T M B : Finset ℕ} (hX : NearK 4 X) (hZ : NearK 4 Z) (hT : T.card = 4)
    (hM : M.card = 4) (hB : B.card = 4) {y : ℕ} (hreg : Regular T M B y) :
    0 ≤ QH 4 X Z T M B y ∧ 0 ≤ QC 4 X Z T M B y := by
  have hreg' : ind (y ∈ M) = 0 ∨ (ind (y ∈ T) = 1 ∧ ind (y ∈ B) = 1) := by
    rcases hreg with h | ⟨h1, h2⟩
    · exact Or.inl (ind_eq_zero_iff.mpr h)
    · exact Or.inr ⟨ind_eq_one_iff.mpr h1, ind_eq_one_iff.mpr h2⟩
  have key := Arith.single_all (atom X Z T M B {y} 1) (atom X Z T M B {y} 2) (atom X Z T M B {y} 3) (atom X Z T M B {y} 4) (atom X Z T M B {y} 5) (atom X Z T M B {y} 6) (atom X Z T M B {y} 7) (atom X Z T M B {y} 8) (atom X Z T M B {y} 9) (atom X Z T M B {y} 10) (atom X Z T M B {y} 11) (atom X Z T M B {y} 12) (atom X Z T M B {y} 13) (atom X Z T M B {y} 14) (atom X Z T M B {y} 15) (atom X Z T M B {y} 16) (atom X Z T M B {y} 17) (atom X Z T M B {y} 18) (atom X Z T M B {y} 19) (atom X Z T M B {y} 20) (atom X Z T M B {y} 21) (atom X Z T M B {y} 22) (atom X Z T M B {y} 23) (atom X Z T M B {y} 24) (atom X Z T M B {y} 25) (atom X Z T M B {y} 26) (atom X Z T M B {y} 27) (atom X Z T M B {y} 28) (atom X Z T M B {y} 29) (atom X Z T M B {y} 30) (atom X Z T M B {y} 31)
    (X.card : ℤ) (Z.card : ℤ) (ind (y ∈ X)) (ind (y ∈ Z)) (ind (y ∈ T)) (ind (y ∈ M)) (ind (y ∈ B)) (ind (y ∈ T) * ind (y ∈ B))
    (((X.filter (· ∉ T)).card : ℤ)) (((X.filter (· ∉ M)).card : ℤ)) (((X.filter (· ∉ T ∩ B)).card : ℤ)) (((X.filter (· ∉ T ∩ B ∩ M)).card : ℤ)) (((Z.filter (· ∉ B)).card : ℤ)) (((Z.filter (· ∉ M)).card : ℤ)) (((Z.filter (· ∉ T ∩ B)).card : ℤ)) (((Z.filter (· ∉ T ∩ B ∩ M)).card : ℤ)) (((M.filter (· ∉ T)).card : ℤ)) (((M.filter (· ∉ B)).card : ℤ)) (((M.filter (· ∉ T ∩ B)).card : ℤ)) ((((M.filter (· ∉ T)).filter (· ∈ X)).card : ℤ)) ((((M.filter (· ∉ B)).filter (· ∈ Z)).card : ℤ)) (((X ∩ Z).card : ℤ)) ((((X ∩ Z).filter (· ∉ M)).card : ℤ)) ((((X ∩ Z).filter (· ∈ T ∩ B)).card : ℤ)) ((((X ∩ Z).filter (· ∈ T ∩ B ∩ M)).card : ℤ)) (((T.filter (· ∉ B)).card : ℤ)) (((Z.filter (· ∉ T)).card : ℤ)) (((X.filter (· ∉ B)).card : ℤ))
    (atom_nonneg X Z T M B {y} 1) (atom_nonneg X Z T M B {y} 2) (atom_nonneg X Z T M B {y} 3) (atom_nonneg X Z T M B {y} 4) (atom_nonneg X Z T M B {y} 5) (atom_nonneg X Z T M B {y} 6) (atom_nonneg X Z T M B {y} 7) (atom_nonneg X Z T M B {y} 8) (atom_nonneg X Z T M B {y} 9) (atom_nonneg X Z T M B {y} 10) (atom_nonneg X Z T M B {y} 11) (atom_nonneg X Z T M B {y} 12) (atom_nonneg X Z T M B {y} 13) (atom_nonneg X Z T M B {y} 14) (atom_nonneg X Z T M B {y} 15) (atom_nonneg X Z T M B {y} 16) (atom_nonneg X Z T M B {y} 17) (atom_nonneg X Z T M B {y} 18) (atom_nonneg X Z T M B {y} 19) (atom_nonneg X Z T M B {y} 20) (atom_nonneg X Z T M B {y} 21) (atom_nonneg X Z T M B {y} 22) (atom_nonneg X Z T M B {y} 23) (atom_nonneg X Z T M B {y} 24) (atom_nonneg X Z T M B {y} 25) (atom_nonneg X Z T M B {y} 26) (atom_nonneg X Z T M B {y} 27) (atom_nonneg X Z T M B {y} 28) (atom_nonneg X Z T M B {y} 29) (atom_nonneg X Z T M B {y} 30) (atom_nonneg X Z T M B {y} 31)
    (nearK_card hX) (nearK_card hZ) (ind_dichot _) (ind_dichot _) (ind_dichot _) (ind_dichot _)
    (ind_dichot _) (ind_mul_le_left _ _) (ind_mul_le_right _ _) (ind_mul_ge _ _) (ind_mul_nonneg _ _)
    (ind_mul_le_one _ _) hreg'
    (sdec_xT X Z T M B y) (sdec_xM X Z T M B y) (sdec_xW X Z T M B y) (sdec_xWM X Z T M B y) (sdec_zB X Z T M B y) (sdec_zM X Z T M B y) (sdec_zW X Z T M B y) (sdec_zWM X Z T M B y) (sdec_mT X Z T M B y) (sdec_mB X Z T M B y) (sdec_mW X Z T M B y) (sdec_mXT X Z T M B y) (sdec_mZB X Z T M B y) (sdec_xz X Z T M B y) (sdec_xzM X Z T M B y) (sdec_xzW X Z T M B y) (sdec_xzWM X Z T M B y) (sdec_om X Z T M B y) (sdec_zT X Z T M B y) (sdec_xB X Z T M B y)
    (ssize_X X Z T M B y) (ssize_Z X Z T M B y) (ssize_T X Z T M B hT y) (ssize_M X Z T M B hM y) (ssize_B X Z T M B hB y)
  obtain ⟨kH, kC⟩ := key
  have eC := single_expand_C X Z T M B hM y
  have eH := single_expand_H X Z T M B hM y
  have bH := betaH_le_QH (M := M) hT hB X Z y
  have rC := RC_eq_RC4 (M := M) (B := B) hT X Z y
  have qC := QC_four X Z T M B y
  exact ⟨by linarith, by linarith⟩

end Four
end Grid3
