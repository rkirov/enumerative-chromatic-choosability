/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Grid3.Four.Punct

/-!
# The per-colour bounds of one colour, in region sizes and indicators

Same as `Grid3.Four.Expand`, for a single marked colour (atoms relative to `{y}`).
-/

open Finset

set_option linter.unusedSimpArgs false

namespace Grid3
namespace Four

theorem single_expand_C (X Z T M B : Finset ℕ) (hM : M.card = 4) (y : ℕ) :
    14 * betaH X Z T M B y + RC4 X Z T M B y = (-2) * ((X ∩ Z).card : ℤ) + (-14) * (((X ∩ Z).filter (· ∉ M)).card : ℤ) + (4) * (((X ∩ Z).filter (· ∈ T ∩ B)).card : ℤ) + (-1) * (((X ∩ Z).filter (· ∈ T ∩ B ∩ M)).card : ℤ) + (57) * (X.card : ℤ) * (Z.card : ℤ) + (-28) * (X.card : ℤ) * (((M.filter (· ∉ B)).filter (· ∈ Z)).card : ℤ) + (112) * (X.card : ℤ) * ((Z.filter (· ∉ B)).card : ℤ) + (-28) * (X.card : ℤ) * ((Z.filter (· ∉ M)).card : ℤ) + (4) * (X.card : ℤ) * ((Z.filter (· ∉ T ∩ B)).card : ℤ) + (-1) * (X.card : ℤ) * ((Z.filter (· ∉ T ∩ B ∩ M)).card : ℤ) + (-144) * (X.card : ℤ) * ind (y ∈ Z) + (-28) * (Z.card : ℤ) * (((M.filter (· ∉ T)).filter (· ∈ X)).card : ℤ) + (-28) * (Z.card : ℤ) * ((X.filter (· ∉ M)).card : ℤ) + (112) * (Z.card : ℤ) * ((X.filter (· ∉ T)).card : ℤ) + (4) * (Z.card : ℤ) * ((X.filter (· ∉ T ∩ B)).card : ℤ) + (-1) * (Z.card : ℤ) * ((X.filter (· ∉ T ∩ B ∩ M)).card : ℤ) + (-144) * (Z.card : ℤ) * ind (y ∈ X) + (28) * (((M.filter (· ∉ T)).filter (· ∈ X)).card : ℤ) * ind (y ∈ Z) + (28) * (((M.filter (· ∉ B)).filter (· ∈ Z)).card : ℤ) * ind (y ∈ X) + (28) * ((X.filter (· ∉ M)).card : ℤ) * ind (y ∈ Z) + (-112) * ((X.filter (· ∉ T)).card : ℤ) * ind (y ∈ Z) + (-4) * ((X.filter (· ∉ T ∩ B)).card : ℤ) * ind (y ∈ Z) + ((X.filter (· ∉ T ∩ B ∩ M)).card : ℤ) * ind (y ∈ Z) + (-1) * (((X ∩ Z).filter (· ∈ T ∩ B)).card : ℤ) * ind (y ∈ M) + (-112) * ((Z.filter (· ∉ B)).card : ℤ) * ind (y ∈ X) + (28) * ((Z.filter (· ∉ M)).card : ℤ) * ind (y ∈ X) + (-4) * ((Z.filter (· ∉ T ∩ B)).card : ℤ) * ind (y ∈ X) + ((Z.filter (· ∉ T ∩ B ∩ M)).card : ℤ) * ind (y ∈ X) + (247) * ind (y ∈ X) * ind (y ∈ Z) + (28) * (X.card : ℤ) * (Z.card : ℤ) * ((M.filter (· ∉ B)).card : ℤ) + (28) * (X.card : ℤ) * (Z.card : ℤ) * ((M.filter (· ∉ T)).card : ℤ) + (X.card : ℤ) * (Z.card : ℤ) * ((M.filter (· ∉ T ∩ B)).card : ℤ) + (-4) * (X.card : ℤ) * (Z.card : ℤ) * ((T.filter (· ∉ B)).card : ℤ) + (-114) * (X.card : ℤ) * (Z.card : ℤ) * ind (y ∈ M) + (-28) * (X.card : ℤ) * ((M.filter (· ∉ B)).card : ℤ) * ind (y ∈ Z) + (-28) * (X.card : ℤ) * ((M.filter (· ∉ T)).card : ℤ) * ind (y ∈ Z) + (-1) * (X.card : ℤ) * ((M.filter (· ∉ T ∩ B)).card : ℤ) * ind (y ∈ Z) + (4) * (X.card : ℤ) * ((T.filter (· ∉ B)).card : ℤ) * ind (y ∈ Z) + (-28) * (X.card : ℤ) * ((Z.filter (· ∉ B)).card : ℤ) * ind (y ∈ M) + (-1) * (X.card : ℤ) * ((Z.filter (· ∉ T ∩ B)).card : ℤ) * ind (y ∈ M) + (112) * (X.card : ℤ) * ind (y ∈ B) * ind (y ∈ Z) + (143) * (X.card : ℤ) * ind (y ∈ M) * ind (y ∈ Z) + (4) * (X.card : ℤ) * (ind (y ∈ T) * ind (y ∈ B)) * ind (y ∈ Z) + (-28) * (Z.card : ℤ) * ((M.filter (· ∉ B)).card : ℤ) * ind (y ∈ X) + (-28) * (Z.card : ℤ) * ((M.filter (· ∉ T)).card : ℤ) * ind (y ∈ X) + (-1) * (Z.card : ℤ) * ((M.filter (· ∉ T ∩ B)).card : ℤ) * ind (y ∈ X) + (4) * (Z.card : ℤ) * ((T.filter (· ∉ B)).card : ℤ) * ind (y ∈ X) + (-28) * (Z.card : ℤ) * ((X.filter (· ∉ T)).card : ℤ) * ind (y ∈ M) + (-1) * (Z.card : ℤ) * ((X.filter (· ∉ T ∩ B)).card : ℤ) * ind (y ∈ M) + (143) * (Z.card : ℤ) * ind (y ∈ M) * ind (y ∈ X) + (112) * (Z.card : ℤ) * ind (y ∈ T) * ind (y ∈ X) + (4) * (Z.card : ℤ) * (ind (y ∈ T) * ind (y ∈ B)) * ind (y ∈ X) + (28) * ((M.filter (· ∉ B)).card : ℤ) * ind (y ∈ X) * ind (y ∈ Z) + (28) * ((M.filter (· ∉ T)).card : ℤ) * ind (y ∈ X) * ind (y ∈ Z) + ((M.filter (· ∉ T ∩ B)).card : ℤ) * ind (y ∈ X) * ind (y ∈ Z) + (-4) * ((T.filter (· ∉ B)).card : ℤ) * ind (y ∈ X) * ind (y ∈ Z) + (28) * ((X.filter (· ∉ T)).card : ℤ) * ind (y ∈ M) * ind (y ∈ Z) + ((X.filter (· ∉ T ∩ B)).card : ℤ) * ind (y ∈ M) * ind (y ∈ Z) + (28) * ((Z.filter (· ∉ B)).card : ℤ) * ind (y ∈ M) * ind (y ∈ X) + ((Z.filter (· ∉ T ∩ B)).card : ℤ) * ind (y ∈ M) * ind (y ∈ X) + (-112) * ind (y ∈ B) * ind (y ∈ X) * ind (y ∈ Z) + (-186) * ind (y ∈ M) * ind (y ∈ X) * ind (y ∈ Z) + (-112) * ind (y ∈ T) * ind (y ∈ X) * ind (y ∈ Z) + (-12) * (ind (y ∈ T) * ind (y ∈ B)) * ind (y ∈ X) * ind (y ∈ Z) + (X.card : ℤ) * (Z.card : ℤ) * ((T.filter (· ∉ B)).card : ℤ) * ind (y ∈ M) + (28) * (X.card : ℤ) * (Z.card : ℤ) * ind (y ∈ B) * ind (y ∈ M) + (28) * (X.card : ℤ) * (Z.card : ℤ) * ind (y ∈ M) * ind (y ∈ T) + (X.card : ℤ) * (Z.card : ℤ) * ind (y ∈ M) * (ind (y ∈ T) * ind (y ∈ B)) + (-1) * (X.card : ℤ) * ((T.filter (· ∉ B)).card : ℤ) * ind (y ∈ M) * ind (y ∈ Z) + (-84) * (X.card : ℤ) * ind (y ∈ B) * ind (y ∈ M) * ind (y ∈ Z) + (-28) * (X.card : ℤ) * ind (y ∈ M) * ind (y ∈ T) * ind (y ∈ Z) + (-3) * (X.card : ℤ) * ind (y ∈ M) * (ind (y ∈ T) * ind (y ∈ B)) * ind (y ∈ Z) + (-1) * (Z.card : ℤ) * ((T.filter (· ∉ B)).card : ℤ) * ind (y ∈ M) * ind (y ∈ X) + (-28) * (Z.card : ℤ) * ind (y ∈ B) * ind (y ∈ M) * ind (y ∈ X) + (-84) * (Z.card : ℤ) * ind (y ∈ M) * ind (y ∈ T) * ind (y ∈ X) + (-3) * (Z.card : ℤ) * ind (y ∈ M) * (ind (y ∈ T) * ind (y ∈ B)) * ind (y ∈ X) + ((T.filter (· ∉ B)).card : ℤ) * ind (y ∈ M) * ind (y ∈ X) * ind (y ∈ Z) + (84) * ind (y ∈ B) * ind (y ∈ M) * ind (y ∈ X) * ind (y ∈ Z) + (84) * ind (y ∈ M) * ind (y ∈ T) * ind (y ∈ X) * ind (y ∈ Z) + (7) * ind (y ∈ M) * (ind (y ∈ T) * ind (y ∈ B)) * ind (y ∈ X) * ind (y ∈ Z) := by
  unfold betaH RC4 om
  simp only [pc_eq, out_eq, out2_eq, in2_eq, xz_eq, outIn_eq, Finset.mem_inter, ind_and, ind_not, hM, Nat.cast_ofNat]
  ring

theorem single_expand_H (X Z T M B : Finset ℕ) (hM : M.card = 4) (y : ℕ) :
    betaH X Z T M B y = (-1) * (((X ∩ Z).filter (· ∉ M)).card : ℤ) + (4) * (X.card : ℤ) * (Z.card : ℤ) + (-2) * (X.card : ℤ) * (((M.filter (· ∉ B)).filter (· ∈ Z)).card : ℤ) + (8) * (X.card : ℤ) * ((Z.filter (· ∉ B)).card : ℤ) + (-2) * (X.card : ℤ) * ((Z.filter (· ∉ M)).card : ℤ) + (-10) * (X.card : ℤ) * ind (y ∈ Z) + (-2) * (Z.card : ℤ) * (((M.filter (· ∉ T)).filter (· ∈ X)).card : ℤ) + (-2) * (Z.card : ℤ) * ((X.filter (· ∉ M)).card : ℤ) + (8) * (Z.card : ℤ) * ((X.filter (· ∉ T)).card : ℤ) + (-10) * (Z.card : ℤ) * ind (y ∈ X) + (2) * (((M.filter (· ∉ T)).filter (· ∈ X)).card : ℤ) * ind (y ∈ Z) + (2) * (((M.filter (· ∉ B)).filter (· ∈ Z)).card : ℤ) * ind (y ∈ X) + (2) * ((X.filter (· ∉ M)).card : ℤ) * ind (y ∈ Z) + (-8) * ((X.filter (· ∉ T)).card : ℤ) * ind (y ∈ Z) + (-8) * ((Z.filter (· ∉ B)).card : ℤ) * ind (y ∈ X) + (2) * ((Z.filter (· ∉ M)).card : ℤ) * ind (y ∈ X) + (17) * ind (y ∈ X) * ind (y ∈ Z) + (2) * (X.card : ℤ) * (Z.card : ℤ) * ((M.filter (· ∉ B)).card : ℤ) + (2) * (X.card : ℤ) * (Z.card : ℤ) * ((M.filter (· ∉ T)).card : ℤ) + (-8) * (X.card : ℤ) * (Z.card : ℤ) * ind (y ∈ M) + (-2) * (X.card : ℤ) * ((M.filter (· ∉ B)).card : ℤ) * ind (y ∈ Z) + (-2) * (X.card : ℤ) * ((M.filter (· ∉ T)).card : ℤ) * ind (y ∈ Z) + (-2) * (X.card : ℤ) * ((Z.filter (· ∉ B)).card : ℤ) * ind (y ∈ M) + (8) * (X.card : ℤ) * ind (y ∈ B) * ind (y ∈ Z) + (10) * (X.card : ℤ) * ind (y ∈ M) * ind (y ∈ Z) + (-2) * (Z.card : ℤ) * ((M.filter (· ∉ B)).card : ℤ) * ind (y ∈ X) + (-2) * (Z.card : ℤ) * ((M.filter (· ∉ T)).card : ℤ) * ind (y ∈ X) + (-2) * (Z.card : ℤ) * ((X.filter (· ∉ T)).card : ℤ) * ind (y ∈ M) + (10) * (Z.card : ℤ) * ind (y ∈ M) * ind (y ∈ X) + (8) * (Z.card : ℤ) * ind (y ∈ T) * ind (y ∈ X) + (2) * ((M.filter (· ∉ B)).card : ℤ) * ind (y ∈ X) * ind (y ∈ Z) + (2) * ((M.filter (· ∉ T)).card : ℤ) * ind (y ∈ X) * ind (y ∈ Z) + (2) * ((X.filter (· ∉ T)).card : ℤ) * ind (y ∈ M) * ind (y ∈ Z) + (2) * ((Z.filter (· ∉ B)).card : ℤ) * ind (y ∈ M) * ind (y ∈ X) + (-8) * ind (y ∈ B) * ind (y ∈ X) * ind (y ∈ Z) + (-13) * ind (y ∈ M) * ind (y ∈ X) * ind (y ∈ Z) + (-8) * ind (y ∈ T) * ind (y ∈ X) * ind (y ∈ Z) + (2) * (X.card : ℤ) * (Z.card : ℤ) * ind (y ∈ B) * ind (y ∈ M) + (2) * (X.card : ℤ) * (Z.card : ℤ) * ind (y ∈ M) * ind (y ∈ T) + (-6) * (X.card : ℤ) * ind (y ∈ B) * ind (y ∈ M) * ind (y ∈ Z) + (-2) * (X.card : ℤ) * ind (y ∈ M) * ind (y ∈ T) * ind (y ∈ Z) + (-2) * (Z.card : ℤ) * ind (y ∈ B) * ind (y ∈ M) * ind (y ∈ X) + (-6) * (Z.card : ℤ) * ind (y ∈ M) * ind (y ∈ T) * ind (y ∈ X) + (6) * ind (y ∈ B) * ind (y ∈ M) * ind (y ∈ X) * ind (y ∈ Z) + (6) * ind (y ∈ M) * ind (y ∈ T) * ind (y ∈ X) * ind (y ∈ Z) := by
  unfold betaH
  simp only [pc_eq, out_eq, out2_eq, outIn_eq, Finset.mem_inter, ind_and, ind_not, hM, Nat.cast_ofNat]
  ring

theorem sdec_xT (X Z T M B : Finset ℕ) (y : ℕ) :
    atom X Z T M B {y} 1 + atom X Z T M B {y} 11 + atom X Z T M B {y} 17 + atom X Z T M B {y} 19 + atom X Z T M B {y} 25 + atom X Z T M B {y} 27 + atom X Z T M B {y} 3 + atom X Z T M B {y} 9 + (-1) * ((X.filter (· ∉ T)).card : ℤ) + ind (y ∈ X) + (-1) * ind (y ∈ T) * ind (y ∈ X) = 0 := by
  have h := card_xT X Z T M B {y}
  rw [card_inter_single] at h
  simp only [ind_mem_filter, ind_mem_inter, ind_not] at h
  linear_combination (-1 : ℤ) * h

theorem sdec_xM (X Z T M B : Finset ℕ) (y : ℕ) :
    atom X Z T M B {y} 1 + atom X Z T M B {y} 17 + atom X Z T M B {y} 19 + atom X Z T M B {y} 21 + atom X Z T M B {y} 23 + atom X Z T M B {y} 3 + atom X Z T M B {y} 5 + atom X Z T M B {y} 7 + (-1) * ((X.filter (· ∉ M)).card : ℤ) + ind (y ∈ X) + (-1) * ind (y ∈ M) * ind (y ∈ X) = 0 := by
  have h := card_xM X Z T M B {y}
  rw [card_inter_single] at h
  simp only [ind_mem_filter, ind_mem_inter, ind_not] at h
  linear_combination (-1 : ℤ) * h

theorem sdec_xW (X Z T M B : Finset ℕ) (y : ℕ) :
    atom X Z T M B {y} 1 + atom X Z T M B {y} 11 + atom X Z T M B {y} 13 + atom X Z T M B {y} 15 + atom X Z T M B {y} 17 + atom X Z T M B {y} 19 + atom X Z T M B {y} 25 + atom X Z T M B {y} 27 + atom X Z T M B {y} 3 + atom X Z T M B {y} 5 + atom X Z T M B {y} 7 + atom X Z T M B {y} 9 + (-1) * ((X.filter (· ∉ T ∩ B)).card : ℤ) + ind (y ∈ X) + (-1) * (ind (y ∈ T) * ind (y ∈ B)) * ind (y ∈ X) = 0 := by
  have h := card_xW X Z T M B {y}
  rw [card_inter_single] at h
  simp only [ind_mem_filter, ind_mem_inter, ind_not] at h
  linear_combination (-1 : ℤ) * h

theorem sdec_xWM (X Z T M B : Finset ℕ) (y : ℕ) :
    atom X Z T M B {y} 1 + atom X Z T M B {y} 11 + atom X Z T M B {y} 13 + atom X Z T M B {y} 15 + atom X Z T M B {y} 17 + atom X Z T M B {y} 19 + atom X Z T M B {y} 21 + atom X Z T M B {y} 23 + atom X Z T M B {y} 25 + atom X Z T M B {y} 27 + atom X Z T M B {y} 3 + atom X Z T M B {y} 5 + atom X Z T M B {y} 7 + atom X Z T M B {y} 9 + (-1) * ((X.filter (· ∉ T ∩ B ∩ M)).card : ℤ) + ind (y ∈ X) + (-1) * ind (y ∈ M) * (ind (y ∈ T) * ind (y ∈ B)) * ind (y ∈ X) = 0 := by
  have h := card_xWM X Z T M B {y}
  rw [card_inter_single] at h
  simp only [ind_mem_filter, ind_mem_inter, ind_not] at h
  linear_combination (-1 : ℤ) * h

theorem sdec_zB (X Z T M B : Finset ℕ) (y : ℕ) :
    atom X Z T M B {y} 10 + atom X Z T M B {y} 11 + atom X Z T M B {y} 14 + atom X Z T M B {y} 15 + atom X Z T M B {y} 2 + atom X Z T M B {y} 3 + atom X Z T M B {y} 6 + atom X Z T M B {y} 7 + (-1) * ((Z.filter (· ∉ B)).card : ℤ) + ind (y ∈ Z) + (-1) * ind (y ∈ B) * ind (y ∈ Z) = 0 := by
  have h := card_zB X Z T M B {y}
  rw [card_inter_single] at h
  simp only [ind_mem_filter, ind_mem_inter, ind_not] at h
  linear_combination (-1 : ℤ) * h

theorem sdec_zM (X Z T M B : Finset ℕ) (y : ℕ) :
    atom X Z T M B {y} 18 + atom X Z T M B {y} 19 + atom X Z T M B {y} 2 + atom X Z T M B {y} 22 + atom X Z T M B {y} 23 + atom X Z T M B {y} 3 + atom X Z T M B {y} 6 + atom X Z T M B {y} 7 + (-1) * ((Z.filter (· ∉ M)).card : ℤ) + ind (y ∈ Z) + (-1) * ind (y ∈ M) * ind (y ∈ Z) = 0 := by
  have h := card_zM X Z T M B {y}
  rw [card_inter_single] at h
  simp only [ind_mem_filter, ind_mem_inter, ind_not] at h
  linear_combination (-1 : ℤ) * h

theorem sdec_zW (X Z T M B : Finset ℕ) (y : ℕ) :
    atom X Z T M B {y} 10 + atom X Z T M B {y} 11 + atom X Z T M B {y} 14 + atom X Z T M B {y} 15 + atom X Z T M B {y} 18 + atom X Z T M B {y} 19 + atom X Z T M B {y} 2 + atom X Z T M B {y} 26 + atom X Z T M B {y} 27 + atom X Z T M B {y} 3 + atom X Z T M B {y} 6 + atom X Z T M B {y} 7 + (-1) * ((Z.filter (· ∉ T ∩ B)).card : ℤ) + ind (y ∈ Z) + (-1) * (ind (y ∈ T) * ind (y ∈ B)) * ind (y ∈ Z) = 0 := by
  have h := card_zW X Z T M B {y}
  rw [card_inter_single] at h
  simp only [ind_mem_filter, ind_mem_inter, ind_not] at h
  linear_combination (-1 : ℤ) * h

theorem sdec_zWM (X Z T M B : Finset ℕ) (y : ℕ) :
    atom X Z T M B {y} 10 + atom X Z T M B {y} 11 + atom X Z T M B {y} 14 + atom X Z T M B {y} 15 + atom X Z T M B {y} 18 + atom X Z T M B {y} 19 + atom X Z T M B {y} 2 + atom X Z T M B {y} 22 + atom X Z T M B {y} 23 + atom X Z T M B {y} 26 + atom X Z T M B {y} 27 + atom X Z T M B {y} 3 + atom X Z T M B {y} 6 + atom X Z T M B {y} 7 + (-1) * ((Z.filter (· ∉ T ∩ B ∩ M)).card : ℤ) + ind (y ∈ Z) + (-1) * ind (y ∈ M) * (ind (y ∈ T) * ind (y ∈ B)) * ind (y ∈ Z) = 0 := by
  have h := card_zWM X Z T M B {y}
  rw [card_inter_single] at h
  simp only [ind_mem_filter, ind_mem_inter, ind_not] at h
  linear_combination (-1 : ℤ) * h

theorem sdec_mT (X Z T M B : Finset ℕ) (y : ℕ) :
    atom X Z T M B {y} 10 + atom X Z T M B {y} 11 + atom X Z T M B {y} 24 + atom X Z T M B {y} 25 + atom X Z T M B {y} 26 + atom X Z T M B {y} 27 + atom X Z T M B {y} 8 + atom X Z T M B {y} 9 + (-1) * ((M.filter (· ∉ T)).card : ℤ) + ind (y ∈ M) + (-1) * ind (y ∈ M) * ind (y ∈ T) = 0 := by
  have h := card_mT X Z T M B {y}
  rw [card_inter_single] at h
  simp only [ind_mem_filter, ind_mem_inter, ind_not] at h
  linear_combination (-1 : ℤ) * h

theorem sdec_mB (X Z T M B : Finset ℕ) (y : ℕ) :
    atom X Z T M B {y} 10 + atom X Z T M B {y} 11 + atom X Z T M B {y} 12 + atom X Z T M B {y} 13 + atom X Z T M B {y} 14 + atom X Z T M B {y} 15 + atom X Z T M B {y} 8 + atom X Z T M B {y} 9 + (-1) * ((M.filter (· ∉ B)).card : ℤ) + ind (y ∈ M) + (-1) * ind (y ∈ B) * ind (y ∈ M) = 0 := by
  have h := card_mB X Z T M B {y}
  rw [card_inter_single] at h
  simp only [ind_mem_filter, ind_mem_inter, ind_not] at h
  linear_combination (-1 : ℤ) * h

theorem sdec_mW (X Z T M B : Finset ℕ) (y : ℕ) :
    atom X Z T M B {y} 10 + atom X Z T M B {y} 11 + atom X Z T M B {y} 12 + atom X Z T M B {y} 13 + atom X Z T M B {y} 14 + atom X Z T M B {y} 15 + atom X Z T M B {y} 24 + atom X Z T M B {y} 25 + atom X Z T M B {y} 26 + atom X Z T M B {y} 27 + atom X Z T M B {y} 8 + atom X Z T M B {y} 9 + (-1) * ((M.filter (· ∉ T ∩ B)).card : ℤ) + ind (y ∈ M) + (-1) * ind (y ∈ M) * (ind (y ∈ T) * ind (y ∈ B)) = 0 := by
  have h := card_mW X Z T M B {y}
  rw [card_inter_single] at h
  simp only [ind_mem_filter, ind_mem_inter, ind_not] at h
  linear_combination (-1 : ℤ) * h

theorem sdec_mXT (X Z T M B : Finset ℕ) (y : ℕ) :
    atom X Z T M B {y} 11 + atom X Z T M B {y} 25 + atom X Z T M B {y} 27 + atom X Z T M B {y} 9 + (-1) * (((M.filter (· ∉ T)).filter (· ∈ X)).card : ℤ) + ind (y ∈ M) * ind (y ∈ X) + (-1) * ind (y ∈ M) * ind (y ∈ T) * ind (y ∈ X) = 0 := by
  have h := card_mXT X Z T M B {y}
  rw [card_inter_single] at h
  simp only [ind_mem_filter, ind_mem_inter, ind_not] at h
  linear_combination (-1 : ℤ) * h

theorem sdec_mZB (X Z T M B : Finset ℕ) (y : ℕ) :
    atom X Z T M B {y} 10 + atom X Z T M B {y} 11 + atom X Z T M B {y} 14 + atom X Z T M B {y} 15 + (-1) * (((M.filter (· ∉ B)).filter (· ∈ Z)).card : ℤ) + ind (y ∈ M) * ind (y ∈ Z) + (-1) * ind (y ∈ B) * ind (y ∈ M) * ind (y ∈ Z) = 0 := by
  have h := card_mZB X Z T M B {y}
  rw [card_inter_single] at h
  simp only [ind_mem_filter, ind_mem_inter, ind_not] at h
  linear_combination (-1 : ℤ) * h

theorem sdec_xz (X Z T M B : Finset ℕ) (y : ℕ) :
    atom X Z T M B {y} 11 + atom X Z T M B {y} 15 + atom X Z T M B {y} 19 + atom X Z T M B {y} 23 + atom X Z T M B {y} 27 + atom X Z T M B {y} 3 + atom X Z T M B {y} 31 + atom X Z T M B {y} 7 + (-1) * ((X ∩ Z).card : ℤ) + ind (y ∈ X) * ind (y ∈ Z) = 0 := by
  have h := card_xz X Z T M B {y}
  rw [card_inter_single] at h
  simp only [ind_mem_filter, ind_mem_inter, ind_not] at h
  linear_combination (-1 : ℤ) * h

theorem sdec_xzM (X Z T M B : Finset ℕ) (y : ℕ) :
    atom X Z T M B {y} 19 + atom X Z T M B {y} 23 + atom X Z T M B {y} 3 + atom X Z T M B {y} 7 + (-1) * (((X ∩ Z).filter (· ∉ M)).card : ℤ) + ind (y ∈ X) * ind (y ∈ Z) + (-1) * ind (y ∈ M) * ind (y ∈ X) * ind (y ∈ Z) = 0 := by
  have h := card_xzM X Z T M B {y}
  rw [card_inter_single] at h
  simp only [ind_mem_filter, ind_mem_inter, ind_not] at h
  linear_combination (-1 : ℤ) * h

theorem sdec_xzW (X Z T M B : Finset ℕ) (y : ℕ) :
    atom X Z T M B {y} 23 + atom X Z T M B {y} 31 + (-1) * (((X ∩ Z).filter (· ∈ T ∩ B)).card : ℤ) + (ind (y ∈ T) * ind (y ∈ B)) * ind (y ∈ X) * ind (y ∈ Z) = 0 := by
  have h := card_xzW X Z T M B {y}
  rw [card_inter_single] at h
  simp only [ind_mem_filter, ind_mem_inter, ind_not] at h
  linear_combination (-1 : ℤ) * h

theorem sdec_xzWM (X Z T M B : Finset ℕ) (y : ℕ) :
    atom X Z T M B {y} 31 + (-1) * (((X ∩ Z).filter (· ∈ T ∩ B ∩ M)).card : ℤ) + ind (y ∈ M) * (ind (y ∈ T) * ind (y ∈ B)) * ind (y ∈ X) * ind (y ∈ Z) = 0 := by
  have h := card_xzWM X Z T M B {y}
  rw [card_inter_single] at h
  simp only [ind_mem_filter, ind_mem_inter, ind_not] at h
  linear_combination (-1 : ℤ) * h

theorem sdec_om (X Z T M B : Finset ℕ) (y : ℕ) :
    atom X Z T M B {y} 12 + atom X Z T M B {y} 13 + atom X Z T M B {y} 14 + atom X Z T M B {y} 15 + atom X Z T M B {y} 4 + atom X Z T M B {y} 5 + atom X Z T M B {y} 6 + atom X Z T M B {y} 7 + (-1) * ((T.filter (· ∉ B)).card : ℤ) + ind (y ∈ T) + (-1) * (ind (y ∈ T) * ind (y ∈ B)) = 0 := by
  have h := card_om X Z T M B {y}
  rw [card_inter_single] at h
  simp only [ind_mem_filter, ind_mem_inter, ind_not] at h
  linear_combination (-1 : ℤ) * h

theorem sdec_zT (X Z T M B : Finset ℕ) (y : ℕ) :
    atom X Z T M B {y} 10 + atom X Z T M B {y} 11 + atom X Z T M B {y} 18 + atom X Z T M B {y} 19 + atom X Z T M B {y} 2 + atom X Z T M B {y} 26 + atom X Z T M B {y} 27 + atom X Z T M B {y} 3 + (-1) * ((Z.filter (· ∉ T)).card : ℤ) + ind (y ∈ Z) + (-1) * ind (y ∈ T) * ind (y ∈ Z) = 0 := by
  have h := card_zT X Z T M B {y}
  rw [card_inter_single] at h
  simp only [ind_mem_filter, ind_mem_inter, ind_not] at h
  linear_combination (-1 : ℤ) * h

theorem sdec_xB (X Z T M B : Finset ℕ) (y : ℕ) :
    atom X Z T M B {y} 1 + atom X Z T M B {y} 11 + atom X Z T M B {y} 13 + atom X Z T M B {y} 15 + atom X Z T M B {y} 3 + atom X Z T M B {y} 5 + atom X Z T M B {y} 7 + atom X Z T M B {y} 9 + (-1) * ((X.filter (· ∉ B)).card : ℤ) + ind (y ∈ X) + (-1) * ind (y ∈ B) * ind (y ∈ X) = 0 := by
  have h := card_xB X Z T M B {y}
  rw [card_inter_single] at h
  simp only [ind_mem_filter, ind_mem_inter, ind_not] at h
  linear_combination (-1 : ℤ) * h

theorem ssize_X (X Z T M B : Finset ℕ) (y : ℕ) :
    atom X Z T M B {y} 1 + atom X Z T M B {y} 11 + atom X Z T M B {y} 13 + atom X Z T M B {y} 15 + atom X Z T M B {y} 17 + atom X Z T M B {y} 19 + atom X Z T M B {y} 21 + atom X Z T M B {y} 23 + atom X Z T M B {y} 25 + atom X Z T M B {y} 27 + atom X Z T M B {y} 29 + atom X Z T M B {y} 3 + atom X Z T M B {y} 31 + atom X Z T M B {y} 5 + atom X Z T M B {y} 7 + atom X Z T M B {y} 9 + (-1) * (X.card : ℤ) + ind (y ∈ X) = 0 := by
  have h := card_nX X Z T M B {y}
  rw [card_inter_single] at h
  linear_combination (-1 : ℤ) * h

theorem ssize_Z (X Z T M B : Finset ℕ) (y : ℕ) :
    atom X Z T M B {y} 10 + atom X Z T M B {y} 11 + atom X Z T M B {y} 14 + atom X Z T M B {y} 15 + atom X Z T M B {y} 18 + atom X Z T M B {y} 19 + atom X Z T M B {y} 2 + atom X Z T M B {y} 22 + atom X Z T M B {y} 23 + atom X Z T M B {y} 26 + atom X Z T M B {y} 27 + atom X Z T M B {y} 3 + atom X Z T M B {y} 30 + atom X Z T M B {y} 31 + atom X Z T M B {y} 6 + atom X Z T M B {y} 7 + (-1) * (Z.card : ℤ) + ind (y ∈ Z) = 0 := by
  have h := card_nZ X Z T M B {y}
  rw [card_inter_single] at h
  linear_combination (-1 : ℤ) * h

theorem ssize_T (X Z T M B : Finset ℕ) (hT : T.card = 4) (y : ℕ) :
    (-4) + atom X Z T M B {y} 12 + atom X Z T M B {y} 13 + atom X Z T M B {y} 14 + atom X Z T M B {y} 15 + atom X Z T M B {y} 20 + atom X Z T M B {y} 21 + atom X Z T M B {y} 22 + atom X Z T M B {y} 23 + atom X Z T M B {y} 28 + atom X Z T M B {y} 29 + atom X Z T M B {y} 30 + atom X Z T M B {y} 31 + atom X Z T M B {y} 4 + atom X Z T M B {y} 5 + atom X Z T M B {y} 6 + atom X Z T M B {y} 7 + ind (y ∈ T) = 0 := by
  have h := card_nT X Z T M B {y}
  rw [card_inter_single] at h
  rw [hT] at h; push_cast at h
  linear_combination (-1 : ℤ) * h

theorem ssize_M (X Z T M B : Finset ℕ) (hM : M.card = 4) (y : ℕ) :
    (-4) + atom X Z T M B {y} 10 + atom X Z T M B {y} 11 + atom X Z T M B {y} 12 + atom X Z T M B {y} 13 + atom X Z T M B {y} 14 + atom X Z T M B {y} 15 + atom X Z T M B {y} 24 + atom X Z T M B {y} 25 + atom X Z T M B {y} 26 + atom X Z T M B {y} 27 + atom X Z T M B {y} 28 + atom X Z T M B {y} 29 + atom X Z T M B {y} 30 + atom X Z T M B {y} 31 + atom X Z T M B {y} 8 + atom X Z T M B {y} 9 + ind (y ∈ M) = 0 := by
  have h := card_nM X Z T M B {y}
  rw [card_inter_single] at h
  rw [hM] at h; push_cast at h
  linear_combination (-1 : ℤ) * h

theorem ssize_B (X Z T M B : Finset ℕ) (hB : B.card = 4) (y : ℕ) :
    (-4) + atom X Z T M B {y} 16 + atom X Z T M B {y} 17 + atom X Z T M B {y} 18 + atom X Z T M B {y} 19 + atom X Z T M B {y} 20 + atom X Z T M B {y} 21 + atom X Z T M B {y} 22 + atom X Z T M B {y} 23 + atom X Z T M B {y} 24 + atom X Z T M B {y} 25 + atom X Z T M B {y} 26 + atom X Z T M B {y} 27 + atom X Z T M B {y} 28 + atom X Z T M B {y} 29 + atom X Z T M B {y} 30 + atom X Z T M B {y} 31 + ind (y ∈ B) = 0 := by
  have h := card_nB X Z T M B {y}
  rw [card_inter_single] at h
  rw [hB] at h; push_cast at h
  linear_combination (-1 : ℤ) * h

end Four
end Grid3
