/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Six.Greedy
import GridGen.Six.Fibre
import GridGen.Five.Local

/-!
# Height six: the count of a column from its interval profile, and row codes

The number of proper colourings of a six-row path is the polynomial `N6z` of
`GridGen/Six/Greedy.lean` in the sizes and interval intersections of the lists
(`card_sts_N6z`, inclusion–exclusion through `card_sts` and the height-five formula). Every real
system satisfies the interval relaxation, so its count is at least the greedy value `N6g`
(`N6g_le_card`, from `greedy_min6`).

**Row codes** (`rcode`, as in `GridGen/Five/K5/State.lean`): `0` if the colour misses its list,
else `1 + [∉ previous] + 2 [∉ next]`. The consecutive intersections of the punctured lists are
`4 - μⱼ + hⱼ₋₁ + xⱼ₋₁⁺ + hⱼ + xⱼ⁻` (`card_inter_rcode`), the lists having `6` colours.
-/

namespace GridGen.Six

open Finset

/-- **The count from the interval profile.** -/
theorem card_sts_N6z (A B C D E F : Finset ℕ) :
    ((sts A B C D E F).card : ℤ) =
      N6z A.card B.card C.card D.card E.card F.card (A ∩ B).card (B ∩ C).card (C ∩ D).card
        (D ∩ E).card (E ∩ F).card (A ∩ B ∩ C).card (B ∩ C ∩ D).card (C ∩ D ∩ E).card
        (D ∩ E ∩ F).card (A ∩ B ∩ C ∩ D).card (B ∩ C ∩ D ∩ E).card (C ∩ D ∩ E ∩ F).card
        (A ∩ B ∩ C ∩ D ∩ E).card (B ∩ C ∩ D ∩ E ∩ F).card (A ∩ B ∩ C ∩ D ∩ E ∩ F).card := by
  rw [card_sts, Five.card_sts_formula, Five.card_sts_formula]
  unfold N6z
  ring

theorem inter3_ge (X Y Z : Finset ℕ) :
    ((X ∩ Y).card : ℤ) + (Y ∩ Z).card - Y.card ≤ (X ∩ Y ∩ Z).card := by
  have h := Lookback.triple_ge X Y Z
  exact_mod_cast h

/-- `|P ∩ Q| ≥ |P| + |Q| - |S|` for `P, Q ⊆ S`. -/
theorem inter_ge_of_sub {P Q S : Finset ℕ} (hP : P ⊆ S) (hQ : Q ⊆ S) :
    (P.card : ℤ) + Q.card - S.card ≤ (P ∩ Q).card := by
  have h := Finset.card_union_add_card_inter P Q
  have hu : (P ∪ Q).card ≤ S.card := Finset.card_le_card (Finset.union_subset hP hQ)
  have : P.card + Q.card ≤ S.card + (P ∩ Q).card := by omega
  have : ((P.card + Q.card : ℕ) : ℤ) ≤ ((S.card + (P ∩ Q).card : ℕ) : ℤ) := by exact_mod_cast this
  push_cast at this
  linarith

/-- **Greedy minimality for actual lists** of at least five colours. -/
theorem N6g_le_card {A₁ A₂ A₃ A₄ A₅ A₆ : Finset ℕ} (h₁ : 5 ≤ A₁.card) (h₂ : 5 ≤ A₂.card)
    (h₃ : 5 ≤ A₃.card) (h₄ : 5 ≤ A₄.card) (h₅ : 5 ≤ A₅.card) (h₆ : 5 ≤ A₆.card) :
    N6g A₁.card A₂.card A₃.card A₄.card A₅.card A₆.card (A₁ ∩ A₂).card (A₂ ∩ A₃).card
      (A₃ ∩ A₄).card (A₄ ∩ A₅).card (A₅ ∩ A₆).card ≤ (sts A₁ A₂ A₃ A₄ A₅ A₆).card := by
  have cl : ∀ {U V : Finset ℕ}, U ⊆ V → (U.card : ℤ) ≤ V.card := fun h => by
    exact_mod_cast Finset.card_le_card h
  have g := greedy_min6 (n1 := A₁.card) (n2 := A₂.card) (n3 := A₃.card) (n4 := A₄.card)
    (n5 := A₅.card) (n6 := A₆.card) (e1 := (A₁ ∩ A₂).card) (e2 := (A₂ ∩ A₃).card)
    (e3 := (A₃ ∩ A₄).card) (e4 := (A₄ ∩ A₅).card) (e5 := (A₅ ∩ A₆).card)
    (t1 := (A₁ ∩ A₂ ∩ A₃).card) (t2 := (A₂ ∩ A₃ ∩ A₄).card) (t3 := (A₃ ∩ A₄ ∩ A₅).card)
    (t4 := (A₄ ∩ A₅ ∩ A₆).card) (q1 := (A₁ ∩ A₂ ∩ A₃ ∩ A₄).card)
    (q2 := (A₂ ∩ A₃ ∩ A₄ ∩ A₅).card) (q3 := (A₃ ∩ A₄ ∩ A₅ ∩ A₆).card)
    (p1 := (A₁ ∩ A₂ ∩ A₃ ∩ A₄ ∩ A₅).card) (p2 := (A₂ ∩ A₃ ∩ A₄ ∩ A₅ ∩ A₆).card)
    (x := (A₁ ∩ A₂ ∩ A₃ ∩ A₄ ∩ A₅ ∩ A₆).card)
    (by exact_mod_cast h₁) (by exact_mod_cast h₂) (by exact_mod_cast h₃) (by exact_mod_cast h₄)
    (by exact_mod_cast h₅) (by exact_mod_cast h₆)
    (cl inter_subset_left) (cl inter_subset_right) (cl inter_subset_left) (cl inter_subset_right)
    (cl inter_subset_left) (cl inter_subset_right)
    (Nat.cast_nonneg _) (inter3_ge _ _ _) (Nat.cast_nonneg _) (inter3_ge _ _ _)
    (Nat.cast_nonneg _) (inter3_ge _ _ _) (Nat.cast_nonneg _) (inter3_ge _ _ _)
    (cl inter_subset_left) (cl (fun x => by simp only [mem_inter]; tauto))
    (cl (fun x => by simp only [mem_inter]; tauto)) (cl (fun x => by simp only [mem_inter]; tauto))
    (cl (fun x => by simp only [mem_inter]; tauto)) (cl (fun x => by simp only [mem_inter]; tauto))
    (Nat.cast_nonneg _)
    (by
      have h := inter_ge_of_sub (P := A₁ ∩ A₂ ∩ A₃ ∩ A₄) (Q := A₂ ∩ A₃ ∩ A₄ ∩ A₅)
        (S := A₂ ∩ A₃ ∩ A₄) (fun x => by simp only [mem_inter]; tauto)
        (fun x => by simp only [mem_inter]; tauto)
      have hi : A₁ ∩ A₂ ∩ A₃ ∩ A₄ ∩ (A₂ ∩ A₃ ∩ A₄ ∩ A₅) = A₁ ∩ A₂ ∩ A₃ ∩ A₄ ∩ A₅ := by
        ext x; simp only [mem_inter]; tauto
      rw [hi] at h; linarith)
    (Nat.cast_nonneg _)
    (by
      have h := inter_ge_of_sub (P := A₂ ∩ A₃ ∩ A₄ ∩ A₅) (Q := A₃ ∩ A₄ ∩ A₅ ∩ A₆)
        (S := A₃ ∩ A₄ ∩ A₅) (fun x => by simp only [mem_inter]; tauto)
        (fun x => by simp only [mem_inter]; tauto)
      have hi : A₂ ∩ A₃ ∩ A₄ ∩ A₅ ∩ (A₃ ∩ A₄ ∩ A₅ ∩ A₆) = A₂ ∩ A₃ ∩ A₄ ∩ A₅ ∩ A₆ := by
        ext x; simp only [mem_inter]; tauto
      rw [hi] at h; linarith)
    (cl (fun x => by simp only [mem_inter]; tauto))
    (cl (fun x => by simp only [mem_inter]; tauto))
  rw [← card_sts_N6z] at g
  exact g

/-! ### Row codes -/

/-- The code of one row: `0` if the colour misses its list, else `1` (in both neighbours' lists),
`2` (not in the previous one), `3` (not in the next one), `4` (in neither). -/
def rcode (Bp Bi Bn : Finset ℕ) (x : ℕ) : ℕ :=
  if x ∈ Bi then (if x ∈ Bp then (if x ∈ Bn then 1 else 3) else (if x ∈ Bn then 2 else 4))
  else 0

def kH (c : ℕ) : ℕ := if c = 0 then 1 else 0
def kM (c : ℕ) : ℕ := if c = 2 ∨ c = 4 then 1 else 0
def kX (c : ℕ) : ℕ := if c = 3 ∨ c = 4 then 1 else 0
def kU (c : ℕ) : ℕ := if c = 2 ∨ c = 3 ∨ c = 4 then 1 else 0

section codes
variable (Bp Bi Bn : Finset ℕ) (x : ℕ)

theorem kH_code : kH (rcode Bp Bi Bn x) = if x ∈ Bi then 0 else 1 := by
  unfold kH rcode; split_ifs <;> simp_all

theorem kM_code : kM (rcode Bp Bi Bn x) = if x ∈ Bi \ Bp then 1 else 0 := by
  unfold kM rcode; simp only [mem_sdiff]; split_ifs <;> simp_all

theorem kX_code : kX (rcode Bp Bi Bn x) = if x ∈ Bi \ Bn then 1 else 0 := by
  unfold kX rcode; simp only [mem_sdiff]; split_ifs <;> simp_all

theorem kU_code : kU (rcode Bp Bi Bn x) = if x ∈ (Bi \ Bp) ∪ (Bi \ Bn) then 1 else 0 := by
  unfold kU rcode; simp only [mem_union, mem_sdiff]; split_ifs <;> simp_all

theorem rcode_le : rcode Bp Bi Bn x ≤ 4 := by
  unfold rcode; split_ifs <;> norm_num

end codes

theorem card_erase_rcode {B : Finset ℕ} (hB : B.card = 6) (Bp Bn : Finset ℕ) (x : ℕ) :
    (B.erase x).card = 5 + kH (rcode Bp B Bn x) := by
  rw [kH_code]
  by_cases h : x ∈ B
  · rw [Finset.card_erase_of_mem h, hB]; simp [h]
  · rw [Finset.erase_eq_of_notMem h, hB]; simp [h]

theorem mu_eq_of6 {B C : Finset ℕ} {m : ℕ} (h : (B ∩ C).card + m = 6) :
    Lookback.mu 6 B C = m := by
  unfold Lookback.mu
  have : ((B ∩ C).card : ℝ) + m = 6 := by exact_mod_cast h
  push_cast; linarith

/-- **The consecutive intersection from the codes.** -/
theorem card_inter_rcode {B C : Finset ℕ} (hB : B.card = 6) (hC : C.card = 6) {m : ℕ}
    (hm : (B ∩ C).card + m = 6) (Bp Cn : Finset ℕ) {x y : ℕ} (hxy : x ≠ y) :
    ((B.erase x) ∩ (C.erase y)).card + m
      = 4 + kH (rcode Bp B C x) + kX (rcode Bp B C x) + kH (rcode B C Cn y)
        + kM (rcode B C Cn y) := by
  have h := Lookback.card_inter_erase hB hC hxy
  rw [mu_eq_of6 hm] at h
  have e1 : Lookback.hb B x = (kH (rcode Bp B C x) : ℝ) := by
    rw [kH_code]; unfold Lookback.hb; split_ifs <;> simp
  have e2 : Lookback.hb C y = (kH (rcode B C Cn y) : ℝ) := by
    rw [kH_code]; unfold Lookback.hb; split_ifs <;> simp
  have e3 : Lookback.zz B C x y = (kX (rcode Bp B C x) : ℝ) + (kM (rcode B C Cn y) : ℝ) := by
    rw [kX_code, kM_code, Lookback.zz_eq]; split_ifs <;> simp
  rw [e1, e2, e3] at h
  push_cast at h
  have : (((B.erase x) ∩ (C.erase y)).card : ℝ) + m
      = ((4 + kH (rcode Bp B C x) + kX (rcode Bp B C x) + kH (rcode B C Cn y)
        + kM (rcode B C Cn y) : ℕ) : ℝ) := by
    push_cast; linarith
  exact_mod_cast this

theorem card_erase56 {B : Finset ℕ} (hB : B.card = 6) (c : ℕ) :
    (B.erase c).card = 5 ∨ (B.erase c).card = 6 := by
  by_cases h : c ∈ B
  · left; rw [Finset.card_erase_of_mem h, hB]
  · right; rw [Finset.erase_eq_of_notMem h, hB]

end GridGen.Six
