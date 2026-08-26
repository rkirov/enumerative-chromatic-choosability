/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Grid3.Four.Bounds

/-!
# Venn atoms of five lists

The `k = 4` arithmetic (`Grid3.Four.Arith`) is phrased in the numbers of colours of each
membership type in the five lists `X, Z, T, M, B` (the two punctured lists, then the next
column), excluding the marked colours. This file defines the type of a colour, the atoms, and
proves the one decomposition lemma: the size of any region cut out by a predicate on the type is
the sum of its atoms plus the marked colours it contains.
-/

open Finset

namespace Grid3
namespace Four

/-- The membership type of a colour, as a number below `32`: bit `1` for `X`, `2` for `Z`, `4`
for `T`, `8` for `M`, `16` for `B`. -/
def typ (X Z T M B : Finset ℕ) (c : ℕ) : ℕ :=
  (if c ∈ X then 1 else 0) + (if c ∈ Z then 2 else 0) + (if c ∈ T then 4 else 0)
    + (if c ∈ M then 8 else 0) + (if c ∈ B then 16 else 0)

/-- Bit `i` of `v`. -/
def bit (v i : ℕ) : Prop := v / 2 ^ i % 2 = 1

instance (v i : ℕ) : Decidable (bit v i) := by unfold bit; infer_instance

theorem typ_lt (X Z T M B : Finset ℕ) (c : ℕ) : typ X Z T M B c < 32 := by
  unfold typ; split_ifs <;> norm_num

theorem bit_typ_X (X Z T M B : Finset ℕ) (c : ℕ) : bit (typ X Z T M B c) 0 ↔ c ∈ X := by
  unfold typ bit; split_ifs <;> simp_all
theorem bit_typ_Z (X Z T M B : Finset ℕ) (c : ℕ) : bit (typ X Z T M B c) 1 ↔ c ∈ Z := by
  unfold typ bit; split_ifs <;> simp_all
theorem bit_typ_T (X Z T M B : Finset ℕ) (c : ℕ) : bit (typ X Z T M B c) 2 ↔ c ∈ T := by
  unfold typ bit; split_ifs <;> simp_all
theorem bit_typ_M (X Z T M B : Finset ℕ) (c : ℕ) : bit (typ X Z T M B c) 3 ↔ c ∈ M := by
  unfold typ bit; split_ifs <;> simp_all
theorem bit_typ_B (X Z T M B : Finset ℕ) (c : ℕ) : bit (typ X Z T M B c) 4 ↔ c ∈ B := by
  unfold typ bit; split_ifs <;> simp_all

/-- All colours of the five lists. -/
def univ5 (X Z T M B : Finset ℕ) : Finset ℕ := X ∪ Z ∪ T ∪ M ∪ B

/-- The atom of type `v`: the colours of that type outside the marked set `E`. -/
def atom (X Z T M B E : Finset ℕ) (v : ℕ) : ℤ :=
  (((univ5 X Z T M B) \ E).filter (fun c => typ X Z T M B c = v)).card

theorem atom_nonneg (X Z T M B E : Finset ℕ) (v : ℕ) : 0 ≤ atom X Z T M B E v := by
  unfold atom; positivity

/-- **The decomposition lemma.** A region cut out by a predicate `P` on the type. -/
theorem card_region (X Z T M B : Finset ℕ) (P : ℕ → Prop) [DecidablePred P] (R E : Finset ℕ)
    (hR : ∀ c, c ∈ R ↔ c ∈ univ5 X Z T M B ∧ P (typ X Z T M B c)) :
    (R.card : ℤ) = ∑ v ∈ (Finset.range 32).filter P, atom X Z T M B E v + ((R ∩ E).card : ℤ) := by
  classical
  have hdisj : Disjoint (R \ E) (R ∩ E) := Finset.disjoint_sdiff_inter R E
  have hcard : R.card = (R \ E).card + (R ∩ E).card := by
    rw [← Finset.card_union_of_disjoint hdisj, Finset.sdiff_union_inter]
  rw [hcard]
  push_cast
  congr 1
  rw [Finset.card_eq_sum_card_fiberwise (f := typ X Z T M B) (t := (Finset.range 32).filter P)]
  · push_cast
    refine Finset.sum_congr rfl fun v hv => ?_
    unfold atom
    have hset : ((univ5 X Z T M B) \ E).filter (fun c => typ X Z T M B c = v)
        = (R \ E).filter (fun c => typ X Z T M B c = v) := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_sdiff, hR, Finset.mem_range] at hv ⊢
      constructor
      · rintro ⟨⟨hU, hE⟩, ht⟩; exact ⟨⟨⟨hU, ht ▸ hv.2⟩, hE⟩, ht⟩
      · rintro ⟨⟨⟨hU, _⟩, hE⟩, ht⟩; exact ⟨⟨hU, hE⟩, ht⟩
    rw [hset]
  · intro c hc
    rw [Finset.mem_coe, Finset.mem_sdiff, hR] at hc
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    exact ⟨typ_lt _ _ _ _ _ _, hc.1.2⟩

/-- The marked part of a region, for two distinct marked colours. -/
theorem card_inter_pair (R : Finset ℕ) {y y' : ℕ} (hne : y ≠ y') :
    ((R ∩ {y, y'}).card : ℤ) = ind (y ∈ R) + ind (y' ∈ R) := by
  have : R ∩ {y, y'} = ({y, y'} : Finset ℕ).filter (· ∈ R) := by
    ext c; simp only [Finset.mem_inter, Finset.mem_filter]; tauto
  rw [this, ← sum_ind_filter, Finset.sum_pair hne]

theorem card_inter_single (R : Finset ℕ) (y : ℕ) :
    ((R ∩ {y}).card : ℤ) = ind (y ∈ R) := by
  have : R ∩ {y} = ({y} : Finset ℕ).filter (· ∈ R) := by
    ext c; simp only [Finset.mem_inter, Finset.mem_filter]; tauto
  rw [this, ← sum_ind_filter, Finset.sum_singleton]

/-! ### Membership in the universe -/

theorem mem_univ5_of_X {X Z T M B : Finset ℕ} {c : ℕ} (h : c ∈ X) : c ∈ univ5 X Z T M B := by
  unfold univ5; simp [h]
theorem mem_univ5_of_Z {X Z T M B : Finset ℕ} {c : ℕ} (h : c ∈ Z) : c ∈ univ5 X Z T M B := by
  unfold univ5; simp [h]
theorem mem_univ5_of_T {X Z T M B : Finset ℕ} {c : ℕ} (h : c ∈ T) : c ∈ univ5 X Z T M B := by
  unfold univ5; simp [h]
theorem mem_univ5_of_M {X Z T M B : Finset ℕ} {c : ℕ} (h : c ∈ M) : c ∈ univ5 X Z T M B := by
  unfold univ5; simp [h]
theorem mem_univ5_of_B {X Z T M B : Finset ℕ} {c : ℕ} (h : c ∈ B) : c ∈ univ5 X Z T M B := by
  unfold univ5; simp [h]

end Four
end Grid3
