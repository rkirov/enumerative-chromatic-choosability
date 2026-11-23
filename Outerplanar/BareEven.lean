/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.Statements
import Outerplanar.TransportFace
import Outerplanar.Square

/-!
# Faces whose path edges are greedy

A face whose path edges all carry `Dominant` profiles ("bare" faces: everything below them is
odd-only). For three colours:

* `dom_face_bare` — the root profile is `Dominant` with the path count `oddB m` of the face,
  which is the constant `α = faceConst3 m` for odd `m` and `α - 1` for even `m`
  (`dom_face_even`);
* `hasPot_face3` — the rank-one class `HasPot` passes through every face of length at least
  four, with the constant `α` (Egerváry, `face_hasPot`);
* `tb_even_long` — an even face of length at least six has the four-cell bound `3/4`, from its
  floor `(α - 1)/α ≥ 10/11`;
* `tb_square` — a **bare square** has the four-cell bound `3/4` (the true value is
  `√(16/27) = 0.7698`, attained). The count of a square at the root colours `(c, e)` is
  `|U'| |V'| - |U' ∩ V'|` with `U' = U ∖ {c}`, `V' = V ∖ {e}` (`bsq_eq`). A count below three
  forces `U ∖ {a} = V ∖ {b}`, and then every proper pair has count at least
  `2 + [c ≠ a] + [e ≠ b]` (`bsq_low`). On a matched six-family this leaves at most one cell
  with count two, and at most two further cells with count three.

Part of the formalization of the six-even-face theorem (proof in
`ai_research_notes/OUTERPLANAR_SIX_EVEN_2026-11-23.md`, by a ChatGPT session; audited and
extended by Claude).
-/

namespace Outerplanar

open Finset

/-! ### Floors -/

theorem faceConst3_zero : faceConst3 0 = 1 := by norm_num [faceConst3]

/-- For an even number of interior vertices the path count is one short of the constant. -/
theorem oddB_even : ∀ k : ℕ, oddB (2 * k) = faceConst3 (2 * k) - 1
  | 0 => by rw [Nat.mul_zero, faceConst3_zero, oddB]; norm_num
  | (k + 1) => by
    have e : 2 * (k + 1) = 2 * k + 2 := by ring
    rw [e, oddB_add_two, oddB_even k, faceConst3_add_two]
    ring

/-- **Floors through a bare face.** A face with greedy profiles on its path edges has a greedy
profile at its root, with the path count `oddB m` times the product of the constants. -/
theorem dom_face_bare {m : ℕ} (Lu Lv : Finset ℕ) (Li : Fin m → Finset ℕ)
    (hLi : ∀ j, (Li j).card = 3) (E : Fin (m + 1) → ℕ → ℕ → ℝ) (hE0 : ∀ j c d, 0 ≤ E j c d)
    (A : Fin (m + 1) → ℝ) (hA : ∀ j, 0 ≤ A j)
    (hE : ∀ j, Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    Dominant Lu Lv (faceSum Li (fun _ _ => 1) E) (oddB m * ∏ j, A j) := by
  intro c hc d hd _
  have h1 := faceSum_ge_bare Lu Lv Li E hE0 A hA hE hc hd
  have h2 : faceSum Li (fun _ _ => 1) (fun _ => neP) c d
      = psum (List.ofFn Li ++ [Lv]) (nes (m + 1)) c d := by
    rw [faceSum_eq_psum Li Lv _ c d hd, List.ofFn_const]
    rfl
  have hcard : ∀ L ∈ List.ofFn Li, L.card = 3 := fun L hL => by
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp hL
    exact hLi i
  have h3 := (path_count (List.ofFn Li) Lv hcard d hd).1 c
  rw [List.length_ofFn] at h3
  calc oddB m * ∏ j, A j = (∏ j, A j) * oddB m := mul_comm _ _
    _ ≤ (∏ j, A j) * faceSum Li (fun _ _ => 1) (fun _ => neP) c d :=
        mul_le_mul_of_nonneg_left (by rw [h2]; exact h3) (Finset.prod_nonneg fun j _ => hA j)
    _ ≤ _ := h1

/-- **Floors through a bare even face**: the constant `α - 1`. -/
theorem dom_face_even {m : ℕ} (hm : Even m) (Lu Lv : Finset ℕ) (Li : Fin m → Finset ℕ)
    (hLi : ∀ j, (Li j).card = 3) (E : Fin (m + 1) → ℕ → ℕ → ℝ) (hE0 : ∀ j c d, 0 ≤ E j c d)
    (A : Fin (m + 1) → ℝ) (hA : ∀ j, 0 ≤ A j)
    (hE : ∀ j, Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    Dominant Lu Lv (faceSum Li (fun _ _ => 1) E) ((faceConst3 m - 1) * ∏ j, A j) := by
  have h := dom_face_bare Lu Lv Li hLi E hE0 A hA hE
  have e : oddB m = faceConst3 m - 1 := by
    obtain ⟨k, hk⟩ := hm
    rw [hk, ← two_mul, oddB_even]
  rwa [e] at h

/-! ### The rank-one class through a face -/

/-- **`HasPot` through a face of length at least four**, with the constant of the face. -/
theorem hasPot_face3 {m : ℕ} (hm : 2 ≤ m) (Lu Lv : Finset ℕ) (Li : Fin m → Finset ℕ)
    (hLu : Lu.card = 3) (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3)
    (E : Fin (m + 1) → ℕ → ℕ → ℝ) (hE0 : ∀ j c d, 0 ≤ E j c d) (A : Fin (m + 1) → ℝ)
    (hA : ∀ j, 0 < A j)
    (hE : ∀ j, HasPot (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    HasPot Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j) := by
  have h := face_hasPot (le_refl 3) (by omega) (cl_three (m + 1) (by omega)) Lu Lv Li hLu hLv
    hLi (fun _ _ => 1) (fun _ _ _ => one_pos) E hE0 A hA hE
  have hg : ∀ j, gmean (Li j) (fun _ => (1 : ℝ)) = 1 := fun j =>
    gmean_eq_one (fun _ _ => one_pos) Finset.prod_const_one
  have e : lam 3 (m + 1) / ((3 : ℕ) : ℝ) * (∏ j, A j) * ∏ j, gmean (Li j) (fun _ => (1 : ℝ))
      = faceConst3 m * ∏ j, A j := by
    simp only [hg, Finset.prod_const_one, mul_one]
    unfold lam faceConst3
    push_cast
    ring
  rwa [e] at h

/-! ### The four-cell bound from a floor -/

/-- Rescaling the constant of the four-cell bound. -/
theorem TB.scale {S T : Finset ℕ} {W : ℕ → ℕ → ℝ} {A f τ : ℝ} (h : TB S T W (f * A) τ) :
    TB S T W A (τ * f ^ 3) := by
  intro p q hm hpq i j k l hij hik hil hjk hjl hkl
  calc (τ * f ^ 3) ^ 2 * A ^ 6 = τ ^ 2 * (f * A) ^ 6 := by ring
    _ ≤ _ := h p q hm hpq i j k l hij hik hil hjk hjl hkl

theorem faceConst3_ge_eleven : ∀ k : ℕ, 11 ≤ faceConst3 (2 * k + 4)
  | 0 => by norm_num [faceConst3]
  | (k + 1) => by
    have e : 2 * (k + 1) + 4 = (2 * k + 4) + 2 := by ring
    rw [e, faceConst3_add_two]
    have h1 := faceConst3_ge_eleven k
    have h2 : (0 : ℝ) ≤ 2 ^ (2 * k + 4 + 1) := by positivity
    linarith

/-- **A bare even face of length at least six** has the four-cell bound `3/4`: its floor is
`(α - 1)/α ≥ 10/11`, and `(10/11)³ ≥ 3/4`. -/
theorem tb_even_long {m : ℕ} (hm : Even m) (hm4 : 4 ≤ m) (Lu Lv : Finset ℕ)
    (Li : Fin m → Finset ℕ) (hLi : ∀ j, (Li j).card = 3) (E : Fin (m + 1) → ℕ → ℕ → ℝ)
    (hE0 : ∀ j c d, 0 ≤ E j c d) (A : Fin (m + 1) → ℝ) (hA : ∀ j, 0 ≤ A j)
    (hE : ∀ j, Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    TB Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j) (3 / 4) := by
  have hα : 11 ≤ faceConst3 m := by
    obtain ⟨k, rfl⟩ := hm
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
    have e : k' + 2 + (k' + 2) = 2 * k' + 4 := by ring
    rw [e]
    exact faceConst3_ge_eleven k'
  have hP : 0 ≤ ∏ j, A j := Finset.prod_nonneg fun j _ => hA j
  have hD := dom_face_even hm Lu Lv Li hLi E hE0 A hA hE
  have e : (faceConst3 m - 1) * ∏ j, A j
      = ((faceConst3 m - 1) / faceConst3 m) * (faceConst3 m * ∏ j, A j) := by
    field_simp
  rw [e] at hD
  have hf0 : 0 ≤ (faceConst3 m - 1) / faceConst3 m := div_nonneg (by linarith) (by linarith)
  have hT := (hD.tb (mul_nonneg hf0 (mul_nonneg (by linarith) hP))).scale
  refine hT.anti (by norm_num) ?_
  have hf : 10 / 11 ≤ (faceConst3 m - 1) / faceConst3 m := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  calc (3 : ℝ) / 4 ≤ (10 / 11) ^ 3 := by norm_num
    _ ≤ ((faceConst3 m - 1) / faceConst3 m) ^ 3 := pow_le_pow_left₀ (by norm_num) hf 3
    _ = 1 * _ := (one_mul _).symm

/-! ### The count of a bare square -/

/-- The number of proper colourings of the two interior vertices of a square with interior
lists `U`, `V` and root colours `c`, `e`. -/
noncomputable def bsq (U V : Finset ℕ) (c e : ℕ) : ℝ :=
  ∑ x ∈ U, ∑ y ∈ V, neP c x * neP x y * neP y e

theorem sum_mul_neP (V : Finset ℕ) (f : ℕ → ℝ) (e : ℕ) :
    ∑ y ∈ V, f y * neP y e = ∑ y ∈ V.erase e, f y := by
  rw [← Finset.filter_ne', Finset.sum_filter]
  refine Finset.sum_congr rfl fun y _ => ?_
  unfold neP
  split_ifs <;> simp

theorem sum_neP_mul (U : Finset ℕ) (f : ℕ → ℝ) (c : ℕ) :
    ∑ x ∈ U, neP c x * f x = ∑ x ∈ U.erase c, f x := by
  rw [← Finset.filter_ne, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold neP
  split_ifs <;> simp

theorem sum_neP_left (V : Finset ℕ) (x : ℕ) :
    ∑ y ∈ V, neP x y = (V.card : ℝ) - if x ∈ V then 1 else 0 := by
  have h : ∀ y, neP x y = 1 - if x = y then 1 else 0 := fun y => by
    unfold neP
    split_ifs <;> simp_all
  simp only [h, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.sum_ite_eq]

/-- **The count of a square**: `|U'| |V'| - |U' ∩ V'|` with `U' = U ∖ {c}`, `V' = V ∖ {e}`. -/
theorem bsq_eq (U V : Finset ℕ) (c e : ℕ) :
    bsq U V c e = ((U.erase c).card : ℝ) * (V.erase e).card - (U.erase c ∩ V.erase e).card := by
  unfold bsq
  simp only [mul_assoc]
  simp_rw [← Finset.mul_sum]
  rw [sum_neP_mul]
  simp_rw [sum_mul_neP, sum_neP_left]
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, Finset.sum_boole,
    Finset.filter_mem_eq_inter]

theorem card_erase_three {U : Finset ℕ} (hU : U.card = 3) {c : ℕ} :
    (c ∈ U → (U.erase c).card = 2) ∧ (c ∉ U → (U.erase c).card = 3) :=
  ⟨fun h => by rw [card_erase_of_mem h, hU], fun h => by rw [erase_eq_of_notMem h, hU]⟩

/-- A square has count at least two everywhere, and at least four when a root colour is not
in the corresponding interior list. -/
theorem bsq_ge {U V : Finset ℕ} (hU : U.card = 3) (hV : V.card = 3) (c e : ℕ) :
    2 ≤ bsq U V c e ∧ (c ∉ U ∨ e ∉ V → 4 ≤ bsq U V c e) := by
  rw [bsq_eq]
  have hw1 : ((U.erase c ∩ V.erase e).card : ℝ) ≤ (U.erase c).card := by
    exact_mod_cast card_le_card inter_subset_left
  have hw2 : ((U.erase c ∩ V.erase e).card : ℝ) ≤ (V.erase e).card := by
    exact_mod_cast card_le_card inter_subset_right
  have hu : (2 : ℝ) ≤ (U.erase c).card := by
    have := pred_card_le_card_erase (s := U) (a := c)
    exact_mod_cast (by omega : 2 ≤ (U.erase c).card)
  have hv : (2 : ℝ) ≤ (V.erase e).card := by
    have := pred_card_le_card_erase (s := V) (a := e)
    exact_mod_cast (by omega : 2 ≤ (V.erase e).card)
  refine ⟨by nlinarith, fun h => ?_⟩
  rcases h with h | h
  · have e3 : ((U.erase c).card : ℝ) = 3 := by exact_mod_cast (card_erase_three hU).2 h
    rw [e3] at hw1 ⊢
    nlinarith
  · have e3 : ((V.erase e).card : ℝ) = 3 := by exact_mod_cast (card_erase_three hV).2 h
    rw [e3] at hw2 ⊢
    nlinarith

/-- **The deficient pair of a square.** If a proper pair `(a, b)` has count below three, then
every proper pair `(c, e)` has count at least `2 + [c ≠ a] + [e ≠ b]`. -/
theorem bsq_low {U V : Finset ℕ} (hU : U.card = 3) (hV : V.card = 3) {a b c e : ℕ}
    (hab : a ≠ b) (h3 : bsq U V a b < 3) (hce : c ≠ e) :
    2 + (if c ≠ a then 1 else 0) + (if e ≠ b then 1 else 0) ≤ bsq U V c e := by
  have haU : a ∈ U := by
    by_contra h
    linarith [(bsq_ge hU hV a b).2 (Or.inl h)]
  have hbV : b ∈ V := by
    by_contra h
    linarith [(bsq_ge hU hV a b).2 (Or.inr h)]
  have hUa := (card_erase_three hU).1 haU
  have hVb := (card_erase_three hV).1 hbV
  -- the common part `D = U ∖ {a} = V ∖ {b}`
  have hD : U.erase a = V.erase b := by
    rw [bsq_eq, hUa, hVb] at h3
    have hw : 2 ≤ (U.erase a ∩ V.erase b).card := by
      have h1 : (1 : ℝ) < (U.erase a ∩ V.erase b).card := by
        push_cast at h3
        linarith
      have h2 : 1 < (U.erase a ∩ V.erase b).card := by exact_mod_cast h1
      omega
    have e1 : U.erase a ∩ V.erase b = U.erase a :=
      eq_of_subset_of_card_le inter_subset_left (by rw [hUa]; exact hw)
    have e2 : U.erase a ∩ V.erase b = V.erase b :=
      eq_of_subset_of_card_le inter_subset_right (by rw [hVb]; exact hw)
    rw [← e1, e2]
  by_cases hcU : c ∈ U
  swap
  · have := (bsq_ge hU hV c e).2 (Or.inl hcU)
    split_ifs <;> linarith
  by_cases heV : e ∈ V
  swap
  · have := (bsq_ge hU hV c e).2 (Or.inr heV)
    split_ifs <;> linarith
  have hUc := (card_erase_three hU).1 hcU
  have hVe := (card_erase_three hV).1 heV
  rw [bsq_eq, hUc, hVe]
  suffices hw : ((U.erase c ∩ V.erase e).card : ℝ)
      ≤ 2 - (if c ≠ a then 1 else 0) - (if e ≠ b then 1 else 0) by
    push_cast
    linarith
  by_cases hca : c = a <;> by_cases heb : e = b
  · -- the deficient pair itself
    subst hca heb
    have := card_le_card (inter_subset_left (s₁ := U.erase c) (s₂ := V.erase e))
    rw [hUc] at this
    simp only [ne_eq, not_true_eq_false, ite_false, sub_zero]
    exact_mod_cast this
  · -- `c = a`, `e ∈ D`
    subst hca
    have heD : e ∈ U.erase c := by rw [hD]; exact mem_erase.mpr ⟨heb, heV⟩
    have hsub : U.erase c ∩ V.erase e ⊆ (U.erase c).erase e := fun x hx =>
      mem_erase.mpr ⟨(mem_erase.mp (mem_inter.mp hx).2).1, (mem_inter.mp hx).1⟩
    have := card_le_card hsub
    rw [card_erase_of_mem heD, hUc] at this
    simp only [ne_eq, not_true_eq_false, ite_false, heb, not_false_eq_true, ite_true]
    have h1 : ((U.erase c ∩ V.erase e).card : ℝ) ≤ 1 := by exact_mod_cast this
    linarith
  · -- `e = b`, `c ∈ D`
    subst heb
    have hcD : c ∈ V.erase e := by rw [← hD]; exact mem_erase.mpr ⟨hca, hcU⟩
    have hsub : U.erase c ∩ V.erase e ⊆ (V.erase e).erase c := fun x hx =>
      mem_erase.mpr ⟨(mem_erase.mp (mem_inter.mp hx).1).1, (mem_inter.mp hx).2⟩
    have := card_le_card hsub
    rw [card_erase_of_mem hcD, hVe] at this
    simp only [ne_eq, not_true_eq_false, ite_false, hca, not_false_eq_true, ite_true]
    have h1 : ((U.erase c ∩ V.erase e).card : ℝ) ≤ 1 := by exact_mod_cast this
    linarith
  · -- `c, e ∈ D` distinct: the two remaining sets are disjoint
    have hempty : U.erase c ∩ V.erase e = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro x hx
      obtain ⟨hxU', hxV'⟩ := mem_inter.mp hx
      obtain ⟨hxc, hxU⟩ := mem_erase.mp hxU'
      obtain ⟨hxe, hxV⟩ := mem_erase.mp hxV'
      by_cases hxa : x = a
      · subst hxa
        have : x ∈ U.erase x := by rw [hD]; exact mem_erase.mpr ⟨hab, hxV⟩
        exact (mem_erase.mp this).1 rfl
      · have hcD : c ∈ U.erase a := mem_erase.mpr ⟨hca, hcU⟩
        have heD : e ∈ U.erase a := by rw [hD]; exact mem_erase.mpr ⟨heb, heV⟩
        have hxD : x ∈ U.erase a := mem_erase.mpr ⟨hxa, hxU⟩
        have hsub : ({x, c, e} : Finset ℕ) ⊆ U.erase a := by
          intro y hy
          simp only [mem_insert, mem_singleton] at hy
          rcases hy with rfl | rfl | rfl <;> assumption
        have hc3 : ({x, c, e} : Finset ℕ).card = 3 := by
          rw [card_insert_of_notMem (by simp [hxc, hxe]), card_pair hce]
        have := card_le_card hsub
        rw [hc3, hUa] at this
        omega
    rw [hempty]
    simp [hca, heb]
    norm_num

/-! ### The four-cell bound of a bare square -/

/-- The lower table of a bare square with deficient pair `(a, b)`, from the two indicators
`[c = a]`, `[e = b]`. -/
def lv : Bool → Bool → ℕ
  | true, true => 2
  | true, false => 3
  | false, true => 3
  | false, false => 4

theorem lv_cast (c a e b : ℕ) : (lv (decide (c = a)) (decide (e = b)) : ℝ)
    = 2 + (if c ≠ a then 1 else 0) + (if e ≠ b then 1 else 0) := by
  by_cases h1 : c = a <;> by_cases h2 : e = b <;> simp [lv, h1, h2] <;> norm_num

/-- The finite core: four cells, at most two in the row of the deficient pair, at most two in
its column, and at most one equal to it. -/
theorem four_bits : ∀ r₀ r₁ r₂ r₃ s₀ s₁ s₂ s₃ : Bool,
    (r₀ && r₁ && r₂) = false → (r₀ && r₁ && r₃) = false → (r₀ && r₂ && r₃) = false →
    (r₁ && r₂ && r₃) = false →
    (s₀ && s₁ && s₂) = false → (s₀ && s₁ && s₃) = false → (s₀ && s₂ && s₃) = false →
    (s₁ && s₂ && s₃) = false →
    (r₀ && s₀ && (r₁ && s₁)) = false → (r₀ && s₀ && (r₂ && s₂)) = false →
    (r₀ && s₀ && (r₃ && s₃)) = false → (r₁ && s₁ && (r₂ && s₂)) = false →
    (r₁ && s₁ && (r₃ && s₃)) = false → (r₂ && s₂ && (r₃ && s₃)) = false →
    432 ≤ lv r₀ s₀ ^ 2 * lv r₁ s₁ ^ 2 * lv r₂ s₂ * lv r₃ s₃ := by
  decide

theorem bool_three {x y z : Prop} [Decidable x] [Decidable y] [Decidable z]
    (h : x → y → z → False) : (decide x && decide y && decide z) = false := by
  by_cases hx : x <;> by_cases hy : y <;> by_cases hz : z <;> simp_all

theorem bool_four {x y z w : Prop} [Decidable x] [Decidable y] [Decidable z] [Decidable w]
    (h : x → y → z → w → False) :
    (decide x && decide y && (decide z && decide w)) = false := by
  by_cases hx : x <;> by_cases hy : y <;> by_cases hz : z <;> by_cases hw : w <;> simp_all

theorem offPair_three_fst : ∀ j₁ j₂ j₃ : Fin 6, j₁ ≠ j₂ → j₁ ≠ j₃ → j₂ ≠ j₃ →
    (offPair j₁).1 = (offPair j₂).1 → (offPair j₁).1 = (offPair j₃).1 → False := by
  decide

/-- **A colour is used by at most two of the six colourings.** -/
theorem Matched.no_three {Lu Lw : Finset ℕ} {p q : Fin 6 → ℕ} (h : Matched Lu Lw p q)
    {i j k : Fin 6} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (h1 : p i = p j)
    (h2 : p i = p k) : False := by
  obtain ⟨α, β, hα, hβ, -, -, hab⟩ := h
  obtain ⟨κ, hκb, hκ⟩ := matched_reindex hα hβ hab
  obtain ⟨i', rfl⟩ := hκb.2 i
  obtain ⟨j', rfl⟩ := hκb.2 j
  obtain ⟨k', rfl⟩ := hκb.2 k
  rw [(hκ i').1, (hκ j').1] at h1
  rw [(hκ i').1, (hκ k').1] at h2
  exact offPair_three_fst i' j' k' (fun e => hij (by rw [e])) (fun e => hik (by rw [e]))
    (fun e => hjk (by rw [e])) (hα h1) (hα h2)

/-- **The bare square has the four-cell bound `3/4`.** -/
theorem tb_square (Lu Lv : Finset ℕ) (Li : Fin 2 → Finset ℕ) (hLi : ∀ j, (Li j).card = 3)
    (E : Fin 3 → ℕ → ℕ → ℝ) (hE0 : ∀ j c d, 0 ≤ E j c d) (A : Fin 3 → ℝ) (hA : ∀ j, 0 ≤ A j)
    (hE : ∀ j, Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    TB Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 2 * ∏ j, A j) (3 / 4) := by
  have hP0 : 0 ≤ ∏ j, A j := Finset.prod_nonneg fun j _ => hA j
  have h3 : faceConst3 2 = 3 := by norm_num [faceConst3]
  rw [h3]
  have hW : ∀ c ∈ Lu, ∀ d ∈ Lv,
      (∏ j, A j) * bsq (Li 0) (Li 1) c d ≤ faceSum Li (fun _ _ => 1) E c d := by
    intro c hc d hd
    have := faceSum_ge_bare Lu Lv Li E hE0 A hA hE hc hd
    rw [faceSum_two Li (fun _ => neP)] at this
    exact this
  intro p q hm hpq i j k l hij hik hil hjk hjl hkl
  have hB0 : ∀ t, 0 ≤ bsq (Li 0) (Li 1) (p t) (q t) := fun t =>
    le_trans (by norm_num) (bsq_ge (hLi 0) (hLi 1) _ _).1
  have hWB : ∀ t, (∏ j, A j) * bsq (Li 0) (Li 1) (p t) (q t)
      ≤ faceSum Li (fun _ _ => 1) E (p t) (q t) := fun t =>
    hW _ (hm.mem t).1 _ (hm.mem t).2
  have key : (432 : ℝ) ≤ bsq (Li 0) (Li 1) (p i) (q i) ^ 2 * bsq (Li 0) (Li 1) (p j) (q j) ^ 2
      * bsq (Li 0) (Li 1) (p k) (q k) * bsq (Li 0) (Li 1) (p l) (q l) := by
    by_cases hall : ∀ t, 3 ≤ bsq (Li 0) (Li 1) (p t) (q t)
    · have := four_le (by norm_num) (by norm_num) (by norm_num) (by norm_num) (hall i) (hall j)
        (hall k) (hall l)
      linarith
    · simp only [not_forall, not_le] at hall
      obtain ⟨t₀, ht₀⟩ := hall
      have hlow : ∀ t, (lv (decide (p t = p t₀)) (decide (q t = q t₀)) : ℝ)
          ≤ bsq (Li 0) (Li 1) (p t) (q t) := fun t => by
        rw [lv_cast]
        exact bsq_low (hLi 0) (hLi 1) (hpq t₀) ht₀ (hpq t)
      refine le_trans ?_ (four_le (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        (Nat.cast_nonneg _) (hlow i) (hlow j) (hlow k) (hlow l))
      have hr : ∀ {x y z : Fin 6}, x ≠ y → x ≠ z → y ≠ z →
          (decide (p x = p t₀) && decide (p y = p t₀) && decide (p z = p t₀)) = false :=
        fun hxy hxz hyz => bool_three fun h1 h2 h3 =>
          hm.no_three hxy hxz hyz (h1.trans h2.symm) (h1.trans h3.symm)
      have hs : ∀ {x y z : Fin 6}, x ≠ y → x ≠ z → y ≠ z →
          (decide (q x = q t₀) && decide (q y = q t₀) && decide (q z = q t₀)) = false :=
        fun hxy hxz hyz => bool_three fun h1 h2 h3 =>
          hm.symm.no_three hxy hxz hyz (h1.trans h2.symm) (h1.trans h3.symm)
      have hrs : ∀ {x y : Fin 6}, x ≠ y →
          (decide (p x = p t₀) && decide (q x = q t₀)
            && (decide (p y = p t₀) && decide (q y = q t₀))) = false :=
        fun hxy => bool_four fun h1 h2 h3 h4 =>
          hxy (hm.injective (h1.trans h3.symm) (h2.trans h4.symm))
      have hn := four_bits _ _ _ _ _ _ _ _ (hr hij hik hjk) (hr hij hil hjl) (hr hik hil hkl)
        (hr hjk hjl hkl) (hs hij hik hjk) (hs hij hil hjl) (hs hik hil hkl) (hs hjk hjl hkl)
        (hrs hij) (hrs hik) (hrs hil) (hrs hjk) (hrs hjl) (hrs hkl)
      exact_mod_cast hn
  have hP6 : 0 ≤ (∏ j, A j) ^ 6 := pow_nonneg hP0 6
  calc (3 / 4 : ℝ) ^ 2 * (3 * ∏ j, A j) ^ 6 ≤ 432 * (∏ j, A j) ^ 6 := by nlinarith
    _ ≤ (∏ j, A j) ^ 6 * (bsq (Li 0) (Li 1) (p i) (q i) ^ 2
          * bsq (Li 0) (Li 1) (p j) (q j) ^ 2 * bsq (Li 0) (Li 1) (p k) (q k)
          * bsq (Li 0) (Li 1) (p l) (q l)) := by nlinarith
    _ = ((∏ j, A j) * bsq (Li 0) (Li 1) (p i) (q i)) ^ 2
          * ((∏ j, A j) * bsq (Li 0) (Li 1) (p j) (q j)) ^ 2
          * ((∏ j, A j) * bsq (Li 0) (Li 1) (p k) (q k))
          * ((∏ j, A j) * bsq (Li 0) (Li 1) (p l) (q l)) := by ring
    _ ≤ _ := four_le (mul_nonneg hP0 (hB0 i)) (mul_nonneg hP0 (hB0 j)) (mul_nonneg hP0 (hB0 k))
        (mul_nonneg hP0 (hB0 l)) (hWB i) (hWB j) (hWB k) (hWB l)

end Outerplanar
