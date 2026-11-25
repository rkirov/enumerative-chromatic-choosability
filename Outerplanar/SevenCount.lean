/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.SevenEven

/-!
# The seven-even-face face rule from counts

The tags of `Outerplanar/SevenEven.lean` as functions of a number of marks `k` and a flag `sq`
("the mark is a square", which matters only for `k = 1`): `tagN k sq` and `tag7N k sq`. The face
rule `sevenRule` at a face with `m` interior vertices holds for the tag of `k` marks over the
tags of the children's `f i` marks, as soon as

* `k` is the root face's mark (if it is even) plus the children's marks;
* the square flags are consistent (`hsq0`, `hsq1`);
* `k ≤ 4`, or an even root face over three or more marks has children with at most two marks.

This is `rule_of_enum'` and `rule7_of_enum` with the marks of a dissection replaced by arbitrary
counts, so that the marks can include what hangs at the cut vertices of a side
(`Outerplanar/SevenBlocks.lean`). Formalized by Claude.
-/

namespace Outerplanar

open Finset

open Classical in
/-- The numeric tag of `k` marks, `sq` telling whether a single mark is a square. -/
noncomputable def tagN (k : ℕ) (sq : Prop) : NTag :=
  if k = 0 then NTag.plain
  else if k = 1 then (if sq then tSq else tLong)
  else if k = 2 then tTwo else tHex

open Classical in
/-- The tag of `k` marks. -/
noncomputable def tag7N (k : ℕ) (sq : Prop) : STag :=
  ⟨tagN k sq, decide (1 ≤ k ∧ k ≤ 3), decide (k = 1)⟩

section Tags

variable {k : ℕ} {sq : Prop}

theorem tagN_zero (h : k = 0) : tagN k sq = NTag.plain := by
  unfold tagN; simp [h]

open Classical in
theorem tagN_one (h : k = 1) : tagN k sq = (if sq then tSq else tLong) := by
  unfold tagN; simp [h]

theorem tagN_two (h : k = 2) : tagN k sq = tTwo := by
  unfold tagN; simp [h]

theorem tagN_three (h : 3 ≤ k) : tagN k sq = tHex := by
  unfold tagN
  simp [show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega]

theorem tagN_one_mb (h : k = 1) : (tagN k sq).mb = true := by
  classical
  rw [tagN_one h]; split_ifs <;> rfl

theorem tagN_one_tv (h : k = 1) : (tagN k sq).tv = 3 / 4 := by
  classical
  rw [tagN_one h]; split_ifs <;> rfl

theorem tagN_mb (h : k ≤ 2) : (tagN k sq).mb = true := by
  rcases Nat.lt_or_ge k 1 with h0 | h1
  · rw [tagN_zero (by omega)]; rfl
  · rcases (by omega : k = 1 ∨ k = 2) with h1 | h2
    · exact tagN_one_mb h1
    · rw [tagN_two h2]; rfl

theorem tag7N_zero (h : k = 0) : tag7N k sq = STag.plain := by
  unfold tag7N STag.plain
  rw [tagN_zero h]
  simp [h]

theorem tag7N_ball (h1 : 1 ≤ k) (h3 : k ≤ 3) : (tag7N k sq).ball = true := by
  unfold tag7N
  simp [h1, h3]

theorem tag7N_isBall (h3 : k ≤ 3) : (tag7N k sq).isBall := by
  rcases Nat.eq_zero_or_pos k with h | h
  · exact Or.inr (tag7N_zero h)
  · exact Or.inl (tag7N_ball h h3)

theorem tag7N_isGain (h1 : k ≤ 1) : (tag7N k sq).isGain := by
  rcases Nat.eq_zero_or_pos k with h | h
  · exact Or.inr (tag7N_zero h)
  · left
    unfold tag7N
    simp only [decide_eq_true_eq]
    omega

theorem tag7N_ball_le (h : (tag7N k sq).ball = true) : 1 ≤ k ∧ k ≤ 3 := by
  unfold tag7N at h
  simpa using h

theorem tag7N_gain_eq (h : (tag7N k sq).gain = true) : k = 1 := by
  unfold tag7N at h
  simpa using h

end Tags

section Rule

variable {m : ℕ} {k : ℕ} {sq : Prop} {f : Fin (m + 1) → ℕ} {s : Fin (m + 1) → Prop}

/-- **The numeric face rule from counts.** -/
theorem numRule_of_counts (hm1 : 1 ≤ m)
    (hM : k = (if Even (m + 2) then 1 else 0) + ∑ i, f i)
    (hsq0 : Even (m + 2) → (∀ i, f i = 0) → (sq ↔ m = 2))
    (hsq1 : ¬ Even (m + 2) → ∀ j, f j = 1 → (∀ i, i ≠ j → f i = 0) → (sq ↔ s j))
    (hg : 3 ≤ k → Even m → ∀ j, f j ≤ 2) :
    numRule (tagN k sq) m (fun i => tagN (f i) (s i)) := by
  classical
  set τ : Fin (m + 1) → NTag := fun i => tagN (f i) (s i) with hτ
  have hevm : Even (m + 2) ↔ Even m := by
    constructor
    · rintro ⟨k, hk⟩; exact ⟨k - 1, by omega⟩
    · rintro ⟨k, hk⟩; exact ⟨k + 1, by omega⟩
  by_cases h3 : 3 ≤ k
  · rw [tagN_three h3]
    rcases Nat.even_or_odd m with hev | hodd
    · refine numRule_hex_even (by obtain ⟨k, hk⟩ := hev; omega) fun j => ?_
      exact tagN_mb (hg h3 hev j)
    · exact numRule_hex_odd hodd
  have hsum : ∑ i, f i ≤ 2 := by
    have : ∑ i, f i ≤ k := by rw [hM]; split_ifs <;> omega
    omega
  rcases sum_le_two_cases f hsum with h0 | ⟨j, hj, hz⟩ | ⟨j, hj, hz⟩ |
      ⟨j₁, j₂, h12, hj₁, hj₂, hz⟩
  · -- no marks in the children
    have hs : ∑ i, f i = 0 := Finset.sum_eq_zero fun i _ => h0 i
    have hτp : ∀ i, τ i = NTag.plain := fun i => tagN_zero (h0 i)
    by_cases hev : Even (m + 2)
    · have hM1 : k = 1 := by rw [hM]; simp only [hev, ↓reduceIte]; rw [hs]
      rw [tagN_one hM1]
      have hτ' : τ = fun _ => NTag.plain := funext hτp
      have hevm' := hevm.mp hev
      by_cases hm2 : m = 2
      · subst hm2
        simp only [(hsq0 hev h0).mpr rfl, ↓reduceIte]
        rw [hτ']
        exact numRule_bare_square
      · simp only [show ¬ sq from fun h => hm2 ((hsq0 hev h0).mp h),
          ↓reduceIte]
        rw [hτ']
        exact numRule_bare_long hevm' (by obtain ⟨k, hk⟩ := hevm'; omega)
    · have hM0 : k = 0 := by rw [hM]; simp only [hev, ↓reduceIte]; rw [hs]
      rw [tagN_zero hM0]
      have hodd : Odd m := Nat.not_even_iff_odd.mp fun h => hev (hevm.mpr h)
      have := numRule_odd_one (τ := τ) hodd 0 (fun i _ => hτp i)
        (fun _ => Or.inr (by rw [hτp 0]; norm_num [NTag.plain]))
      rwa [hτp 0] at this
  · -- one child with one mark
    have hs : ∑ i, f i = 1 := by
      rw [Finset.sum_eq_single j (fun i _ hi => hz i hi) (fun h => absurd (mem_univ j) h)]
      exact hj
    have hτp : ∀ i, i ≠ j → τ i = NTag.plain := fun i hi => tagN_zero (hz i hi)
    by_cases hev : Even (m + 2)
    · have hM2 : k = 2 := by rw [hM]; simp only [hev, ↓reduceIte]; rw [hs]
      rw [tagN_two hM2]
      have hevm' := hevm.mp hev
      by_cases hm2 : m = 2
      · subst hm2
        by_cases hsq : s j
        · have htj : τ j = tSq := by
            show tagN _ _ = tSq; rw [tagN_one hj, ite_eq_left hsq]
          exact numRule_square_hull j hτp (by rw [htj]; rfl) (by rw [htj]; rfl)
        · have htj : τ j = tLong := by
            show tagN _ _ = tLong; rw [tagN_one hj, ite_eq_right hsq]
          exact numRule_square_long j hτp (by rw [htj]; rfl)
            (by rw [htj]; show (10 / 11 : ℝ) ≤ 10 / 11; exact le_rfl)
      · exact numRule_even_one hevm' (by obtain ⟨k, hk⟩ := hevm'; omega) j hτp
          (tagN_one_mb hj) (by rw [show τ j = tagN _ _ from rfl, tagN_one_tv hj])
    · have hM1 : k = 1 := by rw [hM]; simp only [hev, ↓reduceIte]; rw [hs]
      have hodd : Odd m := Nat.not_even_iff_odd.mp fun h => hev (hevm.mpr h)
      have htag : tagN k sq = τ j := by
        show tagN k sq = tagN (f j) (s j)
        rw [tagN_one hM1, tagN_one hj]
        rw [propext (hsq1 hev j hj hz)]
      rw [htag]
      exact numRule_odd_one hodd j hτp fun _ => Or.inr (by
        rw [show τ j = tagN _ _ from rfl, tagN_one_tv hj]; norm_num)
  · -- one child with two marks
    have hs : ∑ i, f i = 2 := by
      rw [Finset.sum_eq_single j (fun i _ hi => hz i hi) (fun h => absurd (mem_univ j) h)]
      exact hj
    have hτp : ∀ i, i ≠ j → τ i = NTag.plain := fun i hi => tagN_zero (hz i hi)
    have hev : ¬ Even (m + 2) := fun hev => by
      have : k = 3 := by rw [hM]; simp only [hev, ↓reduceIte]; rw [hs]
      omega
    have hM2 : k = 2 := by rw [hM]; simp only [hev, ↓reduceIte]; rw [hs]
    have hodd : Odd m := Nat.not_even_iff_odd.mp fun h => hev (hevm.mpr h)
    have htj : τ j = tTwo := tagN_two hj
    rw [tagN_two hM2, ← htj]
    exact numRule_odd_one hodd j hτp fun _ => Or.inr (by rw [htj]; norm_num [tTwo])
  · -- two children with one mark each
    have hs : ∑ i, f i = 2 := by
      rw [← Finset.add_sum_erase univ f (mem_univ j₁),
        ← Finset.add_sum_erase (univ.erase j₁) f (mem_erase.mpr ⟨ne_of_gt h12, mem_univ j₂⟩)]
      rw [Finset.sum_eq_zero fun i hi => hz i (mem_erase.mp (mem_erase.mp hi).2).1
        (mem_erase.mp hi).1]
      show f j₁ + (f j₂ + 0) = 2
      rw [hj₁, hj₂]
    have hev : ¬ Even (m + 2) := fun hev => by
      have : k = 3 := by rw [hM]; simp only [hev, ↓reduceIte]; rw [hs]
      omega
    have hM2 : k = 2 := by rw [hM]; simp only [hev, ↓reduceIte]; rw [hs]
    have hodd : Odd m := Nat.not_even_iff_odd.mp fun h => hev (hevm.mpr h)
    rw [tagN_two hM2]
    have hv1 : (τ j₁).tv = 3 / 4 := tagN_one_tv hj₁
    have hv2 : (τ j₂).tv = 3 / 4 := tagN_one_tv hj₂
    have hb1 : (τ j₁).mb = true := tagN_one_mb hj₁
    have hb2 : (τ j₂).mb = true := tagN_one_mb hj₂
    rcases Nat.lt_or_ge m 3 with hlt | h3m
    · obtain rfl : m = 1 := by obtain ⟨k, hk⟩ := hodd; omega
      have e1 : j₁ = 0 := by
        have : j₁.val < j₂.val := h12; have := j₂.isLt; exact Fin.ext (by simp; omega)
      have e2 : j₂ = 1 := by
        have : j₁.val < j₂.val := h12; have := j₂.isLt; exact Fin.ext (by simp; omega)
      subst e1 e2
      refine numRule_tri tTwo (fun _ => ⟨hb1, hb2, by rw [hv1, hv2]; norm_num⟩)
        (by rw [hv1, hv2]; norm_num [tTwo]) ?_ rfl
      exact mul_nonneg (τ 0).fl0 (τ 1).fl0
    · exact numRule_odd_two hodd h3m tTwo j₁ j₂ h12 (fun i h1 h2 => tagN_zero (hz i h1 h2))
        (fun _ => ⟨hb1, hb2⟩) (by rw [hv1, hv2]; norm_num [tTwo])
        (mul_nonneg (τ j₁).fl0 (τ j₂).fl0) rfl


/-- **The seven-even-face face rule from counts.** -/
theorem rule7_of_counts (hm1 : 1 ≤ m)
    (hM : k = (if Even (m + 2) then 1 else 0) + ∑ i, f i)
    (hsq0 : Even (m + 2) → (∀ i, f i = 0) → (sq ↔ m = 2))
    (hsq1 : ¬ Even (m + 2) → ∀ j, f j = 1 → (∀ i, i ≠ j → f i = 0) → (sq ↔ s j))
    (hg : k ≤ 4 ∨ (3 ≤ k → Even m → ∀ j, f j ≤ 2)) :
    sevenRule (tag7N k sq) m (fun i => tag7N (f i) (s i)) := by
  classical
  have hevm : Even (m + 2) ↔ Even m := by
    constructor
    · rintro ⟨k, hk⟩; exact ⟨k - 1, by omega⟩
    · rintro ⟨k, hk⟩; exact ⟨k + 1, by omega⟩
  have hle : ∀ j, f j ≤ k := fun j => by
    rw [hM]
    have : f j ≤ ∑ i, f i := Finset.single_le_sum (fun i _ => Nat.zero_le (f i)) (mem_univ j)
    split_ifs <;> omega
  refine ⟨?_, fun hb => ?_, fun hgn => ?_⟩
  · -- the numeric part
    by_cases hloc : 3 ≤ k → Even m → ∀ j : Fin (m + 1), f j ≤ 2
    · exact Or.inl (numRule_of_counts hm1 hM hsq0 hsq1 hloc)
    · right
      push Not at hloc
      obtain ⟨h3, hev, j₀, hj₀⟩ := hloc
      have h4 : k ≤ 4 := by
        rcases hg with h | h
        · exact h
        · have h2 : f j₀ ≤ 2 := h h3 hev j₀
          omega
      have hsum : k = 1 + ∑ i, f i := by
        rw [hM]; simp only [hevm.mpr hev, ↓reduceIte]
      have hsingle : f j₀ ≤ ∑ i, f i :=
        Finset.single_le_sum (fun i _ => Nat.zero_le (f i)) (mem_univ j₀)
      have hrest : ∀ j, j ≠ j₀ → f j = 0 := fun j hj => by
        have : f j₀ + f j ≤ ∑ i, f i :=
          Finset.add_le_sum (fun i _ => Nat.zero_le (f i)) (mem_univ j₀) (mem_univ j) (Ne.symm hj)
        omega
      refine ⟨tagN_three h3, hm1, hev, j₀, tag7N_ball (show 1 ≤ f j₀ by omega)
        (show f j₀ ≤ 3 by omega), fun j hj =>
        tag7N_zero (hrest j hj)⟩
  · -- the ball class
    obtain ⟨hk1, hk3⟩ := tag7N_ball_le hb
    rcases Nat.even_or_odd m with hev | hodd
    · have hsum : ∑ i, f i ≤ 2 := by
        rw [hM] at hk3; simp only [hevm.mpr hev, ↓reduceIte] at hk3; omega
      have hm2 : 2 ≤ m := by obtain ⟨k, hk⟩ := hev; omega
      rcases sum_le_two_cases f hsum with h0 | ⟨j, hj, hz⟩ | ⟨j, hj, hz⟩ |
          ⟨j₁, j₂, -, hj₁, hj₂, hz⟩
      · refine Or.inr (Or.inr ⟨hev, hm2, fun i => tag7N_isGain ?_⟩)
        show f i ≤ 1
        rw [h0 i]; omega
      · refine Or.inr (Or.inr ⟨hev, hm2, fun i => tag7N_isGain ?_⟩)
        show f i ≤ 1
        by_cases hi : i = j
        · rw [hi, hj]
        · rw [hz i hi]; omega
      · exact Or.inr (Or.inl ⟨hev, hm2, j, tag7N_isBall (by show f j ≤ 3; omega), fun i hi =>
          tag7N_zero (hz i hi)⟩)
      · refine Or.inr (Or.inr ⟨hev, hm2, fun i => tag7N_isGain ?_⟩)
        show f i ≤ 1
        by_cases h1 : i = j₁
        · rw [h1, hj₁]
        · by_cases h2 : i = j₂
          · rw [h2, hj₂]
          · rw [hz i h1 h2]; omega
    · exact Or.inl ⟨hodd, fun i => tag7N_isBall ((hle i).trans hk3)⟩
  · -- the gain class
    have hk := tag7N_gain_eq hgn
    rcases Nat.even_or_odd m with hev | hodd
    · have hsum : ∑ i, f i = 0 := by
        rw [hM] at hk; simp only [hevm.mpr hev, ↓reduceIte] at hk; omega
      refine Or.inl ⟨hev, by obtain ⟨k, hk⟩ := hev; omega, fun i => tag7N_zero ?_⟩
      exact (Finset.sum_eq_zero_iff.mp hsum) i (mem_univ i)
    · have hodd' : ¬ Even (m + 2) := fun h => (Nat.not_even_iff_odd.mpr hodd) (hevm.mp h)
      have hsum : ∑ i, f i = 1 := by
        rw [hM] at hk; simp only [hodd', ↓reduceIte] at hk; omega
      rcases sum_le_two_cases f (by omega) with h0 | ⟨j, hj, hz⟩ | ⟨j, hj, hz⟩ |
          ⟨j₁, j₂, h12, hj₁, hj₂, hz⟩
      · exfalso
        rw [Finset.sum_eq_zero fun i _ => h0 i] at hsum
        omega
      · exact Or.inr ⟨hodd, j, tag7N_isGain (by show f j ≤ 1; omega), fun i hi =>
          tag7N_zero (hz i hi)⟩
      · exfalso
        have : f j ≤ ∑ i, f i := Finset.single_le_sum (fun i _ => Nat.zero_le (f i)) (mem_univ j)
        omega
      · exfalso
        have : f j₁ + f j₂ ≤ ∑ i, f i := Finset.add_le_sum (fun i _ => Nat.zero_le (f i))
          (mem_univ j₁) (mem_univ j₂) (ne_of_lt h12)
        omega


end Rule

end Outerplanar
