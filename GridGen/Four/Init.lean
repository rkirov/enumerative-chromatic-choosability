/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.Pattern
import GridGen.Four.Relabel

/-!
# Height four: the initial inequality

`Init4Holds k` for every `k ≥ 7`: a column of `k`-lists `X₁, …, X₄`, weighted by pattern, weighs
at least the uniform column `range k`.

* **Relabelling.** The uniform column weighs as much as the constant column `(P, P, P, P)` for
  any `k`-set `P` (`G_image`); take `P = X₂`.
* **Count gain.** With `μ₂ = |X₁ ∖ X₂|`, `μ₃ = |X₂ ∖ X₃|`, `μ₄ = |X₃ ∖ X₄|` and `S = μ₂ + μ₃ + μ₄`,
  the exact count (`card_sts_formula`) and the bounds `|X₁ ∩ X₂ ∩ X₃| ≥ k - μ₂ - μ₃`,
  `|X₂ ∩ X₃ ∩ X₄| ≥ k - μ₃ - μ₄`, `|X₁ ∩ X₂ ∩ X₃ ∩ X₄| ≤ |X₂ ∩ X₃ ∩ X₄|` give
  `|sts X| - k(k-1)³ ≥ k(k-2)·S` (`card_sts_gain`). As `|sts X| ≤ k⁴`, the log count ratio is at
  least `(k-2)S/k³`.
* **Pattern loss.** `pattern_log_ge` against `(P, P, P, P)` costs at most
  `(1-ρ)/ρ · 2S/(k-3) = 4S/(((k-2)³-2)(k-3))`, since `Σ|Xᵢ ∖ X₂| ≤ μ₂ + 2μ₃ + μ₄`.

The gain dominates the loss for every `k ≥ 7` (`init_rate`).
-/

namespace GridGen.Four

open Finset

/-! ### Relabelling the uniform column -/

/-- The uniform column weighs as much as the constant column of any `k`-set. -/
theorem G_range_eq (w : Wt) {k : ℕ} {P : Finset ℕ} (hP : P.card = k) :
    G w (range k) (range k) (range k) (range k) = G w P P P P := by
  set e := P.orderEmbOfFin hP
  let f : ℕ → ℕ := fun i => if h : i < k then e ⟨i, h⟩ else 0
  have hinj : Set.InjOn f ↑(range k) := by
    intro i hi j hj hij
    simp only [coe_range, Set.mem_Iio] at hi hj
    simp only [f, hi, hj, dite_true] at hij
    exact congrArg Fin.val (e.injective hij)
  have himg : (range k).image f = P := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro x hx
      have hx' : x ∈ Set.range e := by rw [Finset.range_orderEmbOfFin]; exact hx
      obtain ⟨i, rfl⟩ := hx'
      refine Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr i.2, ?_⟩
      simp [f, i.2]
    · rw [Finset.card_image_of_injOn hinj, card_range, hP]
  have hinj' : Set.InjOn f ↑(range k ∪ range k ∪ range k ∪ range k) := by
    simpa only [union_self] using hinj
  rw [← G_image w hinj', himg]

/-! ### The count gain -/

/-- **The count gain.** For `k`-lists, the number of proper columns exceeds the constant count
`k(k-1)³` by at least `k(k-2)` per consecutive mismatch. -/
theorem card_sts_gain {k : ℕ} {X₁ X₂ X₃ X₄ : Finset ℕ} (h₁ : X₁.card = k) (h₂ : X₂.card = k)
    (h₃ : X₃.card = k) (h₄ : X₄.card = k) (hk : 1 ≤ k) :
    (k : ℤ) * (k - 1) ^ 3 + k * (k - 2) * ((X₁ \ X₂).card + (X₂ \ X₃).card + (X₃ \ X₄).card)
      ≤ (sts X₁ X₂ X₃ X₄).card := by
  rw [card_sts_formula]
  have e12 := Finset.card_sdiff_add_card_inter X₁ X₂
  have e23 := Finset.card_sdiff_add_card_inter X₂ X₃
  have e34 := Finset.card_sdiff_add_card_inter X₃ X₄
  -- the triple intersections
  have t123 : (X₁ ∩ X₂).card + (X₂ ∩ X₃).card ≤ (X₁ ∩ X₂ ∩ X₃).card + k := by
    have h := Finset.card_union_add_card_inter (X₁ ∩ X₂) (X₂ ∩ X₃)
    have hi : X₁ ∩ X₂ ∩ (X₂ ∩ X₃) = X₁ ∩ X₂ ∩ X₃ := by
      ext x; simp only [mem_inter]; tauto
    have hu : (X₁ ∩ X₂ ∪ X₂ ∩ X₃).card ≤ X₂.card :=
      Finset.card_le_card (Finset.union_subset inter_subset_right inter_subset_left)
    rw [hi] at h
    omega
  have t234 : (X₂ ∩ X₃).card + (X₃ ∩ X₄).card ≤ (X₂ ∩ X₃ ∩ X₄).card + k := by
    have h := Finset.card_union_add_card_inter (X₂ ∩ X₃) (X₃ ∩ X₄)
    have hi : X₂ ∩ X₃ ∩ (X₃ ∩ X₄) = X₂ ∩ X₃ ∩ X₄ := by
      ext x; simp only [mem_inter]; tauto
    have hu : (X₂ ∩ X₃ ∪ X₃ ∩ X₄).card ≤ X₃.card :=
      Finset.card_le_card (Finset.union_subset inter_subset_right inter_subset_left)
    rw [hi] at h
    omega
  have hq : (X₁ ∩ X₂ ∩ X₃ ∩ X₄).card ≤ (X₂ ∩ X₃ ∩ X₄).card := by
    apply Finset.card_le_card
    intro x; simp only [mem_inter]; tauto
  rw [h₁, h₂, h₃, h₄]
  set μ₂ := (X₁ \ X₂).card
  set μ₃ := (X₂ \ X₃).card
  set μ₄ := (X₃ \ X₄).card
  set a₁₂ := (X₁ ∩ X₂).card
  set a₂₃ := (X₂ ∩ X₃).card
  set a₃₄ := (X₃ ∩ X₄).card
  set t₁ := (X₁ ∩ X₂ ∩ X₃).card
  set t₂ := (X₂ ∩ X₃ ∩ X₄).card
  set q := (X₁ ∩ X₂ ∩ X₃ ∩ X₄).card
  have z12 : (a₁₂ : ℤ) = k - μ₂ := by omega
  have z23 : (a₂₃ : ℤ) = k - μ₃ := by omega
  have z34 : (a₃₄ : ℤ) = k - μ₄ := by omega
  have zt1 : (k : ℤ) - μ₂ - μ₃ ≤ t₁ := by omega
  have zt2 : (k : ℤ) - μ₃ - μ₄ ≤ t₂ := by omega
  have zq : (q : ℤ) ≤ t₂ := by exact_mod_cast hq
  have hk1 : (1 : ℤ) ≤ k := by exact_mod_cast hk
  rw [z12, z23, z34]
  nlinarith [mul_nonneg (by positivity : (0 : ℤ) ≤ k) (by linarith : (0 : ℤ) ≤ t₁ - (k - μ₂ - μ₃)),
    mul_nonneg (by linarith : (0 : ℤ) ≤ k - 1) (by linarith : (0 : ℤ) ≤ t₂ - (k - μ₃ - μ₄)),
    mul_nonneg (by positivity : (0 : ℤ) ≤ μ₂) (by positivity : (0 : ℤ) ≤ μ₄),
    mul_nonneg (by positivity : (0 : ℤ) ≤ μ₃) (by linarith : (0 : ℤ) ≤ k - 1),
    mul_nonneg (by positivity : (0 : ℤ) ≤ μ₄) (by linarith : (0 : ℤ) ≤ k - 1)]

/-- Proper columns of `k`-lists number at most `k⁴`. -/
theorem card_sts_le {k : ℕ} {X₁ X₂ X₃ X₄ : Finset ℕ} (h₁ : X₁.card = k) (h₂ : X₂.card = k)
    (h₃ : X₃.card = k) (h₄ : X₄.card = k) : (sts X₁ X₂ X₃ X₄).card ≤ k ^ 4 := by
  have hsub : sts X₁ X₂ X₃ X₄ ⊆ X₁ ×ˢ X₂ ×ˢ X₃ ×ˢ X₄ := by
    intro t ht
    rw [mem_sts] at ht
    simp only [mem_product]
    exact ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1⟩
  refine (Finset.card_le_card hsub).trans_eq ?_
  simp only [card_product, h₁, h₂, h₃, h₄]
  ring

/-! ### The rate comparison -/

/-- **Gain beats loss.** For `k ≥ 7`, `(k-2)/k³ ≥ 4/(((k-2)³-2)(k-3))`, as a statement with the
mismatch `S ≥ 0` multiplied in. -/
theorem init_rate {x S : ℝ} (hx : 7 ≤ x) (hS : 0 ≤ S) :
    4 * S / (((x - 2) ^ 3 - 2) * (x - 3)) ≤ (x - 2) * S / x ^ 3 := by
  have hd : 0 < ((x - 2) ^ 3 - 2) * (x - 3) := by
    apply mul_pos _ (by linarith); nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5)
      (by linarith : (5 : ℝ) ≤ x - 2) 3]
  rw [div_le_div_iff₀ hd (by positivity)]
  -- `4x³ ≤ (x-2)((x-2)³-2)(x-3)`, with `y = x - 7 ≥ 0`
  have hp : 4 * x ^ 3 ≤ (x - 2) * (((x - 2) ^ 3 - 2) * (x - 3)) := by
    obtain ⟨y, hy, rfl⟩ : ∃ y, 0 ≤ y ∧ x = y + 7 := ⟨x - 7, by linarith, by ring⟩
    nlinarith [pow_nonneg hy 2, pow_nonneg hy 3, pow_nonneg hy 4, pow_nonneg hy 5]
  nlinarith [mul_le_mul_of_nonneg_left hp hS]

/-! ### The initial inequality -/

/-- **The height-four initial inequality for every `k ≥ 7`.** -/
theorem init4Holds {k : ℕ} (hk : 7 ≤ k) : Init4Holds k := by
  intro w hw X₁ X₂ X₃ X₄ h₁ h₂ h₃ h₄
  have hkR : (7 : ℝ) ≤ k := by exact_mod_cast hk
  -- the weights
  have hden : (0 : ℝ) < ((k : ℝ) - 2) ^ 3 - 2 := by
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5) (by linarith : (5 : ℝ) ≤ (k : ℝ) - 2) 3]
  have hc3 : (0 : ℝ) < ((k : ℝ) - 2) ^ 3 := by linarith
  have hρ : rho k = (((k : ℝ) - 2) ^ 3 - 2) / ((k : ℝ) - 2) ^ 3 := by
    rw [rho, eq_div_iff hc3.ne', sub_mul, div_mul_cancel₀ _ hc3.ne', one_mul]
  have hρ0 : 0 < rho k := by rw [hρ]; positivity
  have hρ1 : rho k ≤ 1 := by rw [rho]; have : 0 ≤ 2 / ((k : ℝ) - 2) ^ 3 := by positivity
                             linarith
  have hρq : (1 - rho k) / rho k = 2 / (((k : ℝ) - 2) ^ 3 - 2) := by
    rw [hρ, one_sub_div hc3.ne', div_div_div_cancel_right₀ hc3.ne']
    ring
  obtain ⟨ha0, ha1, hb0, hb1, hc0, hc1⟩ := hw
  have hg : ∀ t, rho k ≤ gw w t ∧ gw w t ≤ 1 := by
    intro t; unfold gw
    split_ifs
    · exact ⟨hρ1, le_rfl⟩
    · exact ⟨ha0, ha1⟩
    · exact ⟨hb0, hb1⟩
    · exact ⟨hc0, hc1⟩
  -- relabel the uniform side to the constant column of `X₂`
  show G w (range k) (range k) (range k) (range k) ≤ G w X₁ X₂ X₃ X₄
  rw [G_range_eq w h₂]
  -- the counts, before abbreviating
  have hNX : (0 : ℝ) < (sts X₁ X₂ X₃ X₄).card := by
    exact_mod_cast (sts_nonempty (A₁ := X₁) (A₂ := X₂) (A₃ := X₃) (A₄ := X₄)
      (by omega) (by omega) (by omega) (by omega)).card_pos
  have hNP : (0 : ℝ) < (sts X₂ X₂ X₂ X₂).card := by
    exact_mod_cast (sts_nonempty (A₁ := X₂) (A₂ := X₂) (A₃ := X₂) (A₄ := X₂)
      (by omega) (by omega) (by omega) (by omega)).card_pos
  have hNXle : ((sts X₁ X₂ X₃ X₄).card : ℝ) ≤ (k : ℝ) ^ 4 := by
    exact_mod_cast card_sts_le h₁ h₂ h₃ h₄
  have hP' : ((sts X₂ X₂ X₂ X₂).card : ℝ) = (k : ℝ) * ((k : ℝ) - 1) ^ 3 := by
    have e := card_sts_formula X₂ X₂ X₂ X₂
    simp only [inter_self, h₂] at e
    have e' : ((sts X₂ X₂ X₂ X₂).card : ℤ) = k * ((k : ℤ) - 1) ^ 3 := by rw [e]; ring
    have := congrArg (fun z : ℤ => (z : ℝ)) e'
    push_cast at this
    exact this
  have hX' : (k : ℝ) * ((k : ℝ) - 1) ^ 3 + (k : ℝ) * ((k : ℝ) - 2) *
      (((X₁ \ X₂).card : ℝ) + (X₂ \ X₃).card + (X₃ \ X₄).card) ≤ (sts X₁ X₂ X₃ X₄).card := by
    have := (Int.cast_le (R := ℝ)).mpr (card_sts_gain h₁ h₂ h₃ h₄ (by omega))
    push_cast at this
    exact this
  have hGlow : ∀ A B C D : Finset ℕ, rho k * (sts A B C D).card ≤ G w A B C D := by
    intro A B C D
    have := Finset.card_nsmul_le_sum (sts A B C D) (gw w) (rho k) (fun t _ => (hg t).1)
    rw [G]; simpa [nsmul_eq_mul, mul_comm] using this
  have hGX : 0 < G w X₁ X₂ X₃ X₄ := lt_of_lt_of_le (mul_pos hρ0 hNX) (hGlow _ _ _ _)
  have hGP : 0 < G w X₂ X₂ X₂ X₂ := lt_of_lt_of_le (mul_pos hρ0 hNP) (hGlow _ _ _ _)
  set GX := G w X₁ X₂ X₃ X₄
  set GP := G w X₂ X₂ X₂ X₂
  set NX : ℝ := ((sts X₁ X₂ X₃ X₄).card : ℝ)
  set NP : ℝ := ((sts X₂ X₂ X₂ X₂).card : ℝ)
  -- the mismatches
  set μ₂ := (X₁ \ X₂).card
  set μ₃ := (X₂ \ X₃).card
  set μ₄ := (X₃ \ X₄).card
  set S : ℝ := (μ₂ : ℝ) + μ₃ + μ₄ with hSdef
  have hS : 0 ≤ S := by positivity
  -- the count gain
  have hgain : (k : ℝ) * (k - 2) * S ≤ NX - NP := by
    rw [hP', hSdef]; linarith
  have hlogN : ((k : ℝ) - 2) * S / (k : ℝ) ^ 3 ≤ Real.log (NX / NP) := by
    have hlog : 1 - NP / NX ≤ Real.log (NX / NP) := by
      have := Real.one_sub_inv_le_log_of_pos (div_pos hNX hNP)
      rwa [inv_div] at this
    refine le_trans ?_ hlog
    rw [show 1 - NP / NX = (NX - NP) / NX by field_simp]
    have hk0 : (0 : ℝ) < k := by linarith
    have h1 : ((k : ℝ) - 2) * S / (k : ℝ) ^ 3 = (k : ℝ) * (k - 2) * S / (k : ℝ) ^ 4 := by
      field_simp
    rw [h1]
    have hnum : 0 ≤ (k : ℝ) * (k - 2) * S := by
      apply mul_nonneg (mul_nonneg hk0.le (by linarith)) hS
    calc (k : ℝ) * (k - 2) * S / (k : ℝ) ^ 4 ≤ (k : ℝ) * (k - 2) * S / NX :=
          div_le_div_of_nonneg_left hnum hNX hNXle
      _ ≤ (NX - NP) / NX := div_le_div_of_nonneg_right hgain hNX.le
  -- the pattern loss
  have hk4 : 4 ≤ k := by omega
  have hpat := pattern_log_ge (A₁ := X₁) (A₂ := X₂) (A₃ := X₃) (A₄ := X₄)
    (U₁ := X₂) (U₂ := X₂) (U₃ := X₂) (U₄ := X₂) hk4 (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) w hρ0 hρ1 hg
  have hmax : max ((X₁ \ X₂).card + (X₂ \ X₂).card + (X₃ \ X₂).card + (X₄ \ X₂).card : ℝ)
      ((X₂ \ X₁).card + (X₂ \ X₂).card + (X₂ \ X₃).card + (X₂ \ X₄).card) ≤ 2 * S := by
    have s12 := Finset.card_sdiff_add_card_inter X₁ X₂
    have s21 := Finset.card_sdiff_add_card_inter X₂ X₁
    have s23 := Finset.card_sdiff_add_card_inter X₂ X₃
    have s32 := Finset.card_sdiff_add_card_inter X₃ X₂
    have s34 := Finset.card_sdiff_add_card_inter X₃ X₄
    have s43 := Finset.card_sdiff_add_card_inter X₄ X₃
    rw [inter_comm X₂ X₁] at s21
    rw [inter_comm X₃ X₂] at s32
    rw [inter_comm X₄ X₃] at s43
    have u42 : (X₄ \ X₂).card ≤ (X₄ \ X₃).card + (X₃ \ X₂).card := by
      refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
      intro x; simp only [mem_sdiff, mem_union]; tauto
    have u24 : (X₂ \ X₄).card ≤ (X₂ \ X₃).card + (X₃ \ X₄).card := by
      refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
      intro x; simp only [mem_sdiff, mem_union]; tauto
    have nA : (X₁ \ X₂).card + (X₂ \ X₂).card + (X₃ \ X₂).card + (X₄ \ X₂).card
        ≤ 2 * (μ₂ + μ₃ + μ₄) := by simp only [Finset.sdiff_self, card_empty]; omega
    have nU : (X₂ \ X₁).card + (X₂ \ X₂).card + (X₂ \ X₃).card + (X₂ \ X₄).card
        ≤ 2 * (μ₂ + μ₃ + μ₄) := by simp only [Finset.sdiff_self, card_empty]; omega
    have nA' : ((X₁ \ X₂).card + (X₂ \ X₂).card + (X₃ \ X₂).card + (X₄ \ X₂).card : ℝ) ≤ 2 * S := by
      rw [hSdef]; exact_mod_cast nA
    have nU' : ((X₂ \ X₁).card + (X₂ \ X₂).card + (X₂ \ X₃).card + (X₂ \ X₄).card : ℝ) ≤ 2 * S := by
      rw [hSdef]; exact_mod_cast nU
    exact max_le nA' nU'
  have hk3 : ((k - 3 : ℕ) : ℝ) = (k : ℝ) - 3 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  have hloss : -(4 * S / ((((k : ℝ) - 2) ^ 3 - 2) * ((k : ℝ) - 3)))
      ≤ Real.log ((GX / NX) / (GP / NP)) := by
    refine le_trans ?_ hpat
    rw [hρq, hk3, neg_le_neg_iff]
    have hk3p : (0 : ℝ) < (k : ℝ) - 3 := by linarith
    calc 2 / (((k : ℝ) - 2) ^ 3 - 2) * (max _ _ / ((k : ℝ) - 3))
        ≤ 2 / (((k : ℝ) - 2) ^ 3 - 2) * (2 * S / ((k : ℝ) - 3)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact div_le_div_of_nonneg_right hmax hk3p.le
      _ = 4 * S / ((((k : ℝ) - 2) ^ 3 - 2) * ((k : ℝ) - 3)) := by
          field_simp; ring
  -- combine
  have hsplit : GX / GP = (GX / NX) / (GP / NP) * (NX / NP) := by
    field_simp
  have hlog : 0 ≤ Real.log (GX / GP) := by
    rw [hsplit, Real.log_mul (by positivity) (by positivity)]
    have := init_rate hkR hS
    linarith
  have := (Real.log_nonneg_iff (div_pos hGX hGP)).mp hlog
  rwa [le_div_iff₀ hGP, one_mul] at this

end GridGen.Four
