/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.InitCert5

/-!
# Height five, `k = 6`: the initial inequality

`Init5Holds 6`: a column of `6`-lists `X₁, …, X₅`, weighted by pattern, weighs at least the
uniform column `{0, …, 5}⁵` (`ai_research_notes/H5_K6_ANALYTIC_2026-10-23.md` §4, Lemmas 10–11).

* **No mismatch.** If `Xⱼ₋₁ ⊆ Xⱼ` for all `j`, the lists are equal, and relabelling gives
  equality (`G_range_eq`).
* **Count gain** (`card_sts_gain5`). With `S = Σⱼ |Xⱼ₋₁ ∖ Xⱼ|`, `|sts X| ≥ 3750 + 120 S`.
  Prepending the first row, `|sts X| = 5 N₄ + Δ` with `N₄ = |sts X₂ … X₅| ≥ 750 + 24 S'`
  (`GridGen.Four.card_sts_gain`) and `Δ = N₄ - |sts (X₁ ∩ X₂) X₃ X₄ X₅| ≥ 120 |X₁ ∖ X₂|`
  (`card_sts_step`). (The note's sharper `3750 + 125 S` is not needed.)
* **Pattern loss** (Lemma 11). At every corner of the box the chain linear programme for lists of
  six colours, with an exact dual certificate (`GridGen/Five/InitCert5.lean`), shows that `3870`
  columns of any system outweigh the uniform column. Since the difference of the two weighted
  sums is linear in the weights, the corner fixed by the signs of its coefficients suffices
  (`corner_pick`).
-/

namespace GridGen.Five

open Finset

/-! ### Relabelling the uniform column -/

/-- The uniform column weighs as much as the constant column of any `k`-set. -/
theorem G_range_eq (w : Wt5) {k : ℕ} {P : Finset ℕ} (hP : P.card = k) :
    G w (range k) (range k) (range k) (range k) (range k) = G w P P P P P := by
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
  have hinj' : Set.InjOn f ↑(range k ∪ range k ∪ range k ∪ range k ∪ range k) := by
    simpa only [union_self] using hinj
  rw [← G_image w hinj', himg]

/-! ### The count gain -/

/-- **One prepended row**: the step `|sts X₂ … X₅| - |sts (X₁ ∩ X₂) X₃ X₄ X₅| ≥ 120 |X₁ ∖ X₂|`
for `6`-lists. -/
theorem card_sts_step {X₁ X₂ X₃ X₄ X₅ : Finset ℕ} (h₂ : X₂.card = 6) (h₃ : X₃.card = 6)
    (h₄ : X₄.card = 6) (h₅ : X₅.card = 6) :
    (120 : ℤ) * (6 - (X₁ ∩ X₂).card)
      ≤ (Four.sts X₂ X₃ X₄ X₅).card - (Four.sts (X₁ ∩ X₂) X₃ X₄ X₅).card := by
  rw [Four.card_sts_formula, Four.card_sts_formula, h₂, h₃, h₄, h₅]
  set Y := X₁ ∩ X₂ with hY
  have hYX : Y ⊆ X₂ := inter_subset_right
  have cl : ∀ {U V : Finset ℕ}, U ⊆ V → U.card ≤ V.card := fun h => Finset.card_le_card h
  -- the intersections
  have y6 : Y.card ≤ 6 := h₂ ▸ cl hYX
  have e34 : (X₃ ∩ X₄).card ≤ 6 := h₃ ▸ cl inter_subset_left
  have e45 : (X₄ ∩ X₅).card ≤ 6 := h₄ ▸ cl inter_subset_left
  have t345 : (X₃ ∩ X₄).card + (X₄ ∩ X₅).card ≤ (X₃ ∩ X₄ ∩ X₅).card + 6 := by
    have h := Finset.card_union_add_card_inter (X₃ ∩ X₄) (X₄ ∩ X₅)
    have hi : X₃ ∩ X₄ ∩ (X₄ ∩ X₅) = X₃ ∩ X₄ ∩ X₅ := by
      ext x; simp only [mem_inter]; tauto
    have hu : (X₃ ∩ X₄ ∪ X₄ ∩ X₅).card ≤ X₄.card :=
      cl (Finset.union_subset inter_subset_right inter_subset_left)
    rw [hi] at h
    omega
  -- `u = |X₂ ∩ X₃| - |Y ∩ X₃| ∈ [0, 6 - |Y|]`
  have u0 : (Y ∩ X₃).card ≤ (X₂ ∩ X₃).card := cl (inter_subset_inter_right hYX)
  have u1 : (X₂ ∩ X₃).card + Y.card ≤ 6 + (Y ∩ X₃).card := by
    have h := Finset.card_union_add_card_inter (X₂ ∩ X₃) Y
    have hi : X₂ ∩ X₃ ∩ Y = Y ∩ X₃ := by
      ext x; simp only [hY, mem_inter]; tauto
    have hu : (X₂ ∩ X₃ ∪ Y).card ≤ X₂.card := cl (Finset.union_subset inter_subset_left hYX)
    rw [hi] at h
    omega
  -- `v = |X₂ ∩ X₃ ∩ X₄| - |Y ∩ X₃ ∩ X₄| ≥ 0` and `x = |X₂ ∩ … ∩ X₅| - |Y ∩ … ∩ X₅| ≤ v`
  have v0 : (Y ∩ X₃ ∩ X₄).card ≤ (X₂ ∩ X₃ ∩ X₄).card :=
    cl (inter_subset_inter_right (inter_subset_inter_right hYX))
  have xv : (X₂ ∩ X₃ ∩ X₄ ∩ X₅).card + (Y ∩ X₃ ∩ X₄).card
      ≤ (X₂ ∩ X₃ ∩ X₄).card + (Y ∩ X₃ ∩ X₄ ∩ X₅).card := by
    have h := Finset.card_union_add_card_inter (X₂ ∩ X₃ ∩ X₄ ∩ X₅) (Y ∩ X₃ ∩ X₄)
    have hi : X₂ ∩ X₃ ∩ X₄ ∩ X₅ ∩ (Y ∩ X₃ ∩ X₄) = Y ∩ X₃ ∩ X₄ ∩ X₅ := by
      ext x; simp only [hY, mem_inter]; tauto
    have hu : (X₂ ∩ X₃ ∩ X₄ ∩ X₅ ∪ Y ∩ X₃ ∩ X₄).card ≤ (X₂ ∩ X₃ ∩ X₄).card := by
      refine cl (Finset.union_subset inter_subset_left ?_)
      intro x; simp only [hY, mem_inter]; tauto
    rw [hi] at h
    omega
  set μ : ℤ := 6 - (Y.card : ℤ) with hμ
  set a : ℤ := ((X₂ ∩ X₃).card : ℤ)
  set a' : ℤ := ((Y ∩ X₃).card : ℤ)
  set b : ℤ := ((X₂ ∩ X₃ ∩ X₄).card : ℤ)
  set b' : ℤ := ((Y ∩ X₃ ∩ X₄).card : ℤ)
  set c : ℤ := ((X₂ ∩ X₃ ∩ X₄ ∩ X₅).card : ℤ)
  set c' : ℤ := ((Y ∩ X₃ ∩ X₄ ∩ X₅).card : ℤ)
  set p : ℤ := ((X₃ ∩ X₄).card : ℤ)
  set q : ℤ := ((X₄ ∩ X₅).card : ℤ)
  set r : ℤ := ((X₃ ∩ X₄ ∩ X₅).card : ℤ)
  have hμ0 : 0 ≤ μ := by omega
  have k1 : 0 ≤ μ * (r - p - q + 6) := mul_nonneg hμ0 (by omega)
  have k2 : 0 ≤ μ * (6 - p) := mul_nonneg hμ0 (by omega)
  have k3 : 0 ≤ μ * (6 - q) := mul_nonneg hμ0 (by omega)
  have k4 : 0 ≤ (μ - (a - a')) * (36 - q) := mul_nonneg (by omega) (by omega)
  have ev : ((6 : ℕ) : ℤ) * 6 * 6 * 6 - a * 6 * 6 - (6 : ℕ) * p * 6 - (6 : ℕ) * 6 * q
        + b * 6 + (6 : ℕ) * r + a * q - c
      - ((Y.card : ℤ) * 6 * 6 * 6 - a' * 6 * 6 - Y.card * p * 6 - Y.card * 6 * q
        + b' * 6 + Y.card * r + a' * q - c')
      = μ * (216 - 6 * p - 6 * q + r) - (a - a') * (36 - q) + 6 * (b - b') - (c - c') := by
    rw [hμ]; push_cast; ring
  push_cast at ev ⊢
  rw [ev]
  nlinarith

/-- **The count gain at height five**: `|sts X| ≥ 3750 + 120 S` for `6`-lists. -/
theorem card_sts_gain5 {X₁ X₂ X₃ X₄ X₅ : Finset ℕ} (h₁ : X₁.card = 6) (h₂ : X₂.card = 6)
    (h₃ : X₃.card = 6) (h₄ : X₄.card = 6) (h₅ : X₅.card = 6) :
    (3750 : ℤ) + 120 * ((X₁ \ X₂).card + (X₂ \ X₃).card + (X₃ \ X₄).card + (X₄ \ X₅).card)
      ≤ (sts X₁ X₂ X₃ X₄ X₅).card := by
  rw [card_sts, h₁]
  have hstep := card_sts_step (X₁ := X₁) h₂ h₃ h₄ h₅
  have hgain := Four.card_sts_gain h₂ h₃ h₄ h₅ (by norm_num)
  have s12 := Finset.card_sdiff_add_card_inter X₁ X₂
  push_cast at hgain
  have : ((X₁ \ X₂).card : ℤ) = 6 - (X₁ ∩ X₂).card := by omega
  rw [this]
  push_cast
  linarith

/-! ### The initial inequality -/

theorem sum11_eq (f : Fin 11 → ℕ) : sum11 f = ∑ o, f o := by
  simp only [sum11, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  simp only [add_assoc]
  rfl

theorem zsum_eq (Z : List ℕ) : zsum Z = ∑ p ∈ range 14, Z.getD p 0 := by
  simp only [zsum, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

/-- The orbit counts of the uniform column. -/
theorem V0_counts : ∀ o : Fin 11,
    ((sts (range 6) (range 6) (range 6) (range 6) (range 6)).filter (fun t => orb t = o)).card
      = V0L.getD o 0 := by
  decide +kernel

/-- **The pattern comparison at a corner**: a system of `6`-lists with at least `3870` proper
columns weighs at least the uniform column at every corner of the box. -/
theorem corner_init {X₁ X₂ X₃ X₄ X₅ : Finset ℕ} (h₁ : X₁.card = 6) (h₂ : X₂.card = 6)
    (h₃ : X₃.card = 6) (h₄ : X₄.card = 6) (h₅ : X₅.card = 6)
    (hN : 3870 ≤ (sts X₁ X₂ X₃ X₄ X₅).card) {β : List Bool} (hβ : β ∈ allBits 10) :
    ∑ o : Fin 11, (V0L.getD o 0 : ℝ) * sigR β o
      ≤ ∑ o, (((sts X₁ X₂ X₃ X₄ X₅).filter (fun t => orb t = o)).card : ℝ) * sigR β o := by
  obtain ⟨c, hc⟩ := exists_mem_zip (l₂ := initCerts)
    (by rw [length_allBits, initCerts_length]; rfl) hβ
  have hok := List.all_eq_true.mp initCerts_ok _ hc
  simp only [initOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hpt, hfin⟩ := hok
  set Ω := sts X₁ X₂ X₃ X₄ X₅ with hΩ
  have hB : ∀ p < 14, chainB 6 p * (Ω.filter (fun t => evb p t = true)).card ≤ Ω.card :=
    fun p _ => chain_bound (L := 6) (by norm_num) h₁.ge h₂.ge h₃.ge h₄.ge h₅.ge p
  have hlp := lp_count (fun t ht => proper_of_mem_sts ht) (chainB 6) hB hpt
  rw [← zsum_eq] at hlp
  rw [sum11_eq] at hfin
  -- in the reals
  have hlpR : (c.1 : ℝ) * Ω.card
      ≤ 5000 * (2000 * ∑ o, ((Ω.filter (fun t => orb t = o)).card : ℝ) * sigR β o)
        + (zsum c.2 : ℝ) * Ω.card := by
    rw [← sum_sigN_orb]; exact_mod_cast hlp
  have hfinR : (3870 : ℝ) * zsum c.2 + 5000 * ∑ o : Fin 11, (V0L.getD o 0 : ℝ) * (sigN β o : ℝ)
      ≤ 3870 * c.1 := by exact_mod_cast hfin
  simp only [sigN_eq] at hfinR
  have hNR : (3870 : ℝ) ≤ Ω.card := by exact_mod_cast hN
  have hs0 : 0 ≤ ∑ o : Fin 11, (V0L.getD o 0 : ℝ) * (2000 * sigR β o) := by
    refine Finset.sum_nonneg fun o _ => mul_nonneg (Nat.cast_nonneg _) ?_
    have := sigN_eq β o; have h0 : (0 : ℝ) ≤ sigN β o := Nat.cast_nonneg _; linarith
  have hd : (0 : ℝ) ≤ c.1 - zsum c.2 := by nlinarith
  have h3 : (c.1 - zsum c.2 : ℝ) * 3870 ≤ (c.1 - zsum c.2) * Ω.card :=
    mul_le_mul_of_nonneg_left hNR hd
  have e : ∑ o : Fin 11, (V0L.getD o 0 : ℝ) * (2000 * sigR β o)
      = 2000 * ∑ o : Fin 11, (V0L.getD o 0 : ℝ) * sigR β o := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun o _ => by ring
  rw [e] at hfinR
  nlinarith

/-- **The height-five initial inequality at `k = 6`.** -/
theorem init5Holds_six : Init5Holds 6 := by
  intro w hw X₁ X₂ X₃ X₄ X₅ h₁ h₂ h₃ h₄ h₅
  show G w (range 6) (range 6) (range 6) (range 6) (range 6) ≤ G w X₁ X₂ X₃ X₄ X₅
  by_cases hS : (X₁ \ X₂).card + (X₂ \ X₃).card + (X₃ \ X₄).card + (X₄ \ X₅).card = 0
  · -- no mismatch: the lists are equal
    have eq : ∀ {U V : Finset ℕ}, U.card = 6 → V.card = 6 → (U \ V).card = 0 → U = V := by
      intro U V hU hV h
      have hs : U ⊆ V := by
        intro x hx
        by_contra hxV
        have : x ∈ U \ V := mem_sdiff.mpr ⟨hx, hxV⟩
        rw [Finset.card_eq_zero.mp h] at this
        simp at this
      exact Finset.eq_of_subset_of_card_le hs (by omega)
    have e12 := eq h₁ h₂ (by omega)
    have e23 := eq h₂ h₃ (by omega)
    have e34 := eq h₃ h₄ (by omega)
    have e45 := eq h₄ h₅ (by omega)
    subst e12 e23 e34 e45
    rw [G_range_eq w h₁]
  · -- a mismatch: at least `3870` columns
    have hgain := card_sts_gain5 h₁ h₂ h₃ h₄ h₅
    have hN : 3870 ≤ (sts X₁ X₂ X₃ X₄ X₅).card := by omega
    unfold G
    rw [sum_gw_orb, sum_gw_orb, ← sub_nonneg, ← Finset.sum_sub_distrib]
    have hlin : ∀ o : Fin 11, (((sts X₁ X₂ X₃ X₄ X₅).filter (fun t => orb t = o)).card : ℝ)
        * w o - (((sts (range 6) (range 6) (range 6) (range 6) (range 6)).filter
          (fun t => orb t = o)).card : ℝ) * w o
        = ((((sts X₁ X₂ X₃ X₄ X₅).filter (fun t => orb t = o)).card : ℝ)
          - V0L.getD o 0) * w o := by
      intro o; rw [V0_counts]; ring
    simp only [hlin]
    obtain ⟨β, hβ, hpick⟩ := corner_pick hw (fun o =>
      (((sts X₁ X₂ X₃ X₄ X₅).filter (fun t => orb t = o)).card : ℝ) - V0L.getD o 0)
    have hc := corner_init h₁ h₂ h₃ h₄ h₅ hN hβ
    have e : ∑ o, ((((sts X₁ X₂ X₃ X₄ X₅).filter (fun t => orb t = o)).card : ℝ)
        - V0L.getD o 0) * sigR β o
        = ∑ o, (((sts X₁ X₂ X₃ X₄ X₅).filter (fun t => orb t = o)).card : ℝ) * sigR β o
          - ∑ o : Fin 11, (V0L.getD o 0 : ℝ) * sigR β o := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun o _ => by ring
    linarith

end GridGen.Five
