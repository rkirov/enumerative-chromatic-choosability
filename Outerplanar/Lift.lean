/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.SevenEven

/-!
# Vertex lifts

A branch hanging at a cut vertex `v`, exposed at an edge `vw` with pair profile `X` on the lists
of `v` and `w`, acts on the rest of the graph through the vertex profile

`liftV T X c = ∑_{e ∈ T, e ≠ c} X c e`

(`T` the list of `w`), which can be put on any edge `vy` at `v` as the pair profile
`(c, d) ↦ liftV T X c`. This file shows that the lift keeps every class of the seven-even-face
tag system, with the constant doubled (research note
`ai_research_notes/OUTERPLANAR_SEVEN_AND_CUTS_2026-11-23.md`, "Computing at a cut vertex"):

* for a matched six-family at `vy` and an enumeration of `T` aligned with its row enumeration,
  each row of the parent dominates twice the mean of the two child cells of that row
  (`lift_vec`): a doubly stochastic mixing (`Drow`), so the four-cell bound (`four_mix`) and the
  hull class (`HullV.ds`) pass;
* rowwise AM–GM: `(∏ liftV)² ≥ 64 ∏ (six-family of X)` (`lift_prod_sq`), which gives the
  hexagon bound and, since a row-constant table only sees the product of its rows, the rank-one
  bound `HasPot` from the hexagon bound alone (`lift_hasPot`);
* the ball class through the vertex ball class of `Outerplanar/VBall.lean` (`lift_ball`);
* the gain class: the lifted table of `Z` has bijection products at least `q` because the six
  cells of a family are two bijections (`lift_gain`).

**`scls_lift`** collects these for the tags `STag` of `Outerplanar/SevenEven.lean`; the lifted tag
demands the rank-one bound in addition (`STag.lift`).

The theorem of the note is due to another AI session of this repository's collaboration;
audited and formalized by Claude.
-/

namespace Outerplanar

open Finset

/-- The vertex profile of a branch exposed at `vw`, as a function of the colour of `v`. -/
noncomputable def liftV (T : Finset ℕ) (X : ℕ → ℕ → ℝ) (c : ℕ) : ℝ :=
  ∑ e ∈ T, if c ≠ e then X c e else 0

variable {S T U : Finset ℕ} {X : ℕ → ℕ → ℝ} {A : ℝ}

theorem liftV_nonneg (hX : ∀ c d, 0 ≤ X c d) (c : ℕ) : 0 ≤ liftV T X c :=
  Finset.sum_nonneg fun e _ => by split_ifs; exact hX _ _; exact le_refl 0

theorem sum_three_at (f : Fin 3 → ℝ) (x : Fin 3) : ∑ b, f b = f x + f (x + 1) + f (x + 2) := by
  fin_cases x <;> simp [Fin.sum_univ_three] <;> ring

/-- One row of the lift dominates the two child cells of the row. -/
theorem lift_row (hT : T.card = 3) (hX : ∀ c d, 0 ≤ X c d) {α ξ : Fin 3 → ℕ}
    (hξ : Function.Injective ξ) (hξm : ∀ b, ξ b ∈ T) (hal : ∀ c a, ξ c = α a → a = c)
    (x : Fin 3) : X (α x) (ξ (x + 1)) + X (α x) (ξ (x + 2)) ≤ liftV T X (α x) := by
  unfold liftV
  rw [sum_enum hT hξ hξm, sum_three_at _ x]
  have hne : ∀ b, b ≠ x → α x ≠ ξ b := fun b hb e => hb (hal b x e.symm).symm
  have h0 : 0 ≤ (if α x ≠ ξ x then X (α x) (ξ x) else 0) := by
    split_ifs; exact hX _ _; exact le_refl 0
  simp only [ne_eq, hne _ (add_one_ne x).symm, hne _ (add_two_ne x).symm, not_false_eq_true,
    ↓reduceIte]
  linarith

/-- The mixing matrix of a lift: each parent cell takes half of each child cell of its row. -/
noncomputable def Drow (k z : Fin 6) : ℝ := if (offPair z).1 = (offPair k).1 then 1 / 2 else 0

theorem Drow_ds : DS Drow := by
  refine ⟨fun k z => by unfold Drow; split_ifs <;> norm_num, fun k => ?_, fun z => ?_⟩
  · fin_cases k <;> simp [Drow, Fin.sum_univ_six, offPair] <;> norm_num
  · fin_cases z <;> simp [Drow, Fin.sum_univ_six, offPair] <;> norm_num

/-- The child six-family along an enumeration and an aligned one. -/
theorem lift_vec (hT : T.card = 3) (hX : ∀ c d, 0 ≤ X c d) {α ξ : Fin 3 → ℕ}
    (hξ : Function.Injective ξ) (hξm : ∀ b, ξ b ∈ T) (hal : ∀ c a, ξ c = α a → a = c)
    (k : Fin 6) :
    2 * ∑ z, Drow k z * X (α (offPair z).1) (ξ (offPair z).2) ≤ liftV T X (α (offPair k).1) := by
  have r0 := lift_row hT hX hξ hξm hal 0
  have r1 := lift_row hT hX hξ hξm hal 1
  have r2 := lift_row hT hX hξ hξm hal 2
  simp only [show ((0 : Fin 3) + 1) = 1 from rfl, show ((1 : Fin 3) + 1) = 2 from rfl,
    show ((2 : Fin 3) + 1) = 0 from rfl, show ((0 : Fin 3) + 2) = 2 from rfl,
    show ((1 : Fin 3) + 2) = 0 from rfl, show ((2 : Fin 3) + 2) = 1 from rfl] at r0 r1 r2
  fin_cases k <;> simp [Drow, Fin.sum_univ_six, offPair] <;> linarith

/-- An aligned enumeration of the second list makes a matched family of proper pairs. -/
theorem aligned_family {α ξ : Fin 3 → ℕ} (hα : Function.Injective α) (hξ : Function.Injective ξ)
    (hαm : ∀ a, α a ∈ S) (hξm : ∀ b, ξ b ∈ T) (hal : ∀ c a, ξ c = α a → a = c) :
    Matched S T (fun z => α (offPair z).1) (fun z => ξ (offPair z).2) ∧
      ∀ z, α (offPair z).1 ≠ ξ (offPair z).2 :=
  ⟨matched_of_enum hα hξ hαm hξm, fun z e => offPair_ne z (hal _ _ e.symm)⟩

/-- Rowwise AM–GM. -/
theorem lift_prod_sq (hT : T.card = 3) (hX : ∀ c d, 0 ≤ X c d) {α ξ : Fin 3 → ℕ}
    (hξ : Function.Injective ξ) (hξm : ∀ b, ξ b ∈ T) (hal : ∀ c a, ξ c = α a → a = c) :
    64 * ∏ z : Fin 6, X (α (offPair z).1) (ξ (offPair z).2) ≤ (∏ x, liftV T X (α x)) ^ 2 := by
  have r := fun x => lift_row hT hX hξ hξm hal x
  have q : ∀ x : Fin 3, 4 * (X (α x) (ξ (x + 1)) * X (α x) (ξ (x + 2))) ≤ liftV T X (α x) ^ 2 :=
    fun x => le_trans (four_mul_le_sq (hX _ _) (hX _ _) le_rfl)
      (pow_le_pow_left₀ (add_nonneg (hX _ _) (hX _ _)) (r x) 2)
  have e : 64 * ∏ z : Fin 6, X (α (offPair z).1) (ξ (offPair z).2)
      = (4 * (X (α 0) (ξ (0 + 1)) * X (α 0) (ξ (0 + 2))))
        * (4 * (X (α 1) (ξ (1 + 1)) * X (α 1) (ξ (1 + 2))))
        * (4 * (X (α 2) (ξ (2 + 1)) * X (α 2) (ξ (2 + 2)))) := by
    simp only [Fin.prod_univ_six, offPair]
    simp only [Matrix.cons_val]
    simp only [show ((0 : Fin 3) + 1) = 1 from rfl, show ((1 : Fin 3) + 1) = 2 from rfl,
      show ((2 : Fin 3) + 1) = 0 from rfl, show ((0 : Fin 3) + 2) = 2 from rfl,
      show ((1 : Fin 3) + 2) = 0 from rfl, show ((2 : Fin 3) + 2) = 1 from rfl]
    ring
  rw [e, Fin.prod_univ_three, mul_pow, mul_pow]
  have p := fun x : Fin 3 => mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
    (mul_nonneg (hX (α x) (ξ (x + 1))) (hX (α x) (ξ (x + 2))))
  exact mul_le_mul (mul_le_mul (q 0) (q 1) (p 1) (sq_nonneg _)) (q 2) (p 2)
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The product of the lifted rows, from the products of the six-families of `X`. -/
theorem lift_prod (hS : S.card = 3) (hT : T.card = 3) (hX : ∀ c d, 0 ≤ X c d) {K : ℝ}
    (hK : 0 ≤ K)
    (h : ∀ p q : Fin 6 → ℕ, Matched S T p q → (∀ i, p i ≠ q i) → K ^ 2 ≤ ∏ i, X (p i) (q i)) :
    8 * K ≤ ∏ c ∈ S, liftV T X c := by
  obtain ⟨α, hα, hαm⟩ := exists_enum hS
  obtain ⟨ξ, hξ, hξm, hal⟩ := exists_aligned hT hα
  obtain ⟨hm, hpq⟩ := aligned_family (S := S) hα hξ hαm hξm hal
  have h1 := h _ _ hm hpq
  have h2 := lift_prod_sq hT hX hξ hξm hal
  rw [← prod_enum hS hα hαm]
  have hP0 : 0 ≤ ∏ x, liftV T X (α x) := Finset.prod_nonneg fun x _ => liftV_nonneg hX _
  have : (8 * K) ^ 2 ≤ (∏ x, liftV T X (α x)) ^ 2 := by nlinarith
  exact le_of_sq_le_sq' (by positivity) hP0 this

/-! ### The classes -/

theorem card_filter_ne (hT : T.card = 3) (c : ℕ) : 2 ≤ (T.filter fun e => c ≠ e).card := by
  have : T.filter (fun e => c ≠ e) = T.erase c := by
    ext e; simp [ne_comm, and_comm]
  rw [this]
  have := Finset.pred_card_le_card_erase (s := T) (a := c)
  omega

theorem lift_dom {f : ℝ} (hf : 0 ≤ f) (hT : T.card = 3) (h : Dominant S T X f) :
    Dominant S U (fun c _ => liftV T X c) (2 * f) := fun c hc d _ _ => by
  unfold liftV
  have hle : ∑ e ∈ T, (if c ≠ e then f else 0) ≤ ∑ e ∈ T, (if c ≠ e then X c e else 0) :=
    Finset.sum_le_sum fun e he => by
      split_ifs with hce
      · exact h c hc e he hce
      · exact le_refl 0
  refine le_trans ?_ hle
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hcard := card_filter_ne hT c
  have : (2 : ℝ) ≤ (T.filter fun e => c ≠ e).card := by exact_mod_cast hcard
  nlinarith

theorem lift_hex (hS : S.card = 3) (hT : T.card = 3) (hX : ∀ c d, 0 ≤ X c d) (hA : 0 ≤ A)
    (h : Hex S T X A) : Hex S U (fun c _ => liftV T X c) (2 * A) := fun p q hm _ => by
  have h1 := lift_prod hS hT hX (pow_nonneg hA 3) fun p q hm hpq => by
    rw [← pow_mul]; exact h p q hm hpq
  show (2 * A) ^ 6 ≤ ∏ i, liftV T X (p i)
  rw [hm.prod_left hS (liftV T X)]
  calc (2 * A) ^ 6 = (8 * A ^ 3) ^ 2 := by ring
    _ ≤ _ := pow_le_pow_left₀ (by positivity) h1 2

theorem lift_hasPot (hS : S.card = 3) (hT : T.card = 3) (hX : ∀ c d, 0 ≤ X c d) (hA : 0 < A)
    (h : Hex S T X A) : HasPot S U (fun c _ => liftV T X c) (2 * A) := by
  have h1 := lift_prod hS hT hX (pow_nonneg hA.le 3) fun p q hm hpq => by
    rw [← pow_mul]; exact h p q hm hpq
  set P := ∏ c ∈ S, liftV T X c with hP
  have hPpos : 0 < P := lt_of_lt_of_le (by positivity) h1
  have hpos : ∀ c ∈ S, 0 < liftV T X c := fun c hc => by
    rcases (liftV_nonneg hX (T := T) c).lt_or_eq with h' | h'
    · exact h'
    · exfalso
      have : P = 0 := Finset.prod_eq_zero hc h'.symm
      linarith
  set G := P ^ ((1 : ℝ) / 3) with hG
  have hGpos : 0 < G := Real.rpow_pos_of_pos hPpos _
  have hG3 : G ^ 3 = P := rpow_third_cube hPpos.le
  have h2A : 2 * A ≤ G := by
    refine le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) hGpos.le ?_
    rw [hG3]
    calc (2 * A) ^ 3 = 8 * A ^ 3 := by ring
      _ ≤ P := h1
  refine ⟨fun c => liftV T X c / G, fun _ => 1, fun c hc => div_pos (hpos c hc) hGpos,
    fun _ _ => one_pos, ?_, by simp, fun c hc d _ _ => ?_⟩
  · rw [Finset.prod_div_distrib, Finset.prod_const, hS, hG3, div_self hPpos.ne']
  · rw [mul_one, mul_div_assoc']
    rw [div_le_iff₀ hGpos]
    show 2 * A * liftV T X c ≤ liftV T X c * G
    rw [mul_comm (2 * A)]
    exact mul_le_mul_of_nonneg_left h2A (liftV_nonneg hX c)

/-- The family data of a parent family. -/
theorem lift_family (hT : T.card = 3) {p q : Fin 6 → ℕ} (hm : Matched S U p q) :
    ∃ (κ : Fin 6 → Fin 6) (α ξ : Fin 3 → ℕ), Function.Bijective κ ∧ Function.Injective α ∧
      Function.Injective ξ ∧ (∀ a, α a ∈ S) ∧ (∀ b, ξ b ∈ T) ∧ (∀ c a, ξ c = α a → a = c) ∧
      ∀ k, p (κ k) = α (offPair k).1 := by
  obtain ⟨α, β, hα, hβ, hαm, hβm, hab⟩ := hm
  obtain ⟨κ, hκb, hκ⟩ := matched_reindex hα hβ hab
  obtain ⟨ξ, hξ, hξm, hal⟩ := exists_aligned hT hα
  exact ⟨κ, α, ξ, hκb, hα, hξ, hαm, hξm, hal, fun k => (hκ k).1⟩

theorem lift_tb (hT : T.card = 3) (hX : ∀ c d, 0 ≤ X c d) {τ : ℝ}
    (h : TB S T X A τ) : TB S U (fun c _ => liftV T X c) (2 * A) τ := by
  intro p q hm _ i j k l hij hik hil hjk hjl hkl
  obtain ⟨κ, α, ξ, hκb, hα, hξ, hαm, hξm, hal, hκ⟩ := lift_family (U := U) hT hm
  obtain ⟨hcm, hcp⟩ := aligned_family (S := S) hα hξ hαm hξm hal
  have key := four_mix (M := fun z => X (α (offPair z).1) (ξ (offPair z).2)) (fun z => hX _ _)
    (by positivity : (0 : ℝ) ≤ τ ^ 2 * A ^ 6)
    (fun i j k l hij hik hil hjk hjl hkl => h _ _ hcm hcp i j k l hij hik hil hjk hjl hkl)
    Drow_ds (by norm_num : (0 : ℝ) ≤ 2) (p := fun k => liftV T X (α (offPair k).1))
    fun k => lift_vec hT hX hξ hξm hal k
  obtain ⟨i', rfl⟩ := hκb.2 i
  obtain ⟨j', rfl⟩ := hκb.2 j
  obtain ⟨k', rfl⟩ := hκb.2 k
  obtain ⟨l', rfl⟩ := hκb.2 l
  have k2 := key i' j' k' l' (fun e => hij (by rw [e])) (fun e => hik (by rw [e]))
    (fun e => hil (by rw [e])) (fun e => hjk (by rw [e])) (fun e => hjl (by rw [e]))
    (fun e => hkl (by rw [e]))
  show τ ^ 2 * (2 * A) ^ 6 ≤ liftV T X (p (κ i')) ^ 2 * liftV T X (p (κ j')) ^ 2
    * liftV T X (p (κ k')) * liftV T X (p (κ l'))
  rw [hκ, hκ, hκ, hκ]
  calc τ ^ 2 * (2 * A) ^ 6 = 2 ^ 6 * (τ ^ 2 * A ^ 6) := by ring
    _ ≤ _ := k2

theorem lift_hullC (hT : T.card = 3) (hX : ∀ c d, 0 ≤ X c d) (hA : 0 ≤ A)
    (h : HullC S T X A) : HullC S U (fun c _ => liftV T X c) (2 * A) := by
  refine ⟨fun p q hm _ => ?_, ?_⟩
  · obtain ⟨κ, α, ξ, hκb, hα, hξ, hαm, hξm, hal, hκ⟩ := lift_family (U := U) hT hm
    obtain ⟨hcm, hcp⟩ := aligned_family (S := S) hα hξ hαm hξm hal
    have h1 := ((h.1 _ _ hcm hcp).ds Drow_ds).smul (by norm_num : (0 : ℝ) ≤ 2)
    have h2 : HullV (2 * A) fun k => liftV T X (α (offPair k).1) :=
      h1.mono fun k => lift_vec hT hX hξ hξm hal k
    set e := Equiv.ofBijective κ hκb
    have h3 := h2.comp e.symm.injective
    refine h3.mono fun i => le_of_eq ?_
    show liftV T X (α (offPair (e.symm i)).1) = liftV T X (p i)
    rw [← hκ (e.symm i)]
    congr 2
    exact e.apply_symm_apply i
  · have := lift_dom (U := U) (by positivity) hT h.2
    refine fun c hc d hd hcd => le_trans (le_of_eq (by ring)) (this c hc d hd hcd)

theorem InBall.mask (h : InBall S T X A) (hX : ∀ c d, 0 ≤ X c d) :
    InBall S T (fun c d => if c ≠ d then X c d else 0) A :=
  h.mono hX fun c _ d _ hcd => by simp [hcd]

theorem lift_ball (hS : S.card = 3) (hT : T.card = 3) (hU : U.card = 3) (hX : ∀ c d, 0 ≤ X c d)
    (hA : 0 ≤ A) (h : InBall S T X A) : InBall S U (fun c _ => liftV T X c) (2 * A) :=
  ((h.mask hX).vBall_left hA hT fun c d => by split_ifs; exact hX _ _; exact le_refl 0).inBall_left
    hS hU

theorem lift_gain (hS : S.card = 3) (hT : T.card = 3) (hA : 0 ≤ A)
    (h : Gain1 S T X A) : Gain1 S U (fun c _ => liftV T X c) (2 * A) := by
  obtain ⟨t, Z, ht0, ht1, ⟨hZ0, hZD, hZB, hZT⟩, hXZ⟩ := h
  refine ⟨t, fun c _ => liftV T Z c / 2, ht0, ht1, ⟨fun c _ => div_nonneg (liftV_nonneg hZ0 c)
    (by norm_num), fun c hc d hd hcd => ?_, ?_, ?_⟩, fun c hc d _ _ => ?_⟩
  · have := lift_dom (U := U) (by norm_num) hT hZD c hc d hd hcd
    simp only at this ⊢
    linarith
  · intro α β hα hβ hαm _ _
    have hprod : 8 * (32 / 27) ≤ ∏ c ∈ S, liftV T Z c := by
      refine lift_prod hS hT hZ0 (by norm_num) fun p q hm hpq => ?_
      obtain ⟨α', β', hα', hβ', hαm', hβm', h1, h2, he⟩ := hm.prod_two hpq Z
      have b1 := hZB α' (fun a => β' (a + 1)) hα' (fun x y h => add_right_cancel (hβ' h)) hαm'
        (fun a => hβm' _) h1
      have b2 := hZB α' (fun a => β' (a + 2)) hα' (fun x y h => add_right_cancel (hβ' h)) hαm'
        (fun a => hβm' _) h2
      rw [he]
      rw [one_pow, mul_one] at b1 b2
      exact le_trans (le_of_eq (by norm_num)) (mul_le_mul b1 b2 (by norm_num)
        ((by norm_num : (0 : ℝ) ≤ 32 / 27).trans b1))
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      prod_enum hS hα hαm (liftV T Z), one_pow, mul_one, le_div_iff₀ (by norm_num)]
    linarith
  · have := (lift_tb (U := U) hT hZ0 hZT).div (by norm_num : (0 : ℝ) < 2 * 1)
    simpa using this
  · have hle : ∑ e ∈ T, (if c ≠ e then A * ((1 - t) + t * Z c e) else 0) ≤ liftV T X c :=
      Finset.sum_le_sum fun e he => by
        split_ifs with hce
        · exact hXZ c hc e he hce
        · exact le_refl 0
    have hn := card_filter_ne hT c
    have hsum : ∑ e ∈ T, (if c ≠ e then A * ((1 - t) + t * Z c e) else 0)
        = ((T.filter fun e => c ≠ e).card : ℝ) * (A * (1 - t)) + A * t * liftV T Z c := by
      unfold liftV
      rw [← Finset.sum_filter, ← Finset.sum_filter, Finset.mul_sum, ← nsmul_eq_mul,
        ← Finset.sum_const, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun e _ => by ring
    have hn' : (2 : ℝ) ≤ (T.filter fun e => c ≠ e).card := by exact_mod_cast hn
    have hA1 : 0 ≤ A * (1 - t) := mul_nonneg hA (by linarith)
    show 2 * A * ((1 - t) + t * (liftV T Z c / 2)) ≤ liftV T X c
    calc 2 * A * ((1 - t) + t * (liftV T Z c / 2))
        = 2 * (A * (1 - t)) + A * t * liftV T Z c := by ring
      _ ≤ ((T.filter fun e => c ≠ e).card : ℝ) * (A * (1 - t)) + A * t * liftV T Z c := by
          nlinarith
      _ = _ := hsum.symm
      _ ≤ _ := hle

/-! ### Tags -/

/-- The lifted tag: the same demands, and the rank-one bound. -/
def STag.lift (t : STag) : STag := ⟨{ t.base with mb := true }, t.ball, t.gain⟩

/-- **A lift keeps the class of a tag**, with the constant doubled, and gains the rank-one
bound. -/
theorem scls_lift {t : STag} (hS : S.card = 3) (hT : T.card = 3) (hU : U.card = 3)
    (hX : ∀ c d, 0 ≤ X c d) (hA : 0 < A) (h : scls t S T X A) :
    scls t.lift S U (fun c _ => liftV T X c) (2 * A) := by
  obtain ⟨⟨hhex, -, htb, hfl, hhull⟩, hball, hgain⟩ := h
  refine ⟨⟨lift_hex hS hT hX hA.le hhex, fun _ => lift_hasPot hS hT hX hA hhex, lift_tb hT hX htb,
    ?_, fun hh => lift_hullC hT hX hA.le (hhull hh)⟩, fun hb => lift_ball hS hT hU hX hA.le (hball hb),
    fun hg => lift_gain hS hT hA.le (hgain hg)⟩
  have := lift_dom (U := U) (mul_nonneg t.base.fl0 hA.le) hT hfl
  exact fun c hc d hd hcd => le_trans (le_of_eq (by simp [STag.lift]; ring)) (this c hc d hd hcd)

end Outerplanar
