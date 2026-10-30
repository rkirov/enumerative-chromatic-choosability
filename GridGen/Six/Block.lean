/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Six.Peel

/-!
# Height six at `k = 6`: the marginal-block lemma with the sharp side factors

`GridGen/Five/K5/Block.lean` with six rows and lists of at least five colours (Lemma B of
`ai_research_notes/H4_K5_REVIEW_2026-10-24.md`; the side factors as re-derived in
`H6_K6_REVIEW_2026-10-29.md` §3).

**Side factors** (`step_frac`). For a path of `L` rows with lists of at least five colours, the
share of its proper colourings whose first row is a given colour is at most `p_L`, with
`p_1 = 1/5` and `p_{L+1} = 1/(5 - 4 p_L)`: `1/5, 5/21, 21/85, 85/341, 341/1365`. So the colourings
that avoid a given colour in their first row are at least `f(L) = 1 - p_L` of all:
`4/5, 16/21, 64/85, 256/341, 1024/1365`.

**Blocks** (`blk_bound6`, in `GridGen/Six/Pins.lean`). For a block of one to three consecutive
rows `a..b` and a proper colouring `τ` of it, the columns extending `τ` are a product of a left
part (rows before `a`, last row avoiding `τ_a`) and a right part (rows after `b`, first row
avoiding `τ_b`), so their number lies between `f(a) f(5-b) c` and `c` for a constant `c`
(`fib*`). The block has at least `M = 5 · 4^{len-1}` proper colourings; with the uniform weights
within the factor `10000/9483` (`rowV6_ratio`), the abstract `block_core6` bounds the weight of
the columns whose block lies in a set of at most `m` colourings by `m/(m + ρ ℓ (M - m))`,
`ρ = 9483/10000`.
-/

namespace GridGen.Six

open Finset

/-! ### The side factors -/

/-- The fibre of the first entry of a prepended product. -/
theorem card_prepend_fib {β : Type*} [DecidableEq β] (Y : Finset ℕ) (R : Finset β) (f : β → ℕ)
    (Q : β → Prop) [DecidablePred Q] (x : ℕ) :
    (((Y ×ˢ R).filter (fun q => q.1 ≠ f q.2)).filter (fun q => q.1 = x ∧ Q q.2)).card
      = if x ∈ Y then (R.filter (fun r => f r ≠ x ∧ Q r)).card else 0 := by
  rw [Finset.filter_filter]
  have h := Lookback.card_filter_prod Y R (fun a => a = x) (fun a r => a ≠ f r ∧ Q r)
  have e : (Y ×ˢ R).filter (fun q => q.1 ≠ f q.2 ∧ q.1 = x ∧ Q q.2)
      = (Y ×ˢ R).filter (fun q => q.1 = x ∧ (q.1 ≠ f q.2 ∧ Q q.2)) :=
    Finset.filter_congr (fun q _ => by tauto)
  rw [e, h]
  split_ifs with hx
  · have : Y.filter (fun a => a = x) = {x} := by
      ext a; simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · exact fun h => h.2
      · rintro rfl; exact ⟨hx, rfl⟩
    rw [this, Finset.sum_singleton]
    congr 1
    exact Finset.filter_congr (fun r _ => by constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨Ne.symm h1, h2⟩)
  · have : Y.filter (fun a => a = x) = ∅ := by
      ext a; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      rintro ha rfl; exact hx ha
    rw [this, Finset.sum_empty]

/-- **One step of the side recursion.** -/
theorem step_frac {β : Type*} [DecidableEq β] (Y : Finset ℕ) (R : Finset β) (f : β → ℕ)
    {p : ℝ} (hp1 : p ≤ 1) (hY : 5 ≤ Y.card)
    (hR : ∀ y, ((R.filter (fun r => f r = y)).card : ℝ) ≤ p * R.card) (x : ℕ) :
    (5 - 4 * p) * ((((Y ×ˢ R).filter (fun q => q.1 ≠ f q.2)).filter (fun q => q.1 = x)).card : ℝ)
      ≤ ((Y ×ˢ R).filter (fun q => q.1 ≠ f q.2)).card := by
  have hfib := card_prepend_fib Y R f (fun _ => True) x
  simp only [and_true] at hfib
  have hN := Lookback.card_prepend Y R f
  have hsum : ((R.filter (fun r => f r ∈ Y)).card : ℝ)
      = ∑ y ∈ Y, ((R.filter (fun r => f r = y)).card : ℝ) := by
    have hm := Finset.card_eq_sum_card_fiberwise (s := R.filter (fun r => f r ∈ Y)) (t := Y) (f := f)
      (fun r hr => (Finset.mem_filter.mp hr).2)
    rw [hm]
    push_cast
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [Finset.filter_filter]
    congr 2
    exact Finset.filter_congr (fun r _ => ⟨fun h => h.2, fun h => ⟨h ▸ hy, h⟩⟩)
  have hNR : (((Y ×ˢ R).filter (fun q => q.1 ≠ f q.2)).card : ℝ)
      = Y.card * R.card - ∑ y ∈ Y, ((R.filter (fun r => f r = y)).card : ℝ) := by
    rw [← hsum]; exact_mod_cast hN
  have hY' : (5 : ℝ) ≤ Y.card := by exact_mod_cast hY
  have hR0 : (0 : ℝ) ≤ R.card := Nat.cast_nonneg _
  rw [hfib]
  split_ifs with hx
  · -- `x ∈ Y`
    set a : ℝ := ((R.filter (fun r => f r = x)).card : ℝ) with ha
    have hc : ((R.filter (fun r => f r ≠ x)).card : ℝ) = R.card - a := by
      have := Finset.card_filter_add_card_filter_not (s := R) (fun r => f r = x)
      rw [ha]
      have e : R.filter (fun r => ¬ f r = x) = R.filter (fun r => f r ≠ x) := rfl
      rw [e] at this
      have : ((R.filter (fun r => f r = x)).card : ℝ) + (R.filter (fun r => f r ≠ x)).card
          = R.card := by exact_mod_cast this
      linarith
    have hsplit : ∑ y ∈ Y, ((R.filter (fun r => f r = y)).card : ℝ)
        = a + ∑ y ∈ Y.erase x, ((R.filter (fun r => f r = y)).card : ℝ) := by
      rw [← Finset.add_sum_erase Y _ hx]
    have hrest : ∑ y ∈ Y.erase x, ((R.filter (fun r => f r = y)).card : ℝ)
        ≤ ((Y.card : ℝ) - 1) * (p * R.card) := by
      calc ∑ y ∈ Y.erase x, ((R.filter (fun r => f r = y)).card : ℝ)
          ≤ ∑ _y ∈ Y.erase x, p * R.card := Finset.sum_le_sum (fun y _ => hR y)
        _ = ((Y.card : ℝ) - 1) * (p * R.card) := by
          rw [Finset.sum_const, Finset.card_erase_of_mem hx, nsmul_eq_mul]
          push_cast [Nat.cast_sub (Finset.card_pos.mpr ⟨x, hx⟩)]
          ring
    have ha0 : 0 ≤ a := Nat.cast_nonneg _
    have haR : a ≤ R.card := by
      rw [ha]; exact_mod_cast Finset.card_filter_le _ _
    rw [hc, hNR, hsplit]
    have h1 : 0 ≤ ((Y.card : ℝ) - 5) * (1 - p) * R.card :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) hR0
    have h2 : 0 ≤ 4 * a * (1 - p) := mul_nonneg (mul_nonneg (by norm_num) ha0) (by linarith)
    nlinarith
  · push_cast
    rw [mul_zero]
    exact Nat.cast_nonneg _

/-- The first-row fraction of a single list. -/
theorem frac_one (Z : Finset ℕ) (hZ : 5 ≤ Z.card) (y : ℕ) :
    ((Z.filter (fun r => id r = y)).card : ℝ) ≤ 1 / 5 * Z.card := by
  have h1 : (Z.filter (fun r => id r = y)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter, id] at ha hb
    rw [ha.2, hb.2]
  have h1' : ((Z.filter (fun r => id r = y)).card : ℝ) ≤ 1 := by exact_mod_cast h1
  have hZ' : (5 : ℝ) ≤ Z.card := by exact_mod_cast hZ
  linarith

/-- The first-row fraction of two rows: `5/21`. -/
theorem frac_two {Y Z : Finset ℕ} (hY : 5 ≤ Y.card) (hZ : 5 ≤ Z.card) (x : ℕ) :
    (((Four.sts2 Y Z).filter (fun q => q.1 = x)).card : ℝ) ≤ 5 / 21 * (Four.sts2 Y Z).card := by
  have h := step_frac Y Z id (p := 1 / 5) (by norm_num) hY (frac_one Z hZ) x
  simp only [id] at h
  unfold Four.sts2
  linarith

/-- The first-row fraction of three rows: `21/85`. -/
theorem frac_three {X Y Z : Finset ℕ} (hX : 5 ≤ X.card) (hY : 5 ≤ Y.card) (hZ : 5 ≤ Z.card)
    (x : ℕ) :
    (((Four.sts3 X Y Z).filter (fun q => q.1 = x)).card : ℝ) ≤ 21 / 85 * (Four.sts3 X Y Z).card := by
  have h := step_frac X (Four.sts2 Y Z) Prod.fst (p := 5 / 21) (by norm_num) hX
    (frac_two hY hZ) x
  unfold Four.sts3
  linarith

/-- The first-row fraction of four rows: `85/341`. -/
theorem frac_four {W X Y Z : Finset ℕ} (hW : 5 ≤ W.card) (hX : 5 ≤ X.card) (hY : 5 ≤ Y.card)
    (hZ : 5 ≤ Z.card) (x : ℕ) :
    (((Four.sts W X Y Z).filter (fun q => q.1 = x)).card : ℝ)
      ≤ 85 / 341 * (Four.sts W X Y Z).card := by
  have h := step_frac W (Four.sts3 X Y Z) Prod.fst (p := 21 / 85) (by norm_num) hW
    (frac_three hX hY hZ) x
  unfold Four.sts
  linarith

/-- The first-row fraction of five rows: `341/1365`. -/
theorem frac_five {V W X Y Z : Finset ℕ} (hV : 5 ≤ V.card) (hW : 5 ≤ W.card) (hX : 5 ≤ X.card)
    (hY : 5 ≤ Y.card) (hZ : 5 ≤ Z.card) (x : ℕ) :
    (((Five.sts V W X Y Z).filter (fun q => q.1 = x)).card : ℝ)
      ≤ 341 / 1365 * (Five.sts V W X Y Z).card := by
  have h := step_frac V (Four.sts W X Y Z) Prod.fst (p := 85 / 341) (by norm_num) hV
    (frac_four hW hX hY hZ) x
  unfold Five.sts
  linarith

/-- Avoiding a colour in the first row: at least `1 - p` of all. -/
theorem avoid_of_frac {β : Type*} (S : Finset β) (g : β → ℕ) {p : ℝ}
    (h : ∀ x, ((S.filter (fun q => g q = x)).card : ℝ) ≤ p * S.card) (x : ℕ) :
    (1 - p) * S.card ≤ ((S.filter (fun q => g q ≠ x)).card : ℝ) ∧
      ((S.filter (fun q => g q ≠ x)).card : ℝ) ≤ S.card := by
  have := Finset.card_filter_add_card_filter_not (s := S) (fun q => g q = x)
  have e : ((S.filter (fun q => g q = x)).card : ℝ) + (S.filter (fun q => g q ≠ x)).card
      = S.card := by exact_mod_cast this
  have := h x
  constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) (S.filter (fun q => g q = x)).card]

/-! ### The abstract block inequality (`GridGen/Four/Pins5.lean`, any state type) -/

/-- **The block inequality, abstractly** (`GridGen.Four.block_core` for any type of states). -/
theorem block_core6 {σ α : Type*} [DecidableEq α] (Ω : Finset σ) (u : σ → ℝ) (π : σ → α)
    (F T : Finset α) (hF : ∀ t ∈ Ω, π t ∈ F) {g c ℓ ρ : ℝ} (hρ : 0 ≤ ρ) (hℓ : 0 ≤ ℓ)
    (hc : 0 ≤ c) (hg : 0 ≤ g) (hu : ∀ t ∈ Ω, ρ * g ≤ u t ∧ u t ≤ g)
    (hN : ∀ τ ∈ F, ℓ * c ≤ ((Ω.filter (fun t => π t = τ)).card : ℝ) ∧
      ((Ω.filter (fun t => π t = τ)).card : ℝ) ≤ c)
    {m M : ℕ} (hm : (F ∩ T).card ≤ m) (hM : M ≤ F.card) :
    ((m : ℝ) + ρ * ℓ * ((M : ℝ) - m)) * ∑ t ∈ Ω.filter (fun t => π t ∈ T), u t
      ≤ m * ∑ t ∈ Ω, u t := by
  have hu0 : ∀ t ∈ Ω, 0 ≤ u t := fun t ht => le_trans (mul_nonneg hρ hg) (hu t ht).1
  set SE := ∑ t ∈ Ω.filter (fun t => π t ∈ T), u t with hSE
  set SC := ∑ t ∈ Ω.filter (fun t => ¬ π t ∈ T), u t with hSC
  have hW : ∑ t ∈ Ω, u t = SE + SC := (Finset.sum_filter_add_sum_filter_not Ω _ u).symm
  have hSE0 : 0 ≤ SE := Finset.sum_nonneg fun t ht => hu0 t (Finset.mem_filter.mp ht).1
  have hSC0 : 0 ≤ SC := Finset.sum_nonneg fun t ht => hu0 t (Finset.mem_filter.mp ht).1
  -- the fibre counts
  have cE : ((Ω.filter (fun t => π t ∈ T)).card : ℝ)
      = ∑ τ ∈ F ∩ T, ((Ω.filter (fun t => π t = τ)).card : ℝ) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := π) (t := F ∩ T) (fun t ht => by
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp ht
      exact Finset.mem_inter.mpr ⟨hF t h1, h2⟩)]
    push_cast
    refine Finset.sum_congr rfl (fun τ hτ => ?_)
    rw [Finset.filter_filter]
    congr 2
    ext t; simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨h1, h3 ▸ (Finset.mem_inter.mp hτ).2, h3⟩
  have cC : ((Ω.filter (fun t => ¬ π t ∈ T)).card : ℝ)
      = ∑ τ ∈ F \ T, ((Ω.filter (fun t => π t = τ)).card : ℝ) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := π) (t := F \ T) (fun t ht => by
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp ht
      exact Finset.mem_sdiff.mpr ⟨hF t h1, h2⟩)]
    push_cast
    refine Finset.sum_congr rfl (fun τ hτ => ?_)
    rw [Finset.filter_filter]
    congr 2
    ext t; simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨h1, h3 ▸ (Finset.mem_sdiff.mp hτ).2, h3⟩
  have hNE : ((Ω.filter (fun t => π t ∈ T)).card : ℝ) ≤ (F ∩ T).card * c := by
    rw [cE]
    calc ∑ τ ∈ F ∩ T, ((Ω.filter (fun t => π t = τ)).card : ℝ)
        ≤ ∑ τ ∈ F ∩ T, c := Finset.sum_le_sum (fun τ hτ =>
          (hN τ (Finset.mem_inter.mp hτ).1).2)
      _ = (F ∩ T).card * c := by rw [Finset.sum_const, nsmul_eq_mul]
  have hNC : ((F \ T).card : ℝ) * (ℓ * c) ≤ ((Ω.filter (fun t => ¬ π t ∈ T)).card : ℝ) := by
    rw [cC]
    calc ((F \ T).card : ℝ) * (ℓ * c) = ∑ τ ∈ F \ T, ℓ * c := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum (fun τ hτ => (hN τ (Finset.mem_sdiff.mp hτ).1).1)
  -- the weights
  have bE : SE ≤ g * (Ω.filter (fun t => π t ∈ T)).card := by
    rw [hSE, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum]
    exact Finset.sum_le_sum (fun t ht => by
      have := (hu t (Finset.mem_filter.mp ht).1).2; push_cast; linarith)
  have bC : ρ * g * (Ω.filter (fun t => ¬ π t ∈ T)).card ≤ SC := by
    rw [hSC, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum]
    exact Finset.sum_le_sum (fun t ht => by
      have := (hu t (Finset.mem_filter.mp ht).1).1; push_cast; linarith)
  have hFT : ((F \ T).card : ℝ) = F.card - (F ∩ T).card := by
    have := Finset.card_sdiff_add_card_inter F T
    have : ((F \ T).card : ℝ) + (F ∩ T).card = F.card := by exact_mod_cast this
    linarith
  have hm' : ((F ∩ T).card : ℝ) ≤ m := by exact_mod_cast hm
  have hM' : (M : ℝ) ≤ F.card := by exact_mod_cast hM
  rw [hW]
  rcases le_or_gt (M : ℝ) m with hMm | hMm
  · have : ρ * ℓ * ((M : ℝ) - m) * SE ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hρ hℓ)
        (by linarith)) hSE0
    have : 0 ≤ (m : ℝ) * SC := mul_nonneg (Nat.cast_nonneg m) hSC0
    nlinarith
  · set t' : ℝ := ((F ∩ T).card : ℝ)
    have hK : 0 ≤ ρ * ℓ * g * c := mul_nonneg (mul_nonneg (mul_nonneg hρ hℓ) hg) hc
    have i1 : ρ * ℓ * ((M : ℝ) - m) * SE ≤ ρ * ℓ * ((M : ℝ) - m) * (g * (t' * c)) := by
      have : SE ≤ g * (t' * c) := bE.trans (mul_le_mul_of_nonneg_left hNE hg)
      exact mul_le_mul_of_nonneg_left this (mul_nonneg (mul_nonneg hρ hℓ) (by linarith))
    have i2 : ρ * g * (((F.card : ℝ) - t') * (ℓ * c)) ≤ SC := by
      have : ((F.card : ℝ) - t') * (ℓ * c) ≤ ((Ω.filter (fun t => ¬ π t ∈ T)).card : ℝ) := by
        rw [← hFT]; exact hNC
      exact le_trans (mul_le_mul_of_nonneg_left this (mul_nonneg hρ hg)) bC
    have i3 : ((M : ℝ) - m) * t' ≤ m * ((F.card : ℝ) - t') := by nlinarith
    have i4 : ρ * ℓ * ((M : ℝ) - m) * (g * (t' * c)) ≤ m * (ρ * g * (((F.card : ℝ) - t') * (ℓ * c))) := by
      have := mul_le_mul_of_nonneg_left i3 hK
      nlinarith
    have i5 : (m : ℝ) * (ρ * g * (((F.card : ℝ) - t') * (ℓ * c))) ≤ m * SC :=
      mul_le_mul_of_nonneg_left i2 (Nat.cast_nonneg m)
    nlinarith

/-! ### Products -/

theorem prod_bounds {a A x b B y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hx : a * A ≤ x ∧ x ≤ A) (hy : b * B ≤ y ∧ y ≤ B) :
    a * b * (A * B) ≤ x * y ∧ x * y ≤ A * B := by
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨h3, h4⟩ := hy
  have hx0 : 0 ≤ x := le_trans (mul_nonneg ha hA) h1
  have hy0 : 0 ≤ y := le_trans (mul_nonneg hb hB) h3
  constructor
  · calc a * b * (A * B) = (a * A) * (b * B) := by ring
      _ ≤ x * y := mul_le_mul h1 h3 (mul_nonneg hb hB) hx0
  · exact mul_le_mul h2 h4 hy0 hA


/-! ### Fibres of blocks: left part times right part -/

section fibres

variable {X₁ X₂ X₃ X₄ X₅ X₆ : Finset ℕ}

/-- The membership simp set for the bijections below. -/
macro "fibsimp6" : tactic => `(tactic| simp only [Finset.coe_filter, Finset.coe_product,
  Set.mem_ofPred_eq, Set.mem_prod, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
  Finset.mem_erase, GridGen.Six.mem_sts, GridGen.Five.mem_sts, Four.mem_sts, Four.mem_sts3,
  Four.mem_sts2, GridGen.Six.r1, GridGen.Six.r2, GridGen.Six.r3, GridGen.Six.r4,
  GridGen.Six.r5, GridGen.Six.r6, GridGen.Five.r1, GridGen.Five.r2, GridGen.Five.r3,
  GridGen.Five.r4, GridGen.Five.r5, Four.r1, Four.r2, Four.r3, Four.r4, Prod.mk.injEq] at *)

theorem fib01 {x : ℕ} (hx : x ∈ X₁) :
    ((sts X₁ X₂ X₃ X₄ X₅ X₆).filter (fun t => r1 t = x)).card
      = ((Five.sts X₂ X₃ X₄ X₅ X₆).filter (fun u => u.1 ≠ x)).card := by
  refine Finset.card_nbij' (fun t => t.2) (fun u => (x, u)) ?_ ?_ ?_ ?_
  · rintro ⟨a, b, c, d, e, f⟩ ht; fibsimp6; grind
  · rintro ⟨b, c, d, e, f⟩ ht; fibsimp6; grind
  · rintro ⟨a, b, c, d, e, f⟩ ht; fibsimp6; grind
  · rintro ⟨b, c, d, e, f⟩ ht; rfl

theorem fib02 {x y : ℕ} (hx : x ∈ X₁) (hy : y ∈ X₂) (hxy : x ≠ y) :
    ((sts X₁ X₂ X₃ X₄ X₅ X₆).filter (fun t => (r1 t, r2 t) = (x, y))).card
      = ((Four.sts X₃ X₄ X₅ X₆).filter (fun v => v.1 ≠ y)).card := by
  refine Finset.card_nbij' (fun t => t.2.2) (fun v => (x, y, v)) ?_ ?_ ?_ ?_
  · rintro ⟨a, b, c, d, e, f⟩ ht; fibsimp6; grind
  · rintro ⟨c, d, e, f⟩ ht; fibsimp6; grind
  · rintro ⟨a, b, c, d, e, f⟩ ht; fibsimp6; grind
  · rintro ⟨c, d, e, f⟩ ht; rfl

theorem fib03 {x y z : ℕ} (hx : x ∈ X₁) (hy : y ∈ X₂) (hz : z ∈ X₃) (hxy : x ≠ y) (hyz : y ≠ z) :
    ((sts X₁ X₂ X₃ X₄ X₅ X₆).filter (fun t => (r1 t, r2 t, r3 t) = (x, y, z))).card
      = ((Four.sts3 X₄ X₅ X₆).filter (fun v => v.1 ≠ z)).card := by
  refine Finset.card_nbij' (fun t => t.2.2.2) (fun v => (x, y, z, v)) ?_ ?_ ?_ ?_
  · rintro ⟨a, b, c, d, e, f⟩ ht; fibsimp6; grind
  · rintro ⟨d, e, f⟩ ht; fibsimp6; grind
  · rintro ⟨a, b, c, d, e, f⟩ ht; fibsimp6; grind
  · rintro ⟨d, e, f⟩ ht; rfl

theorem fib11 {x : ℕ} (hx : x ∈ X₂) :
    ((sts X₁ X₂ X₃ X₄ X₅ X₆).filter (fun t => r2 t = x)).card
      = ((X₁.erase x) ×ˢ (Four.sts X₃ X₄ X₅ X₆).filter (fun v => v.1 ≠ x)).card := by
  refine Finset.card_nbij' (fun t => (t.1, t.2.2)) (fun p => (p.1, x, p.2)) ?_ ?_ ?_ ?_
  · rintro ⟨a, b, c, d, e, f⟩ ht; fibsimp6; grind
  · rintro ⟨a, c, d, e, f⟩ ht; fibsimp6; grind
  · rintro ⟨a, b, c, d, e, f⟩ ht; fibsimp6; grind
  · rintro ⟨a, c, d, e, f⟩ ht; rfl

theorem fib12 {x y : ℕ} (hx : x ∈ X₂) (hy : y ∈ X₃) (hxy : x ≠ y) :
    ((sts X₁ X₂ X₃ X₄ X₅ X₆).filter (fun t => (r2 t, r3 t) = (x, y))).card
      = ((X₁.erase x) ×ˢ (Four.sts3 X₄ X₅ X₆).filter (fun v => v.1 ≠ y)).card := by
  refine Finset.card_nbij' (fun t => (t.1, t.2.2.2)) (fun p => (p.1, x, y, p.2)) ?_ ?_ ?_ ?_
  · rintro ⟨a, b, c, d, e, f⟩ ht; fibsimp6; grind
  · rintro ⟨a, d, e, f⟩ ht; fibsimp6; grind
  · rintro ⟨a, b, c, d, e, f⟩ ht; fibsimp6; grind
  · rintro ⟨a, d, e, f⟩ ht; rfl

theorem fib13 {x y z : ℕ} (hx : x ∈ X₂) (hy : y ∈ X₃) (hz : z ∈ X₄) (hxy : x ≠ y) (hyz : y ≠ z) :
    ((sts X₁ X₂ X₃ X₄ X₅ X₆).filter (fun t => (r2 t, r3 t, r4 t) = (x, y, z))).card
      = ((X₁.erase x) ×ˢ (Four.sts2 X₅ X₆).filter (fun v => v.1 ≠ z)).card := by
  refine Finset.card_nbij' (fun t => (t.1, t.2.2.2.2)) (fun p => (p.1, x, y, z, p.2)) ?_ ?_ ?_ ?_
  · rintro ⟨a, b, c, d, e, f⟩ ht; fibsimp6; grind
  · rintro ⟨a, e, f⟩ ht; fibsimp6; grind
  · rintro ⟨a, b, c, d, e, f⟩ ht; fibsimp6; grind
  · rintro ⟨a, e, f⟩ ht; rfl

theorem fib21 {x : ℕ} (hx : x ∈ X₃) :
    ((sts X₁ X₂ X₃ X₄ X₅ X₆).filter (fun t => r3 t = x)).card
      = ((Four.sts2 X₁ X₂).filter (fun p => p.2 ≠ x) ×ˢ
          (Four.sts3 X₄ X₅ X₆).filter (fun v => v.1 ≠ x)).card := by
  refine Finset.card_nbij' (fun t => ((t.1, t.2.1), t.2.2.2)) (fun p => (p.1.1, p.1.2, x, p.2))
    ?_ ?_ ?_ ?_
  · rintro ⟨a, b, c, d, e, f⟩ ht; fibsimp6; grind
  · rintro ⟨⟨a, b⟩, d, e, f⟩ ht; fibsimp6; grind
  · rintro ⟨a, b, c, d, e, f⟩ ht; fibsimp6; grind
  · rintro ⟨⟨a, b⟩, d, e, f⟩ ht; rfl

theorem fib22 {x y : ℕ} (hx : x ∈ X₃) (hy : y ∈ X₄) (hxy : x ≠ y) :
    ((sts X₁ X₂ X₃ X₄ X₅ X₆).filter (fun t => (r3 t, r4 t) = (x, y))).card
      = ((Four.sts2 X₁ X₂).filter (fun p => p.2 ≠ x) ×ˢ
          (Four.sts2 X₅ X₆).filter (fun v => v.1 ≠ y)).card := by
  refine Finset.card_nbij' (fun t => ((t.1, t.2.1), t.2.2.2.2))
    (fun p => (p.1.1, p.1.2, x, y, p.2)) ?_ ?_ ?_ ?_
  · rintro ⟨a, b, c, d, e, f⟩ ht; fibsimp6; grind
  · rintro ⟨⟨a, b⟩, e, f⟩ ht; fibsimp6; grind
  · rintro ⟨a, b, c, d, e, f⟩ ht; fibsimp6; grind
  · rintro ⟨⟨a, b⟩, e, f⟩ ht; rfl

end fibres

/-! ### Side bounds -/

theorem side1 {X : Finset ℕ} (hX : 5 ≤ X.card) (x : ℕ) :
    4 / 5 * (X.card : ℝ) ≤ ((X.erase x).card : ℝ) ∧ ((X.erase x).card : ℝ) ≤ X.card := by
  have h1 := Finset.pred_card_le_card_erase (s := X) (a := x)
  have h2 := Finset.card_erase_le (s := X) (a := x)
  have hX' : (5 : ℝ) ≤ X.card := by exact_mod_cast hX
  have h1' : (X.card : ℝ) - 1 ≤ (X.erase x).card := by
    have h3 : ((X.card - 1 : ℕ) : ℝ) ≤ (X.erase x).card := by exact_mod_cast h1
    push_cast [Nat.cast_sub (by omega : 1 ≤ X.card)] at h3
    exact h3
  constructor
  · linarith
  · exact_mod_cast h2

theorem side2 {Y Z : Finset ℕ} (hY : 5 ≤ Y.card) (hZ : 5 ≤ Z.card) (x : ℕ) :
    16 / 21 * ((Four.sts2 Y Z).card : ℝ) ≤ (((Four.sts2 Y Z).filter (fun q => q.1 ≠ x)).card : ℝ) ∧
      (((Four.sts2 Y Z).filter (fun q => q.1 ≠ x)).card : ℝ) ≤ (Four.sts2 Y Z).card := by
  have h := avoid_of_frac (Four.sts2 Y Z) Prod.fst (fun x => frac_two hY hZ x) x
  constructor <;> linarith [h.1, h.2]

theorem side3 {X Y Z : Finset ℕ} (hX : 5 ≤ X.card) (hY : 5 ≤ Y.card) (hZ : 5 ≤ Z.card) (x : ℕ) :
    64 / 85 * ((Four.sts3 X Y Z).card : ℝ)
        ≤ (((Four.sts3 X Y Z).filter (fun q => q.1 ≠ x)).card : ℝ) ∧
      (((Four.sts3 X Y Z).filter (fun q => q.1 ≠ x)).card : ℝ) ≤ (Four.sts3 X Y Z).card := by
  have h := avoid_of_frac (Four.sts3 X Y Z) Prod.fst (fun x => frac_three hX hY hZ x) x
  constructor <;> linarith [h.1, h.2]

theorem side4 {W X Y Z : Finset ℕ} (hW : 5 ≤ W.card) (hX : 5 ≤ X.card) (hY : 5 ≤ Y.card)
    (hZ : 5 ≤ Z.card) (x : ℕ) :
    256 / 341 * ((Four.sts W X Y Z).card : ℝ)
        ≤ (((Four.sts W X Y Z).filter (fun q => q.1 ≠ x)).card : ℝ) ∧
      (((Four.sts W X Y Z).filter (fun q => q.1 ≠ x)).card : ℝ) ≤ (Four.sts W X Y Z).card := by
  have h := avoid_of_frac (Four.sts W X Y Z) Prod.fst (fun x => frac_four hW hX hY hZ x) x
  constructor <;> linarith [h.1, h.2]

theorem side5 {V W X Y Z : Finset ℕ} (hV : 5 ≤ V.card) (hW : 5 ≤ W.card) (hX : 5 ≤ X.card)
    (hY : 5 ≤ Y.card) (hZ : 5 ≤ Z.card) (x : ℕ) :
    1024 / 1365 * ((Five.sts V W X Y Z).card : ℝ)
        ≤ (((Five.sts V W X Y Z).filter (fun q => q.1 ≠ x)).card : ℝ) ∧
      (((Five.sts V W X Y Z).filter (fun q => q.1 ≠ x)).card : ℝ) ≤ (Five.sts V W X Y Z).card := by
  have h := avoid_of_frac (Five.sts V W X Y Z) Prod.fst (fun x => frac_five hV hW hX hY hZ x) x
  constructor <;> linarith [h.1, h.2]

theorem sts2_swap_card (Y Z : Finset ℕ) (P : ℕ × ℕ → Prop) [DecidablePred P] :
    ((Four.sts2 Y Z).filter P).card = ((Four.sts2 Z Y).filter (fun q => P (q.2, q.1))).card := by
  refine Finset.card_nbij' (fun q => (q.2, q.1)) (fun q => (q.2, q.1)) ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ h; fibsimp6; grind
  · rintro ⟨a, b⟩ h; fibsimp6; grind
  · rintro ⟨a, b⟩ h; rfl
  · rintro ⟨a, b⟩ h; rfl

theorem side2last {Y Z : Finset ℕ} (hY : 5 ≤ Y.card) (hZ : 5 ≤ Z.card) (x : ℕ) :
    16 / 21 * ((Four.sts2 Y Z).card : ℝ) ≤ (((Four.sts2 Y Z).filter (fun q => q.2 ≠ x)).card : ℝ) ∧
      (((Four.sts2 Y Z).filter (fun q => q.2 ≠ x)).card : ℝ) ≤ (Four.sts2 Y Z).card := by
  have e1 := sts2_swap_card Y Z (fun q => q.2 ≠ x)
  have e2 := sts2_swap_card Y Z (fun _ => True)
  simp only [Finset.filter_true] at e2
  rw [e1, e2]
  exact side2 hZ hY x

theorem twenty_le {X Y : Finset ℕ} (hX : 5 ≤ X.card) (hY : 5 ≤ Y.card) :
    20 ≤ (Four.sts2 X Y).card := by
  have h := Four.card_sts2 X Y
  have h1 : ((X ∩ Y).card : ℤ) ≤ Y.card := by exact_mod_cast card_le_card inter_subset_right
  have hX' : (5 : ℤ) ≤ X.card := by exact_mod_cast hX
  have hY' : (5 : ℤ) ≤ Y.card := by exact_mod_cast hY
  have : (20 : ℤ) ≤ (Four.sts2 X Y).card := by nlinarith
  exact_mod_cast this

theorem eighty_le {X Y Z : Finset ℕ} (hX : 5 ≤ X.card) (hY : 5 ≤ Y.card) (hZ : 5 ≤ Z.card) :
    80 ≤ (Four.sts3 X Y Z).card := by
  have h := Four.card_sts3 X Y Z
  have hsub : (Four.sts2 (X ∩ Y) Z).card ≤ (Four.sts2 Y Z).card := by
    apply card_le_card
    intro q hq; rw [Four.mem_sts2] at hq ⊢
    exact ⟨(Finset.mem_inter.mp hq.1).2, hq.2.1, hq.2.2⟩
  have h20 := twenty_le hY hZ
  have hX' : (5 : ℤ) ≤ X.card := by exact_mod_cast hX
  have h20' : (20 : ℤ) ≤ (Four.sts2 Y Z).card := by exact_mod_cast h20
  have hsub' : ((Four.sts2 (X ∩ Y) Z).card : ℤ) ≤ (Four.sts2 Y Z).card := by exact_mod_cast hsub
  have : (80 : ℤ) ≤ (Four.sts3 X Y Z).card := by nlinarith
  exact_mod_cast this

/-! ### The block bound for the uniform weights -/

/-- The side factors `f(L)`. -/
def fsd : ℕ → ℚ
  | 0 => 1
  | 1 => 4 / 5
  | 2 => 16 / 21
  | 3 => 64 / 85
  | 4 => 256 / 341
  | _ => 1024 / 1365

/-- `m/(m + ρ ℓ (M - m))` for `m < M`, else `1` (`ρ = 9483/10000`). -/
def βQ6 (m M : ℕ) (ℓ : ℚ) : ℚ := if m < M then m / (m + 9483 / 10000 * ℓ * (M - m)) else 1

/-- `block_core6` with the bound `βQ6`. -/
theorem block_beta6 {σ α : Type*} [DecidableEq α] (Ω : Finset σ) (u : σ → ℝ) (π : σ → α)
    (F T : Finset α) (hF : ∀ t ∈ Ω, π t ∈ F) {g c : ℝ} {ℓ : ℚ} (hℓ : 0 < ℓ)
    (hc : 0 ≤ c) (hg : 0 ≤ g) (hu : ∀ t ∈ Ω, 9483 / 10000 * g ≤ u t ∧ u t ≤ g)
    (hN : ∀ τ ∈ F, (ℓ : ℝ) * c ≤ ((Ω.filter (fun t => π t = τ)).card : ℝ) ∧
      ((Ω.filter (fun t => π t = τ)).card : ℝ) ≤ c)
    {m M : ℕ} (hm : (F ∩ T).card ≤ m) (hM : M ≤ F.card) :
    ∑ t ∈ Ω.filter (fun t => π t ∈ T), u t ≤ ((βQ6 m M ℓ : ℚ) : ℝ) * ∑ t ∈ Ω, u t := by
  have hℓ' : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hu0 : ∀ t ∈ Ω, 0 ≤ u t := fun t ht =>
    le_trans (mul_nonneg (by norm_num) hg) (hu t ht).1
  have h := block_core6 Ω u π F T hF (ρ := 9483 / 10000) (by norm_num) hℓ'.le hc hg hu hN hm hM
  unfold βQ6
  split_ifs with hmM
  · have hmM' : (m : ℝ) < M := by exact_mod_cast hmM
    have hpos : (0 : ℝ) < (m : ℝ) + 9483 / 10000 * (ℓ : ℝ) * ((M : ℝ) - m) := by
      have : (0 : ℝ) < 9483 / 10000 * (ℓ : ℝ) * ((M : ℝ) - m) :=
        mul_pos (mul_pos (by norm_num) hℓ') (by linarith)
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    push_cast
    rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
    linarith
  · push_cast
    rw [one_mul]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun t ht _ => hu0 t ht)

/-- The largest uniform row. -/
noncomputable def gmax (w : Wt6) : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun o => rowV6 o w)

theorem GU_bounds {w : Wt6} (hw : InCone6 w) {t : T6} (ht : Proper t) :
    9483 / 10000 * gmax w ≤ GU 6 w t ∧ GU 6 w t ≤ gmax w := by
  rw [GU_six w ht]
  obtain ⟨o, -, ho⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun o => rowV6 o w)
  constructor
  · rw [gmax, ho]; exact rowV6_ratio hw _ _
  · exact Finset.le_sup' (fun o => rowV6 o w) (Finset.mem_univ _)

theorem gmax_nonneg {w : Wt6} (hw : InCone6 w) : 0 ≤ gmax w :=
  le_trans (rowV6_pos hw 0).le (Finset.le_sup' (fun o => rowV6 o w) (Finset.mem_univ 0))

/-- Sums of uniform weights over an event, with the rows reversed. -/
theorem sum_filter_rev66 (w : Wt6) (X₁ X₂ X₃ X₄ X₅ X₆ : Finset ℕ) (P : T6 → Prop)
    [DecidablePred P] :
    ∑ t ∈ (sts X₁ X₂ X₃ X₄ X₅ X₆).filter P, GU 6 w t
      = ∑ t ∈ (sts X₆ X₅ X₄ X₃ X₂ X₁).filter (fun t => P (rev6 t)), GU 6 w t := by
  rw [Finset.sum_filter, Finset.sum_filter, sum_sts_rev X₁ X₂ X₃ X₄ X₅ X₆]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [GU_rev w (proper_of_mem_sts ht)]

section blocks

variable {w : Wt6} {X₁ X₂ X₃ X₄ X₅ X₆ : Finset ℕ}

/-- `block_beta6` for the uniform weights on the proper columns. -/
theorem block_GU6 (hw : InCone6 w) {α : Type*} [DecidableEq α] (π : T6 → α) (F T : Finset α)
    (hF : ∀ t ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, π t ∈ F) {c : ℝ} {ℓ : ℚ} (hℓ : 0 < ℓ) (hc : 0 ≤ c)
    (hN : ∀ τ ∈ F, (ℓ : ℝ) * c ≤ (((sts X₁ X₂ X₃ X₄ X₅ X₆).filter (fun t => π t = τ)).card : ℝ) ∧
      (((sts X₁ X₂ X₃ X₄ X₅ X₆).filter (fun t => π t = τ)).card : ℝ) ≤ c)
    {m M : ℕ} (hm : (F ∩ T).card ≤ m) (hM : M ≤ F.card) :
    ∑ t ∈ (sts X₁ X₂ X₃ X₄ X₅ X₆).filter (fun t => π t ∈ T), GU 6 w t
      ≤ ((βQ6 m M ℓ : ℚ) : ℝ) * ∑ t ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, GU 6 w t :=
  block_beta6 _ _ π F T hF hℓ hc (gmax_nonneg hw)
    (fun t ht => GU_bounds hw (proper_of_mem_sts ht)) hN hm hM

theorem inter_le_of {α : Type*} [DecidableEq α] (F T : Finset α) {m : ℕ} (h : T.card ≤ m) :
    (F ∩ T).card ≤ m := (card_le_card inter_subset_right).trans h

/-- One row, at row 1. -/
theorem blk_one0 (hw : InCone6 w) (h₁ : 5 ≤ X₁.card) (h₂ : 5 ≤ X₂.card) (h₃ : 5 ≤ X₃.card)
    (h₄ : 5 ≤ X₄.card) (h₅ : 5 ≤ X₅.card) (h₆ : 5 ≤ X₆.card) (D : Finset ℕ) {d : ℕ}
    (hd : D.card ≤ d) :
    ∑ t ∈ (sts X₁ X₂ X₃ X₄ X₅ X₆).filter (fun t => r1 t ∈ D), GU 6 w t
      ≤ ((βQ6 d 5 (fsd 0 * fsd 5) : ℚ) : ℝ) * ∑ t ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, GU 6 w t := by
  refine block_GU6 hw r1 X₁ D (fun t ht => (mem_sts.mp ht).1) (c := (Five.sts X₂ X₃ X₄ X₅ X₆).card)
    (by norm_num [fsd]) (Nat.cast_nonneg _) (fun x hx => ?_) (inter_le_of _ D hd) h₁
  rw [fib01 hx]
  have := side5 h₂ h₃ h₄ h₅ h₆ x
  exact ⟨le_of_eq_of_le (by norm_num [fsd]) this.1, this.2⟩

/-- One row, at row 2. -/
theorem blk_one1 (hw : InCone6 w) (h₁ : 5 ≤ X₁.card) (h₂ : 5 ≤ X₂.card) (h₃ : 5 ≤ X₃.card)
    (h₄ : 5 ≤ X₄.card) (h₅ : 5 ≤ X₅.card) (h₆ : 5 ≤ X₆.card) (D : Finset ℕ) {d : ℕ}
    (hd : D.card ≤ d) :
    ∑ t ∈ (sts X₁ X₂ X₃ X₄ X₅ X₆).filter (fun t => r2 t ∈ D), GU 6 w t
      ≤ ((βQ6 d 5 (fsd 1 * fsd 4) : ℚ) : ℝ) * ∑ t ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, GU 6 w t := by
  refine block_GU6 hw r2 X₂ D (fun t ht => (mem_sts.mp ht).2.1)
    (c := (X₁.card : ℝ) * (Four.sts X₃ X₄ X₅ X₆).card)
    (by norm_num [fsd]) (by positivity) (fun x hx => ?_) (inter_le_of _ D hd) h₂
  rw [fib11 hx, Finset.card_product]
  push_cast
  have := prod_bounds (by norm_num) (by norm_num) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (side1 h₁ x) (side4 h₃ h₄ h₅ h₆ x)
  exact ⟨le_of_eq_of_le (by norm_num [fsd]) this.1, this.2⟩

/-- One row, at row 3. -/
theorem blk_one2 (hw : InCone6 w) (h₁ : 5 ≤ X₁.card) (h₂ : 5 ≤ X₂.card) (h₃ : 5 ≤ X₃.card)
    (h₄ : 5 ≤ X₄.card) (h₅ : 5 ≤ X₅.card) (h₆ : 5 ≤ X₆.card) (D : Finset ℕ) {d : ℕ}
    (hd : D.card ≤ d) :
    ∑ t ∈ (sts X₁ X₂ X₃ X₄ X₅ X₆).filter (fun t => r3 t ∈ D), GU 6 w t
      ≤ ((βQ6 d 5 (fsd 2 * fsd 3) : ℚ) : ℝ) * ∑ t ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, GU 6 w t := by
  refine block_GU6 hw r3 X₃ D (fun t ht => (mem_sts.mp ht).2.2.1)
    (c := ((Four.sts2 X₁ X₂).card : ℝ) * (Four.sts3 X₄ X₅ X₆).card)
    (by norm_num [fsd]) (by positivity) (fun x hx => ?_) (inter_le_of _ D hd) h₃
  rw [fib21 hx, Finset.card_product]
  push_cast
  have := prod_bounds (by norm_num) (by norm_num) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (side2last h₁ h₂ x) (side3 h₄ h₅ h₆ x)
  exact ⟨le_of_eq_of_le (by norm_num [fsd]) this.1, this.2⟩

/-- Two rows, at rows 1, 2. -/
theorem blk_two0 (hw : InCone6 w) (h₁ : 5 ≤ X₁.card) (h₂ : 5 ≤ X₂.card) (h₃ : 5 ≤ X₃.card)
    (h₄ : 5 ≤ X₄.card) (h₅ : 5 ≤ X₅.card) (h₆ : 5 ≤ X₆.card) (D D' : Finset ℕ) {d d' : ℕ}
    (hd : D.card ≤ d) (hd' : D'.card ≤ d') :
    ∑ t ∈ (sts X₁ X₂ X₃ X₄ X₅ X₆).filter (fun t => (r1 t, r2 t) ∈ D ×ˢ D'), GU 6 w t
      ≤ ((βQ6 (d * d') 20 (fsd 0 * fsd 4) : ℚ) : ℝ) * ∑ t ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, GU 6 w t := by
  have hT : (D ×ˢ D').card ≤ d * d' := by rw [card_product]; exact Nat.mul_le_mul hd hd'
  refine block_GU6 hw (fun t => (r1 t, r2 t)) (Four.sts2 X₁ X₂) (D ×ˢ D')
    (fun t ht => ?_) (c := (Four.sts X₃ X₄ X₅ X₆).card) (by norm_num [fsd]) (Nat.cast_nonneg _)
    (fun τ hτ => ?_) (inter_le_of _ _ hT) (twenty_le h₁ h₂)
  · obtain ⟨a1, a2, -, -, -, -, p1, -, -, -, -⟩ := mem_sts.mp ht
    exact Four.mem_sts2.mpr ⟨a1, a2, p1⟩
  · obtain ⟨x, y⟩ := τ
    obtain ⟨hx, hy, hxy⟩ := Four.mem_sts2.mp hτ
    rw [fib02 hx hy hxy]
    have := side4 h₃ h₄ h₅ h₆ y
    exact ⟨le_of_eq_of_le (by norm_num [fsd]) this.1, this.2⟩

/-- Two rows, at rows 2, 3. -/
theorem blk_two1 (hw : InCone6 w) (h₁ : 5 ≤ X₁.card) (h₂ : 5 ≤ X₂.card) (h₃ : 5 ≤ X₃.card)
    (h₄ : 5 ≤ X₄.card) (h₅ : 5 ≤ X₅.card) (h₆ : 5 ≤ X₆.card) (D D' : Finset ℕ) {d d' : ℕ}
    (hd : D.card ≤ d) (hd' : D'.card ≤ d') :
    ∑ t ∈ (sts X₁ X₂ X₃ X₄ X₅ X₆).filter (fun t => (r2 t, r3 t) ∈ D ×ˢ D'), GU 6 w t
      ≤ ((βQ6 (d * d') 20 (fsd 1 * fsd 3) : ℚ) : ℝ) * ∑ t ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, GU 6 w t := by
  have hT : (D ×ˢ D').card ≤ d * d' := by rw [card_product]; exact Nat.mul_le_mul hd hd'
  refine block_GU6 hw (fun t => (r2 t, r3 t)) (Four.sts2 X₂ X₃) (D ×ˢ D')
    (fun t ht => ?_) (c := (X₁.card : ℝ) * (Four.sts3 X₄ X₅ X₆).card) (by norm_num [fsd])
    (by positivity) (fun τ hτ => ?_) (inter_le_of _ _ hT) (twenty_le h₂ h₃)
  · obtain ⟨-, a2, a3, -, -, -, -, p2, -, -, -⟩ := mem_sts.mp ht
    exact Four.mem_sts2.mpr ⟨a2, a3, p2⟩
  · obtain ⟨x, y⟩ := τ
    obtain ⟨hx, hy, hxy⟩ := Four.mem_sts2.mp hτ
    rw [fib12 hx hy hxy, Finset.card_product]
    push_cast
    have := prod_bounds (by norm_num) (by norm_num) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (side1 h₁ x) (side3 h₄ h₅ h₆ y)
    exact ⟨le_of_eq_of_le (by norm_num [fsd]) this.1, this.2⟩

/-- Two rows, at rows 3, 4. -/
theorem blk_two2 (hw : InCone6 w) (h₁ : 5 ≤ X₁.card) (h₂ : 5 ≤ X₂.card) (h₃ : 5 ≤ X₃.card)
    (h₄ : 5 ≤ X₄.card) (h₅ : 5 ≤ X₅.card) (h₆ : 5 ≤ X₆.card) (D D' : Finset ℕ) {d d' : ℕ}
    (hd : D.card ≤ d) (hd' : D'.card ≤ d') :
    ∑ t ∈ (sts X₁ X₂ X₃ X₄ X₅ X₆).filter (fun t => (r3 t, r4 t) ∈ D ×ˢ D'), GU 6 w t
      ≤ ((βQ6 (d * d') 20 (fsd 2 * fsd 2) : ℚ) : ℝ) * ∑ t ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, GU 6 w t := by
  have hT : (D ×ˢ D').card ≤ d * d' := by rw [card_product]; exact Nat.mul_le_mul hd hd'
  refine block_GU6 hw (fun t => (r3 t, r4 t)) (Four.sts2 X₃ X₄) (D ×ˢ D')
    (fun t ht => ?_) (c := ((Four.sts2 X₁ X₂).card : ℝ) * (Four.sts2 X₅ X₆).card)
    (by norm_num [fsd]) (by positivity) (fun τ hτ => ?_) (inter_le_of _ _ hT) (twenty_le h₃ h₄)
  · obtain ⟨-, -, a3, a4, -, -, -, -, p3, -, -⟩ := mem_sts.mp ht
    exact Four.mem_sts2.mpr ⟨a3, a4, p3⟩
  · obtain ⟨x, y⟩ := τ
    obtain ⟨hx, hy, hxy⟩ := Four.mem_sts2.mp hτ
    rw [fib22 hx hy hxy, Finset.card_product]
    push_cast
    have := prod_bounds (by norm_num) (by norm_num) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (side2last h₁ h₂ x) (side2 h₅ h₆ y)
    exact ⟨le_of_eq_of_le (by norm_num [fsd]) this.1, this.2⟩

/-- Three rows, at rows 1–3. -/
theorem blk_three0 (hw : InCone6 w) (h₁ : 5 ≤ X₁.card) (h₂ : 5 ≤ X₂.card) (h₃ : 5 ≤ X₃.card)
    (h₄ : 5 ≤ X₄.card) (h₅ : 5 ≤ X₅.card) (h₆ : 5 ≤ X₆.card) (D D' D'' : Finset ℕ)
    {d d' d'' : ℕ} (hd : D.card ≤ d) (hd' : D'.card ≤ d') (hd'' : D''.card ≤ d'') :
    ∑ t ∈ (sts X₁ X₂ X₃ X₄ X₅ X₆).filter (fun t => (r1 t, r2 t, r3 t) ∈ D ×ˢ D' ×ˢ D''), GU 6 w t
      ≤ ((βQ6 (d * d' * d'') 80 (fsd 0 * fsd 3) : ℚ) : ℝ)
        * ∑ t ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, GU 6 w t := by
  have hT : (D ×ˢ D' ×ˢ D'').card ≤ d * d' * d'' := by
    rw [card_product, card_product, ← Nat.mul_assoc]
    exact Nat.mul_le_mul (Nat.mul_le_mul hd hd') hd''
  refine block_GU6 hw (fun t => (r1 t, r2 t, r3 t)) (Four.sts3 X₁ X₂ X₃) (D ×ˢ D' ×ˢ D'')
    (fun t ht => ?_) (c := (Four.sts3 X₄ X₅ X₆).card) (by norm_num [fsd]) (Nat.cast_nonneg _)
    (fun τ hτ => ?_) (inter_le_of _ _ hT) (eighty_le h₁ h₂ h₃)
  · obtain ⟨a1, a2, a3, -, -, -, p1, p2, -, -, -⟩ := mem_sts.mp ht
    exact Four.mem_sts3.mpr ⟨a1, a2, a3, p1, p2⟩
  · obtain ⟨x, y, z⟩ := τ
    obtain ⟨hx, hy, hz, hxy, hyz⟩ := Four.mem_sts3.mp hτ
    rw [fib03 hx hy hz hxy hyz]
    have := side3 h₄ h₅ h₆ z
    exact ⟨le_of_eq_of_le (by norm_num [fsd]) this.1, this.2⟩

/-- Three rows, at rows 2–4. -/
theorem blk_three1 (hw : InCone6 w) (h₁ : 5 ≤ X₁.card) (h₂ : 5 ≤ X₂.card) (h₃ : 5 ≤ X₃.card)
    (h₄ : 5 ≤ X₄.card) (h₅ : 5 ≤ X₅.card) (h₆ : 5 ≤ X₆.card) (D D' D'' : Finset ℕ)
    {d d' d'' : ℕ} (hd : D.card ≤ d) (hd' : D'.card ≤ d') (hd'' : D''.card ≤ d'') :
    ∑ t ∈ (sts X₁ X₂ X₃ X₄ X₅ X₆).filter (fun t => (r2 t, r3 t, r4 t) ∈ D ×ˢ D' ×ˢ D''), GU 6 w t
      ≤ ((βQ6 (d * d' * d'') 80 (fsd 1 * fsd 2) : ℚ) : ℝ)
        * ∑ t ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, GU 6 w t := by
  have hT : (D ×ˢ D' ×ˢ D'').card ≤ d * d' * d'' := by
    rw [card_product, card_product, ← Nat.mul_assoc]
    exact Nat.mul_le_mul (Nat.mul_le_mul hd hd') hd''
  refine block_GU6 hw (fun t => (r2 t, r3 t, r4 t)) (Four.sts3 X₂ X₃ X₄) (D ×ˢ D' ×ˢ D'')
    (fun t ht => ?_) (c := (X₁.card : ℝ) * (Four.sts2 X₅ X₆).card) (by norm_num [fsd])
    (by positivity) (fun τ hτ => ?_) (inter_le_of _ _ hT) (eighty_le h₂ h₃ h₄)
  · obtain ⟨-, a2, a3, a4, -, -, -, p2, p3, -, -⟩ := mem_sts.mp ht
    exact Four.mem_sts3.mpr ⟨a2, a3, a4, p2, p3⟩
  · obtain ⟨x, y, z⟩ := τ
    obtain ⟨hx, hy, hz, hxy, hyz⟩ := Four.mem_sts3.mp hτ
    rw [fib13 hx hy hz hxy hyz, Finset.card_product]
    push_cast
    have := prod_bounds (by norm_num) (by norm_num) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (side1 h₁ x) (side2 h₅ h₆ z)
    exact ⟨le_of_eq_of_le (by norm_num [fsd]) this.1, this.2⟩

end blocks

end GridGen.Six
