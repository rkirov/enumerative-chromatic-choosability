/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.Hex

/-!
# The rank-one bound at a triangle (Hall's condition)

A triangle `u w v` with root edge `uv` and side profiles `E₀` on `uw`, `E₁` on `wv`. Fix a
bijection `σ : L u → L v` with `σ c ≠ c`. For each root pair `(c, σ c)` the apex can take the
colours of `L w` other than `c` and `σ c`.

* If these three sets of apex colours have distinct representatives `τ c`, the root bijection
  product is at least the product of the two side bijection products
  `c ↦ τ c` and `τ c ↦ σ c`, so the rank-one bounds (`HasPot`) of the sides suffice.
* Otherwise two root pairs force the same apex colour `t`: they are `(x, y)` and `(y, x)` with
  `L w = {x, y, t}`, and the third pair `(a, b)` may use `x` or `y`. Then
  `F(x,y) F(y,x) F(a,b) ≥ 2 · [E₀(x,t) E₀(y,t) √(E₀(a,x) E₀(a,y))] · [E₁(t,y) E₁(t,x) √(E₁(x,b) E₁(y,b))]`,
  and each bracket is a four-cell product of one matched six-family (`TB`).

So `HasPot` on both sides and four-cell constants with `2 τ₀ τ₁ ≥ 1` give `HasPot` at the root
(`hasPot_tri`, via Egerváry's theorem `exists_potentials`). The combinatorial dichotomy is
checked on indices by `decide` (`hall_pattern`).

This is part of the formalization of the six-even-face theorem (research note
`ai_research_notes/OUTERPLANAR_SIX_EVEN_2026-11-23.md`, section "The triangle where Hall fails").
-/

namespace Outerplanar

open Finset

/-! ### The dichotomy on indices -/

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 4000 in
set_option maxHeartbeats 4000000 in
/-- `A i = some j` records `α i = γ j` and `B i = some j` records `σ (α i) = γ j`. Either the
apex has distinct admissible indices for the three root pairs, or two root pairs are `(x, y)`
and `(y, x)` with `x, y` in the apex list. -/
theorem hall_pattern : ∀ A B : Fin 3 → Option (Fin 3),
    (∀ i i' j, A i = some j → A i' = some j → i = i') →
    (∀ i i' j, B i = some j → B i' = some j → i = i') →
    (∀ i j, A i = some j → B i = some j → False) →
    (∃ ρ : Fin 3 → Fin 3, (∀ x y, ρ x = ρ y → x = y) ∧
        ∀ i, A i ≠ some (ρ i) ∧ B i ≠ some (ρ i)) ∨
      (∃ i₁ i₂ i₃ j₁ j₂ j₃ : Fin 3, i₁ ≠ i₂ ∧ i₁ ≠ i₃ ∧ i₂ ≠ i₃ ∧ j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃ ∧
        A i₁ = some j₁ ∧ B i₁ = some j₂ ∧ A i₂ = some j₂ ∧ B i₂ = some j₁) := by
  decide +kernel

/-! ### Small facts -/

set_option linter.unusedTactic false in
theorem prod_fin_three_of_ne (f : Fin 3 → ℝ) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) : ∏ x, f x = f i * f j * f k := by
  rw [Fin.prod_univ_three]
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    first | exact absurd rfl hij | exact absurd rfl hik | exact absurd rfl hjk |
      (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> ring)

/-- The six pairs off the identity between two enumerations are matched. -/
theorem matched_of_enum {S T : Finset ℕ} {α β : Fin 3 → ℕ} (hα : Function.Injective α)
    (hβ : Function.Injective β) (hαm : ∀ a, α a ∈ S) (hβm : ∀ b, β b ∈ T) :
    Matched S T (fun i => α (offPair i).1) (fun i => β (offPair i).2) := by
  refine ⟨α, β, hα, hβ, hαm, hβm, fun a b hab => ?_⟩
  obtain ⟨j, hj⟩ := offPair_surj a b hab
  exact ⟨j, by simp [hj], by simp [hj]⟩

theorem injective_three {x y z : ℕ} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    Function.Injective ![x, y, z] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

/-- A rank-one bound gives the bijection bound along any pair of enumerations. -/
theorem HasPot.enum_prod {S T : Finset ℕ} {W : ℕ → ℕ → ℝ} {A : ℝ} (hS : S.card = 3)
    (hT : T.card = 3) (h : HasPot S T W A) (hA : 0 ≤ A) {φ ψ : Fin 3 → ℕ}
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ) (hφm : ∀ i, φ i ∈ S)
    (hψm : ∀ i, ψ i ∈ T) (hne : ∀ i, φ i ≠ ψ i) : A ^ 3 ≤ ∏ i, W (φ i) (ψ i) := by
  obtain ⟨a, b, ha, hb, hpa, hpb, hW⟩ := h
  have e1 : ∏ i, a (φ i) = 1 := by
    rw [← hpa, ← image_enum hS hφ hφm, Finset.prod_image fun x _ y _ e => hφ e]
  have e2 : ∏ i, b (ψ i) = 1 := by
    rw [← hpb, ← image_enum hT hψ hψm, Finset.prod_image fun x _ y _ e => hψ e]
  calc A ^ 3 = ∏ i : Fin 3, A * (a (φ i) * b (ψ i)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          Finset.prod_mul_distrib, e1, e2, mul_one, mul_one]
    _ ≤ _ := Finset.prod_le_prod₀
        (fun i _ => mul_nonneg hA (mul_pos (ha _ (hφm i)) (hb _ (hψm i))).le)
        fun i _ => hW _ (hφm i) _ (hψm i) (hne i)

/-! ### The bijection bound at a triangle -/

/-- **Hall at a triangle.** `F` is any profile that dominates the apex sums (`hF1`, `hF2`); the
triangle's own profile is one (`faceSum_tri_one`, `faceSum_tri_two`). -/
theorem tri_bij_bound {Lu Lw Lv : Finset ℕ} (hu : Lu.card = 3) (hw : Lw.card = 3)
    (hv : Lv.card = 3) {E₀ E₁ F : ℕ → ℕ → ℝ} (h00 : ∀ c d, 0 ≤ E₀ c d) (h01 : ∀ c d, 0 ≤ E₁ c d)
    {A₀ A₁ τ₀ τ₁ : ℝ} (hA₀ : 0 < A₀) (hA₁ : 0 < A₁)
    (hP₀ : HasPot Lu Lw E₀ A₀) (hP₁ : HasPot Lw Lv E₁ A₁) (hT₀ : TB Lu Lw E₀ A₀ τ₀)
    (hT₁ : TB Lw Lv E₁ A₁ τ₁) (h2 : 1 ≤ 2 * (τ₀ * τ₁))
    (hF1 : ∀ c d t, t ∈ Lw → E₀ c t * E₁ t d ≤ F c d)
    (hF2 : ∀ c d t t', t ∈ Lw → t' ∈ Lw → t ≠ t' → E₀ c t * E₁ t d + E₀ c t' * E₁ t' d ≤ F c d)
    {σ : ℕ → ℕ} (hσ : Set.BijOn σ Lu Lv) (hne : ∀ c ∈ Lu, σ c ≠ c) :
    (A₀ * A₁) ^ 3 ≤ ∏ c ∈ Lu, F c (σ c) := by
  obtain ⟨α, hα, hαm⟩ := exists_enum hu
  obtain ⟨γ, hγ, hγm⟩ := exists_enum hw
  set β : Fin 3 → ℕ := fun i => σ (α i) with hβdef
  have hβm : ∀ i, β i ∈ Lv := fun i => hσ.mapsTo (hαm i)
  have hβ : Function.Injective β := fun i i' e => hα (hσ.injOn (hαm i) (hαm i') e)
  have hαβ : ∀ i, α i ≠ β i := fun i e => hne _ (hαm i) e.symm
  have hprod : ∏ c ∈ Lu, F c (σ c) = ∏ i, F (α i) (β i) := by
    rw [← image_enum hu hα hαm, Finset.prod_image fun x _ y _ e => hα e]
  rw [hprod]
  obtain ⟨Ai, hAi⟩ := exists_pos γ α hγ
  obtain ⟨Bi, hBi⟩ := exists_pos γ β hγ
  have hF0 : ∀ c d, 0 ≤ F c d := fun c d =>
    (mul_nonneg (h00 c (γ 0)) (h01 (γ 0) d)).trans (hF1 c d _ (hγm 0))
  rcases hall_pattern Ai Bi
    (fun i i' j h h' => hα (((hAi i j).mp h).trans ((hAi i' j).mp h').symm))
    (fun i i' j h h' => hβ (((hBi i j).mp h).trans ((hBi i' j).mp h').symm))
    (fun i j h h' => hαβ i (((hAi i j).mp h).trans ((hBi i j).mp h').symm)) with
    ⟨ρ, hρ, hρA⟩ | ⟨i₁, i₂, i₃, j₁, j₂, j₃, hi12, hi13, hi23, hj12, hj13, hj23, ha1, hb1, ha2, hb2⟩
  · -- distinct representatives
    have hρi : Function.Injective (fun i => γ (ρ i)) := fun x y e => hρ x y (hγ e)
    have k0 := hP₀.enum_prod hu hw hA₀.le hα hρi hαm (fun i => hγm _)
      fun i e => (hρA i).1 ((hAi i (ρ i)).mpr e)
    have k1 := hP₁.enum_prod hw hv hA₁.le hρi hβ (fun i => hγm _) hβm
      fun i e => (hρA i).2 ((hBi i (ρ i)).mpr e.symm)
    calc (A₀ * A₁) ^ 3 = A₀ ^ 3 * A₁ ^ 3 := mul_pow _ _ _
      _ ≤ (∏ i, E₀ (α i) (γ (ρ i))) * ∏ i, E₁ (γ (ρ i)) (β i) :=
          mul_le_mul k0 k1 (pow_nonneg hA₁.le _) ((pow_nonneg hA₀.le _).trans k0)
      _ = ∏ i, E₀ (α i) (γ (ρ i)) * E₁ (γ (ρ i)) (β i) := (Finset.prod_mul_distrib).symm
      _ ≤ _ := Finset.prod_le_prod₀ (fun i _ => mul_nonneg (h00 _ _) (h01 _ _))
          fun i _ => hF1 _ _ _ (hγm _)
  · -- two root pairs force the same apex colour
    have ex1 : α i₁ = γ j₁ := (hAi _ _).mp ha1
    have ey1 : β i₁ = γ j₂ := (hBi _ _).mp hb1
    have ey2 : α i₂ = γ j₂ := (hAi _ _).mp ha2
    have ex2 : β i₂ = γ j₁ := (hBi _ _).mp hb2
    set x := γ j₁
    set y := γ j₂
    set t := γ j₃
    set a := α i₃
    set b := β i₃
    have hxy : x ≠ y := fun e => hj12 (hγ e)
    have hxt : x ≠ t := fun e => hj13 (hγ e)
    have hyt : y ≠ t := fun e => hj23 (hγ e)
    have hax : a ≠ x := fun e => hi13 (hα (ex1.trans e.symm))
    have hay : a ≠ y := fun e => hi23 (hα (ey2.trans e.symm))
    have hbx : b ≠ x := fun e => hi23 (hβ (ex2.trans e.symm))
    have hby : b ≠ y := fun e => hi13 (hβ (ey1.trans e.symm))
    have hxw : x ∈ Lw := hγm _
    have hyw : y ∈ Lw := hγm _
    have htw : t ∈ Lw := hγm _
    have hxu : x ∈ Lu := ex1 ▸ hαm _
    have hyu : y ∈ Lu := ey2 ▸ hαm _
    have hau : a ∈ Lu := hαm _
    have hxv : x ∈ Lv := ex2 ▸ hβm _
    have hyv : y ∈ Lv := ey1 ▸ hβm _
    have hbv : b ∈ Lv := hβm _
    -- the two four-cell bounds
    have q0 := hT₀ _ _ (matched_of_enum (injective_three hxy hax.symm hay.symm)
      (injective_three hxy hxt hyt) (fun i => by fin_cases i <;> simpa)
      (fun i => by fin_cases i <;> simpa))
      (fun i => by fin_cases i <;> simp [offPair] <;> tauto)
      1 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have q1 := hT₁ _ _ (matched_of_enum (injective_three hxy hxt hyt)
      (injective_three hxy hbx.symm hby.symm) (fun i => by fin_cases i <;> simpa)
      (fun i => by fin_cases i <;> simpa))
      (fun i => by fin_cases i <;> simp [offPair] <;> tauto)
      5 4 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    simp only [offPair, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one] at q0 q1
    -- the three root pairs
    rw [prod_fin_three_of_ne _ hi12 hi13 hi23, ex1, ey1, ey2, ex2]
    have f1 := hF1 x y t htw
    have f2 := hF1 y x t htw
    have f3 := hF2 a b x y hxw hyw hxy
    set P := E₀ x t * E₁ t y * (E₀ y t * E₁ t x) *
      (E₀ a x * E₁ x b + E₀ a y * E₁ y b) with hP
    have hPle : P ≤ F x y * F y x * F a b :=
      mul_le_mul (mul_le_mul f1 f2 (mul_nonneg (h00 _ _) (h01 _ _)) (hF0 _ _)) f3
        (add_nonneg (mul_nonneg (h00 _ _) (h01 _ _)) (mul_nonneg (h00 _ _) (h01 _ _)))
        (mul_nonneg (hF0 _ _) (hF0 _ _))
    have hP0 : 0 ≤ P := mul_nonneg (mul_nonneg (mul_nonneg (h00 _ _) (h01 _ _))
      (mul_nonneg (h00 _ _) (h01 _ _)))
      (add_nonneg (mul_nonneg (h00 _ _) (h01 _ _)) (mul_nonneg (h00 _ _) (h01 _ _)))
    -- `(u + v)² ≥ 4 u v`
    have hsq : 4 * ((E₀ x t ^ 2 * E₀ y t ^ 2 * E₀ a x * E₀ a y)
        * (E₁ t y ^ 2 * E₁ t x ^ 2 * E₁ x b * E₁ y b)) ≤ P ^ 2 := by
      have huv := four_mul_le_sq_add (E₀ a x * E₁ x b) (E₀ a y * E₁ y b)
      have hc : 0 ≤ (E₀ x t * E₁ t y * (E₀ y t * E₁ t x)) ^ 2 := sq_nonneg _
      calc 4 * ((E₀ x t ^ 2 * E₀ y t ^ 2 * E₀ a x * E₀ a y)
            * (E₁ t y ^ 2 * E₁ t x ^ 2 * E₁ x b * E₁ y b))
          = (E₀ x t * E₁ t y * (E₀ y t * E₁ t x)) ^ 2
            * (4 * (E₀ a x * E₁ x b) * (E₀ a y * E₁ y b)) := by ring
        _ ≤ (E₀ x t * E₁ t y * (E₀ y t * E₁ t x)) ^ 2
            * (E₀ a x * E₁ x b + E₀ a y * E₁ y b) ^ 2 := mul_le_mul_of_nonneg_left huv hc
        _ = P ^ 2 := by rw [hP]; ring
    have hτ : 1 ≤ 4 * (τ₀ ^ 2 * τ₁ ^ 2) := by
      calc (1 : ℝ) = 1 ^ 2 := by norm_num
        _ ≤ (2 * (τ₀ * τ₁)) ^ 2 := pow_le_pow_left₀ zero_le_one h2 2
        _ = 4 * (τ₀ ^ 2 * τ₁ ^ 2) := by ring
    have key : ((A₀ * A₁) ^ 3) ^ 2 ≤ P ^ 2 := by
      have hq : (τ₀ ^ 2 * A₀ ^ 6) * (τ₁ ^ 2 * A₁ ^ 6) ≤
          (E₀ x t ^ 2 * E₀ y t ^ 2 * E₀ a x * E₀ a y)
            * (E₁ t y ^ 2 * E₁ t x ^ 2 * E₁ x b * E₁ y b) :=
        mul_le_mul q0 q1 (by positivity) ((by positivity : (0 : ℝ) ≤ τ₀ ^ 2 * A₀ ^ 6).trans q0)
      calc ((A₀ * A₁) ^ 3) ^ 2 ≤ 4 * (τ₀ ^ 2 * τ₁ ^ 2) * ((A₀ * A₁) ^ 3) ^ 2 :=
            le_mul_of_one_le_left (by positivity) hτ
        _ = 4 * ((τ₀ ^ 2 * A₀ ^ 6) * (τ₁ ^ 2 * A₁ ^ 6)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hq (by norm_num)
        _ ≤ P ^ 2 := hsq
    exact ((pow_le_pow_iff_left₀ (by positivity) hP0 (by norm_num : (2 : ℕ) ≠ 0)).mp key).trans
      hPle

/-! ### The triangle's profile -/

/-- Two apex colours of a triangle. -/
theorem tri_two_le (Li : Fin 1 → Finset ℕ) (E : Fin 2 → ℕ → ℕ → ℝ)
    (hE0 : ∀ j c d, 0 ≤ E j c d) (a b : ℕ) {e e' : ℕ} (he : e ∈ Li 0) (he' : e' ∈ Li 0)
    (hee : e ≠ e') :
    E 0 a e * E 1 e b + E 0 a e' * E 1 e' b ≤ faceSum Li (fun _ _ => 1) E a b := by
  have hterm : ∀ g ∈ Fintype.piFinset Li, 0 ≤ (∏ _j : Fin 1, (1 : ℝ)) *
      ∏ j : Fin 2, E j (pathCol a b g j.castSucc) (pathCol a b g j.succ) := fun g _ =>
    mul_nonneg (Finset.prod_nonneg fun _ _ => zero_le_one)
      (Finset.prod_nonneg fun j _ => hE0 _ _ _)
  have hval : ∀ f : ℕ, (∏ _j : Fin 1, (1 : ℝ)) * ∏ j : Fin 2,
      E j (pathCol a b (fun _ : Fin 1 => f) j.castSucc) (pathCol a b (fun _ : Fin 1 => f) j.succ)
      = E 0 a f * E 1 f b := by
    intro f
    have p0 : pathCol a b (fun _ : Fin 1 => f) (Fin.castSucc (0 : Fin 2)) = a :=
      consSnoc_zero _ _ _ _ (by simp)
    have p1 : pathCol a b (fun _ : Fin 1 => f) (Fin.succ (0 : Fin 2)) = f :=
      consSnoc_mid _ _ _ _ (0 : Fin 1) (by simp)
    have p1' : pathCol a b (fun _ : Fin 1 => f) (Fin.castSucc (1 : Fin 2)) = f :=
      consSnoc_mid _ _ _ _ (0 : Fin 1) (by simp)
    have p2 : pathCol a b (fun _ : Fin 1 => f) (Fin.succ (1 : Fin 2)) = b :=
      consSnoc_last _ _ _ _ (by simp)
    rw [Fin.prod_univ_two, p0, p1, p1', p2]
    simp only [Finset.prod_const_one, one_mul]
  have hmem : ∀ f ∈ Li 0, (fun _ : Fin 1 => f) ∈ Fintype.piFinset Li := fun f hf =>
    Fintype.mem_piFinset.mpr fun j => by rw [Subsingleton.elim j 0]; exact hf
  have hne : (fun _ : Fin 1 => e) ≠ (fun _ : Fin 1 => e') := fun h => hee (congrFun h 0)
  have hsub : ({fun _ : Fin 1 => e, fun _ : Fin 1 => e'} : Finset (Fin 1 → ℕ)) ⊆
      Fintype.piFinset Li := by
    intro g hg
    rcases mem_insert.mp hg with rfl | hg
    · exact hmem e he
    · rw [mem_singleton.mp hg]; exact hmem e' he'
  have := Finset.sum_le_sum_of_subset_of_nonneg hsub fun g hg _ => hterm g hg
  rw [Finset.sum_pair hne, hval, hval] at this
  exact this

/-- **A triangle has the rank-one bound** when both sides have it and their four-cell constants
satisfy `2 τ₀ τ₁ ≥ 1`. -/
theorem hasPot_tri {Lu Lv : Finset ℕ} {Li : Fin 1 → Finset ℕ} (hu : Lu.card = 3)
    (hv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3) {E : Fin 2 → ℕ → ℕ → ℝ}
    (hE0 : ∀ j c d, 0 ≤ E j c d) {A τ : Fin 2 → ℝ} (hA : ∀ j, 0 < A j)
    (hP : ∀ j : Fin 2,
      HasPot (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j))
    (hT : ∀ j : Fin 2,
      TB (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j) (τ j))
    (h2 : 1 ≤ 2 * (τ 0 * τ 1)) :
    HasPot Lu Lv (faceSum Li (fun _ _ => 1) E) (∏ j, A j) := by
  obtain ⟨l0, l1, l2, l3⟩ := pathList_tri Lu Lv Li
  have hP₀ : HasPot Lu (Li 0) (E 0) (A 0) := by have := hP 0; rwa [l0, l1] at this
  have hP₁ : HasPot (Li 0) Lv (E 1) (A 1) := by have := hP 1; rwa [l2, l3] at this
  have hT₀ : TB Lu (Li 0) (E 0) (A 0) (τ 0) := by have := hT 0; rwa [l0, l1] at this
  have hT₁ : TB (Li 0) Lv (E 1) (A 1) (τ 1) := by have := hT 1; rwa [l2, l3] at this
  set F := faceSum Li (fun _ _ => 1) E with hFdef
  have hA01 : 0 < A 0 * A 1 := mul_pos (hA 0) (hA 1)
  rw [Fin.prod_univ_two]
  -- positivity on the pairs of different colours
  have hFpos : ∀ c ∈ Lu, ∀ d ∈ Lv, c ≠ d → 0 < F c d := by
    intro c hc d hd _
    obtain ⟨e, he, hec, hed⟩ := exists_avoid (hLi 0) c d
    obtain ⟨a, b, ha, hb, -, -, hW⟩ := hP₀
    obtain ⟨a', b', ha', hb', -, -, hW'⟩ := hP₁
    have q0 : 0 < E 0 c e := lt_of_lt_of_le
      (mul_pos (hA 0) (mul_pos (ha c hc) (hb e he))) (hW c hc e he (Ne.symm hec))
    have q1 : 0 < E 1 e d := lt_of_lt_of_le
      (mul_pos (hA 1) (mul_pos (ha' e he) (hb' d hd))) (hW' e he d hd hed)
    exact lt_of_lt_of_le (mul_pos q0 q1) (tri_term_le Li E hE0 c d he)
  obtain ⟨a, b, ha, hb, hpa, hpb, hW⟩ := exists_potentials (le_refl 3) Lu Lv hu hv
    (fun c d => F c d / (A 0 * A 1))
    (fun c hc d hd hcd => div_pos (hFpos c hc d hd hcd) hA01)
    (fun σ hσ hne => by
      have key := tri_bij_bound hu (hLi 0) hv (hE0 0) (hE0 1) (hA 0) (hA 1) hP₀ hP₁ hT₀ hT₁ h2
        (fun c d t ht => tri_term_le Li E hE0 c d ht)
        (fun c d t t' ht ht' htt => tri_two_le Li E hE0 c d ht ht' htt) hσ hne
      rw [Finset.prod_div_distrib, Finset.prod_const, hu]
      exact (one_le_div (pow_pos hA01 3)).mpr key)
  refine ⟨a, b, ha, hb, hpa, hpb, fun c hc d hd hcd => ?_⟩
  have := hW c hc d hd hcd
  rwa [le_div_iff₀ hA01, mul_comm] at this

end Outerplanar
