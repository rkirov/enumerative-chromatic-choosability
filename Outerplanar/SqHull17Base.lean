/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.SqHullBase

/-!
# A square over the hull class: the four-cell bound `17/32`

The certificates of `Outerplanar/SqHullData*.lean` (generated for the bound `1/2`) also pass the
vertex check at `τ = 17/32`, `τ² = 289/1024`: their least vertex value is `171500 / 9⁶ = 0.3227`
(the minimum over the 4202 list configurations of the six-even-face note), and
`289/1024 = 0.2822`. This file has the check and its soundness:

* `vok17 R` — `289 · 9⁶ · U ≤ 1024 · L · ∏ R` for `L`, `U` the least and greatest product of two
  entries; `HCase.vertOK17` — every hull vertex passes;
* `genHull17_of_case` — the four-cell bound `17/32` (`SqHullOK17`) from a checked case, the proof of
  `genHull_of_case` with the new constant.

The two-mark class of the thirteen-even-face theorem needs exactly this constant (research note
`ai_research_notes/OUTERPLANAR_ELEVEN_AND_CENTRAL_SQUARE_2026-11-23.md`, "Two marks"; plan
`ai_research_notes/OUTERPLANAR_13_15_LEAN_PLAN.md`, gate G3). Formalized by Claude.
-/

namespace Outerplanar

open Finset

/-! ### The property of a pattern -/

/-- The four-cell bound `17/32` at the root, for every loaded table in the hull class. -/
def GenHull17 (B₁ : Fin 3 → Fin 3 → ℕ) (El : BMat) (B₂ : Fin 3 → Fin 3 → ℕ) : Prop :=
  ∀ w : Fin 3 → Fin 3 → ℝ, (∀ s t, 0 ≤ w s t) → ∀ A : ℝ, 0 < A → IdxHull El w A →
    ∀ i j k l : Fin 6, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      (17 / 32) ^ 2 * (3 * A) ^ 6 ≤ genF B₁ El B₂ w (offPair i).1 (offPair i).2 ^ 2
        * genF B₁ El B₂ w (offPair j).1 (offPair j).2 ^ 2
        * genF B₁ El B₂ w (offPair k).1 (offPair k).2
        * genF B₁ El B₂ w (offPair l).1 (offPair l).2

theorem GenHull17.mono {B₁ B₁' B₂ B₂' : Fin 3 → Fin 3 → ℕ} {El El' : BMat}
    (h : GenHull17 B₁ El B₂) (h1 : ∀ a s, B₁ a s ≤ B₁' a s) (h2 : ∀ t b, B₂ t b ≤ B₂' t b)
    (hE : ∀ s t, El' s t = true → El s t = true) : GenHull17 B₁' El' B₂' := by
  intro w hw A hA hidx i j k l hij hik hil hjk hjl hkl
  have key := h w hw A hA (hidx.mono_el hE) i j k l hij hik hil hjk hjl hkl
  have hg := genF_mono' hw h1 h2 hE
  have hn := genF_nonneg B₁ El B₂ hw
  exact key.trans (four_le (hn _ _) (hn _ _) (hn _ _) (hn _ _) (hg _ _) (hg _ _) (hg _ _)
    (hg _ _))

/-- The square with pattern `P` and loaded edge `e`. -/
def SqHullOK17 (P : Pat) (e : Fin 3) : Prop := GenHull17 (sqB₁ P e) (sqEl P e) (sqB₂ P e)

theorem SqHullOK17.mono {P Q : Pat} (h : PatLE P Q) {e : Fin 3} (hQ : SqHullOK17 Q e) :
    SqHullOK17 P e := by
  unfold SqHullOK17 at hQ ⊢
  refine hQ.mono (fun a s => ?_) (fun t b => ?_) fun s t => ?_
  · unfold sqB₁
    by_cases h0 : e = 0
    · rw [ite_eq_left h0, ite_eq_left h0]
    · rw [ite_eq_right h0, ite_eq_right h0]
      by_cases h1 : e = 1
      · rw [ite_eq_left h1, ite_eq_left h1]
        exact nb_le (h.h01 a s)
      · rw [ite_eq_right h1, ite_eq_right h1]
        exact arc2_le h.h01 h.h12 a s
  · unfold sqB₂
    by_cases h0 : e = 0
    · rw [ite_eq_left h0, ite_eq_left h0]
      exact arc2_le h.h12 h.h23 t b
    · rw [ite_eq_right h0, ite_eq_right h0]
      by_cases h1 : e = 1
      · rw [ite_eq_left h1, ite_eq_left h1]
        exact nb_le (h.h23 t b)
      · rw [ite_eq_right h1, ite_eq_right h1]
  · unfold sqEl
    split_ifs
    · exact h.h01 s t
    · exact h.h12 s t
    · exact h.h23 s t

/-! ### The vertex check at `17/32` -/

/-- The check of one vertex: `1024 L ∏ ≥ 289 · 9⁶ U`. -/
def vok17 (R : Fin 6 → ℕ) : Bool :=
  decide (0 < vL R) && decide (153586449 * vU R ≤ 1024 * vL R * (R 0 * R 1 * R 2 * R 3 * R 4 * R 5))

/-- All vertices pass at `17/32`. -/
def HCase.vertOK17 (c : HCase) : Prop :=
  vok17 c.r3 = true ∧ ∀ i j k : Fin 6, i ≠ j → i ≠ k → j < k → vok17 (c.rv i j k) = true

/-- **The four-cell bound from the products of pairs**, for any constants. -/
theorem quad_bound_gen (R : Fin 6 → ℕ) {L U K M : ℕ} (hL0 : 0 < L)
    (hp : ∀ x y : Fin 6, x ≠ y → L ≤ R x * R y ∧ R x * R y ≤ U)
    (hmain : K * U ≤ M * L * ∏ z, R z) (i j k l : Fin 6) (hij : i ≠ j) (hik : i ≠ k)
    (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    K ≤ M * (R i ^ 2 * R j ^ 2 * R k * R l) := by
  set s : Finset (Fin 6) := {i, j, k, l} with hs
  have hs4 : s.card = 4 := by
    rw [hs, card_insert_of_notMem (by simp [hij, hik, hil]),
      card_insert_of_notMem (by simp [hjk, hjl]), card_pair hkl]
  have hc2 : (univ \ s).card = 2 := by
    rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin, hs4]
  obtain ⟨x, y, hxy, hC⟩ := card_eq_two.mp hc2
  have hprod : ∏ z, R z = (R i * R j * R k * R l) * (R x * R y) := by
    rw [← Finset.prod_sdiff (subset_univ s), hC, Finset.prod_pair hxy, mul_comm]
    congr 1
    rw [hs, prod_insert (by simp [hij, hik, hil]), prod_insert (by simp [hjk, hjl]),
      prod_pair hkl]
    ring
  have hU0 : 0 < U := lt_of_lt_of_le hL0 ((hp i j hij).1.trans (hp i j hij).2)
  have h1 : L * ∏ z, R z ≤ U * (R i ^ 2 * R j ^ 2 * R k * R l) := by
    rw [hprod]
    have e1 := (hp i j hij).1
    have e2 := (hp x y hxy).2
    calc L * ((R i * R j * R k * R l) * (R x * R y))
        = (L * (R i * R j * R k * R l)) * (R x * R y) := by ring
      _ ≤ (R i * R j * (R i * R j * R k * R l)) * U :=
          Nat.mul_le_mul (Nat.mul_le_mul_right _ e1) e2
      _ = U * (R i ^ 2 * R j ^ 2 * R k * R l) := by ring
  have h3 : U * K ≤ U * (M * (R i ^ 2 * R j ^ 2 * R k * R l)) := by
    calc U * K = K * U := mul_comm _ _
      _ ≤ M * L * ∏ z, R z := hmain
      _ = M * (L * ∏ z, R z) := by ring
      _ ≤ M * (U * (R i ^ 2 * R j ^ 2 * R k * R l)) := Nat.mul_le_mul_left _ h1
      _ = U * (M * (R i ^ 2 * R j ^ 2 * R k * R l)) := by ring
  exact Nat.le_of_mul_le_mul_left h3 hU0

/-- A passed vertex has the four-cell bound `289 · 9⁶ / 1024`. -/
theorem vok17_quad {R : Fin 6 → ℕ} (h : vok17 R = true) (i j k l : Fin 6) (hij : i ≠ j)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    (531441 * 289 / 1024 : ℝ) ≤ (R i : ℝ) ^ 2 * (R j : ℝ) ^ 2 * (R k : ℝ) * (R l : ℝ) := by
  simp only [vok17, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hL0, hmain⟩ := h
  have hprod : ∏ z, R z = R 0 * R 1 * R 2 * R 3 * R 4 * R 5 := Fin.prod_univ_six R
  have key := quad_bound_gen R (K := 153586449) (M := 1024) hL0
    (pair_bounds R (vL_le_lt R) (le_vU_lt R)) (by rw [hprod]; exact hmain) i j k l hij hik hil
    hjk hjl hkl
  have : ((153586449 : ℕ) : ℝ) ≤ ((1024 * (R i ^ 2 * R j ^ 2 * R k * R l) : ℕ) : ℝ) := by
    exact_mod_cast key
  push_cast at this
  linarith

/-! ### From a checked case to the four-cell bound -/

/-- **A checked case gives the four-cell bound `17/32`.** -/
theorem genHull17_of_case (c : HCase) (hc : c.consOK ∧ c.tabOK ∧ c.flOK ∧ c.vertOK17) :
    SqHullOK17 (patOfCode c.code) c.e := by
  obtain ⟨hcons, htab, hfl, hv3, hvt⟩ := hc
  intro w hw A hA hidx i j k l hij hik hil hjk hjl hkl
  obtain ⟨μ₀, μ, h0, hμ, hok, h1, hx⟩ :=
    hidx.1 (sigOf c.si) ⟨fun a b e => sigOf_inj _ a b e, fun s t h => (hcons s t h).symm⟩
  have hflo := hidx.2
  set P := patOfCode c.code with hP
  set σ := sigOf c.si with hσ
  set G : Fin 6 → ℝ := fun r => genF (sqB₁ P c.e) (sqEl P c.e) (sqB₂ P c.e) w (offPair r).1
    (offPair r).2 with hG
  -- the root value against the mixture
  have hlow : ∀ r, A * (μ₀ * (3 * ∑ z, (c.t r z : ℝ) + c.f r)
      + ∑ t, μ t * (∑ z, (c.t r z : ℝ) * vtx t z + c.f r)) ≤ 3 * G r := by
    intro r
    set D : Fin 3 → ℝ := fun s => if sqEl P c.e s (σ s) = true then 0 else
      (sqB₁ P c.e (offPair r).1 s : ℝ) * w s (σ s) * (sqB₂ P c.e (σ s) (offPair r).2 : ℝ)
      with hD
    have hfam : ∀ z : Fin 6, (if sqEl P c.e (offPair z).1 (σ (offPair z).2) = true then (0 : ℝ)
        else (sqB₁ P c.e (offPair r).1 (offPair z).1 : ℝ) * w (offPair z).1 (σ (offPair z).2)
          * (sqB₂ P c.e (σ (offPair z).2) (offPair r).2 : ℝ))
        = (c.t r z : ℝ) * w (offPair z).1 (σ (offPair z).2) := by
      intro z
      have hne : sqEl P c.e (offPair z).1 (σ (offPair z).2) = false := by
        cases h' : sqEl P c.e (offPair z).1 (σ (offPair z).2)
        · rfl
        · exact absurd (sigOf_inj _ _ _ (hcons _ _ h')).symm (offPair_ne z)
      rw [hne, htab r z]
      simp only [Bool.false_eq_true, ite_false]
      push_cast
      ring
    have hGr : G r = ∑ z, (c.t r z : ℝ) * w (offPair z).1 (σ (offPair z).2) + ∑ s, D s := by
      show genF _ _ _ _ _ _ = _
      unfold genF
      rw [sum_cells c.si]
      congr 1
      exact Finset.sum_congr rfl fun z _ => hfam z
    have hdiag : ∀ s, 2 / 3 * A * (flT P c.e σ r s : ℝ) ≤ D s := by
      intro s
      simp only [hD, flT]
      split_ifs with h
      · simp
      · push_cast
        have hw' := hflo s (σ s) (by simpa using h)
        have hb : 0 ≤ (sqB₁ P c.e (offPair r).1 s : ℝ) * (sqB₂ P c.e (σ s) (offPair r).2 : ℝ) :=
          mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        nlinarith
    have hA1 : ∑ z, (c.t r z : ℝ) * (A * (3 * μ₀ + ∑ t, μ t * vtx t z))
        ≤ 3 * ∑ z, (c.t r z : ℝ) * w (offPair z).1 (σ (offPair z).2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun z _ => ?_
      have := hx z
      have ht0 : (0 : ℝ) ≤ c.t r z := Nat.cast_nonneg _
      nlinarith
    have hA2 : A * (c.f r : ℝ) ≤ 3 * ∑ s, D s := by
      rw [hfl r, Fin.sum_univ_three]
      push_cast
      linarith [hdiag 0, hdiag 1, hdiag 2]
    have hsc : ∑ z, (c.t r z : ℝ) * (∑ t, μ t * vtx t z)
        = ∑ t, μ t * ∑ z, (c.t r z : ℝ) * vtx t z := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun z _ => by ring
    have hsplit2 : ∑ t, μ t * (∑ z, (c.t r z : ℝ) * vtx t z + c.f r)
        = ∑ t, μ t * ∑ z, (c.t r z : ℝ) * vtx t z + (∑ t, μ t) * c.f r := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun t _ => by ring
    have hexp : ∑ z, (c.t r z : ℝ) * (A * (3 * μ₀ + ∑ t, μ t * vtx t z))
        = A * (3 * μ₀ * ∑ z, (c.t r z : ℝ) + ∑ z, (c.t r z : ℝ) * (∑ t, μ t * vtx t z)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun z _ => by ring
    rw [hsplit2, hGr]
    rw [hexp, hsc] at hA1
    have hμs : ∑ t, μ t = 1 - μ₀ := by linarith
    rw [hμs]
    nlinarith [hA1, hA2]
  -- weighted AM–GM over the mixture
  set ω : Option Tr → ℝ := fun o => o.elim μ₀ μ with hω
  set val : Option Tr → Fin 6 → ℝ := fun o r => o.elim (3 * ∑ z, (c.t r z : ℝ) + c.f r)
    (fun t => ∑ z, (c.t r z : ℝ) * vtx t z + c.f r) with hval
  have hω0 : ∀ o, 0 ≤ ω o := fun o => by cases o <;> simp [hω, h0, hμ]
  have hω1 : ∑ o, ω o = 1 := by rw [Fintype.sum_option]; exact h1
  have hval0 : ∀ o r, 0 ≤ val o r := fun o r => by
    cases o
    · exact add_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg fun z _ => Nat.cast_nonneg _))
        (Nat.cast_nonneg _)
    · exact add_nonneg (Finset.sum_nonneg fun z _ => mul_nonneg (Nat.cast_nonneg _)
        (vtx_nonneg _ _)) (Nat.cast_nonneg _)
  set g : Fin 6 → ℝ := fun r => ∏ o, val o r ^ ω o with hg
  have hg0 : ∀ r, 0 ≤ g r := fun r => Finset.prod_nonneg fun o _ => Real.rpow_nonneg (hval0 o r) _
  have hAg : ∀ r, A * g r ≤ 3 * G r := fun r => by
    have hgm := Real.geom_mean_le_arith_mean_weighted univ ω (fun o => val o r)
      (fun o _ => hω0 o) hω1 (fun o _ => hval0 o r)
    have hmix : ∑ o, ω o * val o r = μ₀ * (3 * ∑ z, (c.t r z : ℝ) + c.f r)
        + ∑ t, μ t * (∑ z, (c.t r z : ℝ) * vtx t z + c.f r) := by
      rw [Fintype.sum_option]
      rfl
    rw [hmix] at hgm
    exact (mul_le_mul_of_nonneg_left hgm hA.le).trans (hlow r)
  -- each vertex in the mixture passes
  set Y : ℝ := 531441 * 289 / 1024 with hY
  have hvert : ∀ o, ω o ≠ 0 →
      Y ≤ val o i ^ 2 * val o j ^ 2 * val o k * val o l := by
    intro o ho
    cases o with
    | none =>
      have := vok17_quad hv3 i j k l hij hik hil hjk hjl hkl
      simpa only [hval, Option.elim, HCase.r3_cast] using this
    | some t =>
      have htok := hok t ho
      obtain ⟨t1, t2, t3⟩ := t
      obtain ⟨h12, h13, h23⟩ := htok
      rcases lt_or_gt_of_ne h23 with hlt | hgt
      · have := vok17_quad (hvt t1 t2 t3 h12 h13 hlt) i j k l hij hik hil hjk hjl hkl
        simpa only [hval, Option.elim, HCase.rv_cast c (t := (t1, t2, t3)) ⟨h12, h13, h23⟩] using this
      · have := vok17_quad (hvt t1 t3 t2 h13 h12 hgt) i j k l hij hik hil hjk hjl hkl
        have e := vtx_swap (t1, t2, t3)
        simp only [HCase.rv_cast c (t := (t1, t3, t2)) ⟨h13, h12, Ne.symm h23⟩] at this
        simpa only [hval, Option.elim, show vtx (t1, t3, t2) = vtx (t1, t2, t3) from e] using this
  have hgY : Y ≤ g i ^ 2 * g j ^ 2 * g k * g l := by
    have hprod : g i ^ 2 * g j ^ 2 * g k * g l
        = ∏ o, (val o i ^ 2 * val o j ^ 2 * val o k * val o l) ^ ω o := by
      simp only [hg, ← Finset.prod_pow]
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun o _ => ?_
      rw [rpow_sq_comm (hval0 _ _), rpow_sq_comm (hval0 _ _),
        Real.mul_rpow (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (hval0 _ _))
          (hval0 _ _),
        Real.mul_rpow (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (hval0 _ _),
        Real.mul_rpow (sq_nonneg _) (sq_nonneg _)]
    rw [hprod]
    have hY0 : (0 : ℝ) ≤ Y := by norm_num [hY]
    calc Y = Y ^ (∑ o, ω o) := by rw [hω1, Real.rpow_one]
      _ = ∏ o, Y ^ ω o := Real.rpow_sum_of_nonneg hY0 fun o _ => hω0 o
      _ ≤ _ := Finset.prod_le_prod₀ (fun o _ => Real.rpow_nonneg hY0 _) fun o _ => by
          by_cases ho : ω o = 0
          · rw [ho, Real.rpow_zero, Real.rpow_zero]
          · exact Real.rpow_le_rpow hY0 (hvert o ho) (hω0 o)
  -- assemble
  have hG0 : ∀ r, 0 ≤ A * g r := fun r => mul_nonneg hA.le (hg0 r)
  have key := four_le (hG0 i) (hG0 j) (hG0 k) (hG0 l) (hAg i) (hAg j) (hAg k) (hAg l)
  have hA6 : 0 ≤ A ^ 6 := by positivity
  have e1 : (A * g i) ^ 2 * (A * g j) ^ 2 * (A * g k) * (A * g l)
      = A ^ 6 * (g i ^ 2 * g j ^ 2 * g k * g l) := by ring
  have e2 : (3 * G i) ^ 2 * (3 * G j) ^ 2 * (3 * G k) * (3 * G l)
      = 729 * (G i ^ 2 * G j ^ 2 * G k * G l) := by ring
  rw [e1, e2] at key
  have := mul_le_mul_of_nonneg_left hgY hA6
  show (17 / 32) ^ 2 * (3 * A) ^ 6 ≤ G i ^ 2 * G j ^ 2 * G k * G l
  calc (17 / 32) ^ 2 * (3 * A) ^ 6 = A ^ 6 * Y / 729 := by rw [hY]; ring
    _ ≤ 729 * (G i ^ 2 * G j ^ 2 * G k * G l) / 729 :=
        div_le_div_of_nonneg_right (this.trans key) (by norm_num)
    _ = _ := by ring

end Outerplanar
