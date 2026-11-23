/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.OneLoad

/-!
# The hexagon class and the four-cell class

Two profile classes for three colours, on top of the matched six-families of
`Outerplanar/SixFamily.lean` (`Matched S T p q` with `p i ≠ q i`: the six pairs off a bijection
between the lists that fixes the common colours).

* `Hex S T W A` — the **hexagon bound**: on every matched six-family the product of the six
  entries is at least `A ^ 6`.
* `TB S T W A τ` — the **four-cell bound**: for every matched six-family and four distinct cells
  `i, j, k, l` of it, `W_i² W_j² W_k W_l ≥ τ² A⁶`. In the normalised profile `X = W / A` this is
  `X_i X_j √(X_k X_l) ≥ τ`, the quantity `T` of the research note
  `ai_research_notes/OUTERPLANAR_SIX_EVEN_2026-11-23.md`.

Facts proved here, independent of the shape of a face: both classes are monotone and
multiplicative and contain the `Dominant` profiles; the rank-one class `HasPot` is contained in
`Hex` (a six-family is two bijections); `Hex` gives the count `6 A` at a root (`Hex.sum_ge`);
and a triangle multiplies both classes (`hex_tri`, `tb_tri`, from `Matched.extend`).

This is part of the formalization of the six-even-face theorem, a result of this repository's
2026-11 AI research collaboration (proof in the note above, by a ChatGPT session; audited and
extended by Claude).
-/

namespace Outerplanar

open Finset

/-! ### The classes -/

/-- Every matched six-family has product at least `A ^ 6`. -/
def Hex (S T : Finset ℕ) (W : ℕ → ℕ → ℝ) (A : ℝ) : Prop :=
  ∀ p q : Fin 6 → ℕ, Matched S T p q → (∀ i, p i ≠ q i) → A ^ 6 ≤ ∏ i, W (p i) (q i)

/-- Four distinct cells of a matched six-family, two of them squared, have product at least
`τ² A⁶`. -/
def TB (S T : Finset ℕ) (W : ℕ → ℕ → ℝ) (A τ : ℝ) : Prop :=
  ∀ p q : Fin 6 → ℕ, Matched S T p q → (∀ i, p i ≠ q i) → ∀ i j k l : Fin 6,
    i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
    τ ^ 2 * A ^ 6 ≤ W (p i) (q i) ^ 2 * W (p j) (q j) ^ 2 * W (p k) (q k) * W (p l) (q l)

variable {S T : Finset ℕ} {W W' : ℕ → ℕ → ℝ} {A A' τ τ' : ℝ}

/-! ### Monotonicity and products -/

theorem Hex.mono (h : Hex S T W A) (h0 : ∀ c d, 0 ≤ W c d)
    (hle : ∀ c ∈ S, ∀ d ∈ T, c ≠ d → W c d ≤ W' c d) : Hex S T W' A := by
  intro p q hm hpq
  exact (h p q hm hpq).trans (Finset.prod_le_prod₀ (fun i _ => h0 _ _)
    fun i _ => hle _ (hm.mem i).1 _ (hm.mem i).2 (hpq i))

theorem four_le {a b c d a' b' c' d' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (h1 : a ≤ a') (h2 : b ≤ b') (h3 : c ≤ c') (h4 : d ≤ d') :
    a ^ 2 * b ^ 2 * c * d ≤ a' ^ 2 * b' ^ 2 * c' * d' := by
  have e1 := pow_le_pow_left₀ ha h1 2
  have e2 := pow_le_pow_left₀ hb h2 2
  have p1 : a ^ 2 * b ^ 2 ≤ a' ^ 2 * b' ^ 2 :=
    mul_le_mul e1 e2 (by positivity) ((pow_nonneg ha 2).trans e1)
  have p2 : a ^ 2 * b ^ 2 * c ≤ a' ^ 2 * b' ^ 2 * c' :=
    mul_le_mul p1 h3 hc ((by positivity : (0 : ℝ) ≤ a ^ 2 * b ^ 2).trans p1)
  exact mul_le_mul p2 h4 hd ((by positivity : (0 : ℝ) ≤ a ^ 2 * b ^ 2 * c).trans p2)

theorem TB.mono (h : TB S T W A τ) (h0 : ∀ c d, 0 ≤ W c d)
    (hle : ∀ c ∈ S, ∀ d ∈ T, c ≠ d → W c d ≤ W' c d) : TB S T W' A τ := by
  intro p q hm hpq i j k l hij hik hil hjk hjl hkl
  have hk : ∀ i, W (p i) (q i) ≤ W' (p i) (q i) := fun i =>
    hle _ (hm.mem i).1 _ (hm.mem i).2 (hpq i)
  exact (h p q hm hpq i j k l hij hik hil hjk hjl hkl).trans
    (four_le (h0 _ _) (h0 _ _) (h0 _ _) (h0 _ _) (hk i) (hk j) (hk k) (hk l))

theorem TB.anti (h : TB S T W A τ) (hτ' : 0 ≤ τ') (hle : τ' ≤ τ) : TB S T W A τ' := by
  intro p q hm hpq i j k l hij hik hil hjk hjl hkl
  refine le_trans ?_ (h p q hm hpq i j k l hij hik hil hjk hjl hkl)
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hτ' hle 2) (by positivity)

theorem Hex.mul (hA : 0 ≤ A) (hA' : 0 ≤ A') (h : Hex S T W A) (h' : Hex S T W' A') :
    Hex S T (fun c d => W c d * W' c d) (A * A') := by
  intro p q hm hpq
  rw [mul_pow, Finset.prod_mul_distrib]
  exact mul_le_mul (h p q hm hpq) (h' p q hm hpq) (pow_nonneg hA' _)
    ((pow_nonneg hA _).trans (h p q hm hpq))

theorem TB.mul (h : TB S T W A τ) (h' : TB S T W' A' τ') :
    TB S T (fun c d => W c d * W' c d) (A * A') (τ * τ') := by
  intro p q hm hpq i j k l hij hik hil hjk hjl hkl
  have h1 := h p q hm hpq i j k l hij hik hil hjk hjl hkl
  have h2 := h' p q hm hpq i j k l hij hik hil hjk hjl hkl
  have e : (τ * τ') ^ 2 * (A * A') ^ 6 = (τ ^ 2 * A ^ 6) * (τ' ^ 2 * A' ^ 6) := by ring
  rw [e]
  calc (τ ^ 2 * A ^ 6) * (τ' ^ 2 * A' ^ 6)
      ≤ (W (p i) (q i) ^ 2 * W (p j) (q j) ^ 2 * W (p k) (q k) * W (p l) (q l))
        * (W' (p i) (q i) ^ 2 * W' (p j) (q j) ^ 2 * W' (p k) (q k) * W' (p l) (q l)) :=
        mul_le_mul h1 h2 (by positivity) ((by positivity : (0 : ℝ) ≤ τ ^ 2 * A ^ 6).trans h1)
    _ = _ := by ring

/-! ### What the classes contain -/

theorem Dominant.hex (h : Dominant S T W A) (hA : 0 ≤ A) : Hex S T W A := by
  intro p q hm hpq
  calc A ^ 6 = ∏ _i : Fin 6, A := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => hA) fun i _ => h _ (hm.mem i).1 _ (hm.mem i).2 (hpq i)

theorem Dominant.tb (h : Dominant S T W A) (hA : 0 ≤ A) : TB S T W A 1 := by
  intro p q hm hpq i j k l _ _ _ _ _ _
  have hk : ∀ i, A ≤ W (p i) (q i) := fun i => h _ (hm.mem i).1 _ (hm.mem i).2 (hpq i)
  have := four_le hA hA hA hA (hk i) (hk j) (hk k) (hk l)
  calc (1 : ℝ) ^ 2 * A ^ 6 = A ^ 2 * A ^ 2 * A * A := by ring
    _ ≤ _ := this

theorem Dominant.hasPot (h : Dominant S T W A) : HasPot S T W A :=
  ⟨fun _ => 1, fun _ => 1, fun _ _ => one_pos, fun _ _ => one_pos, by simp, by simp,
    fun c hc d hd hcd => by rw [mul_one, mul_one]; exact h c hc d hd hcd⟩

/-- **A rank-one bound gives the hexagon bound**: on a six-family every colour of either list
occurs twice, so the potentials cancel. -/
theorem HasPot.hex (hS : S.card = 3) (hT : T.card = 3) (h : HasPot S T W A) (hA : 0 ≤ A) :
    Hex S T W A := by
  obtain ⟨a, b, ha, hb, hpa, hpb, hW⟩ := h
  intro p q hm hpq
  have hl := hm.prod_left hS a
  have hr := hm.symm.prod_left hT b
  rw [hpa, one_pow] at hl
  rw [hpb, one_pow] at hr
  calc A ^ 6 = ∏ i : Fin 6, A * (a (p i) * b (q i)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          Finset.prod_mul_distrib, hl, hr, mul_one, mul_one]
    _ ≤ ∏ i, W (p i) (q i) := Finset.prod_le_prod₀
        (fun i _ => mul_nonneg hA (mul_pos (ha _ (hm.mem i).1) (hb _ (hm.mem i).2)).le)
        fun i _ => hW _ (hm.mem i).1 _ (hm.mem i).2 (hpq i)

/-- **The count at a root**: a profile with the hexagon bound sums to at least `6 A`. -/
theorem Hex.sum_ge (hS : S.card = 3) (hT : T.card = 3) (h : Hex S T W A) (hA : 0 < A)
    (h0 : ∀ c d, 0 ≤ W c d) : 6 * A ≤ ∑ c ∈ S, ∑ d ∈ T, W c d := by
  obtain ⟨p, q, hpS, hqT, hpq, hm⟩ := exists_matched hS hT
  have hhex := h p q hm hpq
  have hprod : 0 < ∏ i, W (p i) (q i) := lt_of_lt_of_le (pow_pos hA 6) hhex
  have htpos : ∀ i, 0 < W (p i) (q i) := fun i =>
    lt_of_le_of_ne (h0 _ _) fun e => hprod.ne' (Finset.prod_eq_zero (mem_univ i) e.symm)
  set P : ℝ := (∏ i, W (p i) (q i)) ^ ((6 : ℕ) : ℝ)⁻¹ with hP
  have hPpos : 0 < P := Real.rpow_pos_of_pos hprod _
  have hP6 : ∏ i, W (p i) (q i) = P ^ 6 :=
    (Real.rpow_inv_natCast_pow hprod.le (by norm_num)).symm
  have hAP : A ≤ P := by
    rw [hP6] at hhex
    exact (pow_le_pow_iff_left₀ hA.le hPpos.le (by norm_num)).mp hhex
  have hsum := six_mul_le_sum htpos hPpos hP6
  have hle : ∑ i, W (p i) (q i) ≤ ∑ c ∈ S, ∑ d ∈ T, W c d := by
    rw [← Finset.sum_product']
    have hinj : ∀ i ∈ (univ : Finset (Fin 6)), ∀ i' ∈ (univ : Finset (Fin 6)),
        (p i, q i) = (p i', q i') → i = i' := fun i _ i' _ e =>
      hm.injective (congrArg Prod.fst e) (congrArg Prod.snd e)
    rw [← Finset.sum_image (f := fun x : ℕ × ℕ => W x.1 x.2) hinj]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => ?_) fun x _ _ => h0 _ _
    obtain ⟨i, -, rfl⟩ := mem_image.mp hx
    exact mem_product.mpr ⟨hpS i, hqT i⟩
  calc 6 * A ≤ 6 * P := by linarith
    _ ≤ ∑ i, W (p i) (q i) := hsum
    _ ≤ _ := hle

/-- Gluing two pieces along an edge: if both sides have the hexagon bound, the edge sees at
least `6 A A'` colourings. -/
theorem Hex.glue (hS : S.card = 3) (hT : T.card = 3) (h : Hex S T W A) (h' : Hex S T W' A')
    (hA : 0 < A) (hA' : 0 < A') (h0 : ∀ c d, 0 ≤ W c d) (h0' : ∀ c d, 0 ≤ W' c d) :
    6 * (A * A') ≤ ∑ c ∈ S, ∑ d ∈ T, W c d * W' c d :=
  (h.mul hA.le hA'.le h').sum_ge hS hT (mul_pos hA hA') fun c d => mul_nonneg (h0 c d) (h0' c d)

/-! ### Triangles -/

/-- A triangle multiplies the hexagon bounds of its two sides. -/
theorem hex_tri {Lu Lv : Finset ℕ} {Li : Fin 1 → Finset ℕ} (hLi : ∀ j, (Li j).card = 3)
    {E : Fin 2 → ℕ → ℕ → ℝ} (hE0 : ∀ j c d, 0 ≤ E j c d) {A : Fin 2 → ℝ} (hA : ∀ j, 0 ≤ A j)
    (hE : ∀ j : Fin 2, Hex (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    Hex Lu Lv (faceSum Li (fun _ _ => 1) E) (∏ j, A j) := by
  intro p q hm hpq
  obtain ⟨l0, l1, l2, l3⟩ := pathList_tri Lu Lv Li
  have hI0 : Hex Lu (Li 0) (E 0) (A 0) := by have := hE 0; rwa [l0, l1] at this
  have hI1 : Hex (Li 0) Lv (E 1) (A 1) := by have := hE 1; rwa [l2, l3] at this
  obtain ⟨g, hgm, hgp, hgq, hm0, hm1⟩ := hm.extend (hLi 0) hpq
  have k0 := hI0 p g hm0.symm fun i => (hgp i).symm
  have k1 := hI1 g q hm1 hgq
  rw [Fin.prod_univ_two, mul_pow]
  calc A 0 ^ 6 * A 1 ^ 6 ≤ (∏ i, E 0 (p i) (g i)) * ∏ i, E 1 (g i) (q i) :=
        mul_le_mul k0 k1 (pow_nonneg (hA 1) _) ((pow_nonneg (hA 0) _).trans k0)
    _ = ∏ i, E 0 (p i) (g i) * E 1 (g i) (q i) := (Finset.prod_mul_distrib).symm
    _ ≤ _ := Finset.prod_le_prod₀ (fun i _ => mul_nonneg (hE0 _ _ _) (hE0 _ _ _))
        fun i _ => tri_term_le Li E hE0 _ _ (hgm i)

/-- A triangle multiplies the four-cell bounds of its two sides. -/
theorem tb_tri {Lu Lv : Finset ℕ} {Li : Fin 1 → Finset ℕ} (hLi : ∀ j, (Li j).card = 3)
    {E : Fin 2 → ℕ → ℕ → ℝ} (hE0 : ∀ j c d, 0 ≤ E j c d) {A τ : Fin 2 → ℝ}
    (hE : ∀ j : Fin 2,
      TB (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j) (τ j)) :
    TB Lu Lv (faceSum Li (fun _ _ => 1) E) (∏ j, A j) (τ 0 * τ 1) := by
  intro p q hm hpq i j k l hij hik hil hjk hjl hkl
  obtain ⟨l0, l1, l2, l3⟩ := pathList_tri Lu Lv Li
  have hI0 : TB Lu (Li 0) (E 0) (A 0) (τ 0) := by have := hE 0; rwa [l0, l1] at this
  have hI1 : TB (Li 0) Lv (E 1) (A 1) (τ 1) := by have := hE 1; rwa [l2, l3] at this
  obtain ⟨g, hgm, hgp, hgq, hm0, hm1⟩ := hm.extend (hLi 0) hpq
  have k0 := hI0 p g hm0.symm (fun i => (hgp i).symm) i j k l hij hik hil hjk hjl hkl
  have k1 := hI1 g q hm1 hgq i j k l hij hik hil hjk hjl hkl
  set F := faceSum Li (fun _ _ => 1) E
  have hF : ∀ r, E 0 (p r) (g r) * E 1 (g r) (q r) ≤ F (p r) (q r) := fun r =>
    tri_term_le Li E hE0 _ _ (hgm r)
  have h00 : ∀ r, 0 ≤ E 0 (p r) (g r) * E 1 (g r) (q r) := fun r =>
    mul_nonneg (hE0 _ _ _) (hE0 _ _ _)
  have hprod := mul_le_mul k0 k1 (by positivity)
    ((by positivity : (0 : ℝ) ≤ τ 0 ^ 2 * A 0 ^ 6).trans k0)
  calc (τ 0 * τ 1) ^ 2 * (∏ j, A j) ^ 6 = (τ 0 ^ 2 * A 0 ^ 6) * (τ 1 ^ 2 * A 1 ^ 6) := by
        rw [Fin.prod_univ_two]; ring
    _ ≤ _ := hprod
    _ = (E 0 (p i) (g i) * E 1 (g i) (q i)) ^ 2 * (E 0 (p j) (g j) * E 1 (g j) (q j)) ^ 2
        * (E 0 (p k) (g k) * E 1 (g k) (q k)) * (E 0 (p l) (g l) * E 1 (g l) (q l)) := by ring
    _ ≤ _ := four_le (h00 i) (h00 j) (h00 k) (h00 l) (hF i) (hF j) (hF k) (hF l)

end Outerplanar
