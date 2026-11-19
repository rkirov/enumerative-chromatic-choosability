/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.TwoTree

/-!
# The ball invariant for three colours

A piece rooted at an edge `uv` has a pair profile `W c d` (the number of colourings with
`u ↦ c`, `v ↦ d`). For three colours and triangles below long faces the rank-one invariant
`HasPot` of `Outerplanar/Pot.lean` is too strong. The invariant of this file is weaker in one
direction and stronger in another.

Take six pairs of distinct colours `(p i, q i)` that are *matched* on the two lists (`Matched`
of `Outerplanar/SixFamily.lean`: the pairs `(α a, β b)`, `a ≠ b`, for enumerations of the lists
in which a common colour has the same index). These are the *good* pairs. `InBall S T W A` says
that for every such family, every good pair `j` and every pair `(c, d)` of distinct colours of
the two lists,

`A ^ 600 ≤ (∏_{k ≠ j} W (p k) (q k)) ^ 100 · W (p j) (q j) ^ 91 · W c d ^ 9`,

that is, weight `9` out of `100` may be moved from one good pair to any pair. In logarithms: the
mean of `log (W / A)` over the six good pairs is at least `3/200` times
`log W (p j) (q j) - log W c d`. So the geometric mean of the six good entries exceeds `A` by a margin
proportional to the spread of the profile. It is the profile form of "every law within
`ℓ¹`-distance `3/100` of the uniform law on the six good pairs is valid".

This is a result of this repository's 2026-11 AI research collaboration (research log
`ai_research_notes/OUTERPLANAR_K3_TRIANGLES_2026-11-10.md`, section "Twelfth pass"; proof and
certificates in `ai_research_notes/outerplanar/chain/cx/REPORT.md`). This file contains the
definitions and the facts that do not depend on the shape of a face: the class is closed under
entrywise products and under entrywise increase, it contains the profile of an ordinary edge,
and it gives the count `6 A` at a root.
-/

namespace Outerplanar

open Finset

/-! ### The invariant -/

/-- The colours of six matched pairs lie in the two lists. -/
theorem Matched.mem {Lu Lw : Finset ℕ} {p q : Fin 6 → ℕ} (h : Matched Lu Lw p q) (i : Fin 6) :
    p i ∈ Lu ∧ q i ∈ Lw := by
  obtain ⟨α, β, hα, hβ, hαm, hβm, hab⟩ := h
  obtain ⟨κ, hκb, hκ⟩ := matched_reindex hα hβ hab
  obtain ⟨j, rfl⟩ := hκb.2 i
  rw [(hκ j).1, (hκ j).2]
  exact ⟨hαm _, hβm _⟩

/-- The profile `W` on the lists `S`, `T` lies in the ball class with constant `A`. -/
def InBall (S T : Finset ℕ) (W : ℕ → ℕ → ℝ) (A : ℝ) : Prop :=
  ∀ p q : Fin 6 → ℕ, Matched S T p q → (∀ i, p i ≠ q i) → ∀ j : Fin 6, ∀ c ∈ S, ∀ d ∈ T,
    c ≠ d →
    A ^ 600 ≤ (∏ k ∈ univ.erase j, W (p k) (q k)) ^ 100 * W (p j) (q j) ^ 91 * W c d ^ 9

/-- `W` is at least `A` on every pair of distinct colours: the profile of a piece that can be
coloured greedily. -/
def Dominant (S T : Finset ℕ) (W : ℕ → ℕ → ℝ) (A : ℝ) : Prop :=
  ∀ c ∈ S, ∀ d ∈ T, c ≠ d → A ≤ W c d

variable {S T : Finset ℕ} {W W' : ℕ → ℕ → ℝ} {A A' : ℝ}

/-- The three factors of the invariant are monotone. -/
theorem ball_mul_le {x y z x' y' z' : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hxx : x ≤ x')
    (hyy : y ≤ y') (hzz : z ≤ z') : x ^ 100 * y ^ 91 * z ^ 9 ≤ x' ^ 100 * y' ^ 91 * z' ^ 9 :=
  mul_le_mul
    (mul_le_mul (pow_le_pow_left₀ hx hxx _) (pow_le_pow_left₀ hy hyy _) (pow_nonneg hy _)
      (pow_nonneg (hx.trans hxx) _))
    (pow_le_pow_left₀ hz hzz _) (pow_nonneg hz _)
    (mul_nonneg (pow_nonneg (hx.trans hxx) _) (pow_nonneg (hy.trans hyy) _))

theorem InBall.mono (h : InBall S T W A) (h0 : ∀ c d, 0 ≤ W c d)
    (hle : ∀ c ∈ S, ∀ d ∈ T, c ≠ d → W c d ≤ W' c d) : InBall S T W' A := by
  intro p q hm hpq j c hc d hd hcd
  have hk : ∀ k, W (p k) (q k) ≤ W' (p k) (q k) := fun k =>
    hle _ (hm.mem k).1 _ (hm.mem k).2 (hpq k)
  exact (h p q hm hpq j c hc d hd hcd).trans
    (ball_mul_le (Finset.prod_nonneg fun k _ => h0 _ _) (h0 _ _) (h0 _ _)
      (Finset.prod_le_prod₀ (fun k _ => h0 _ _) fun k _ => hk k) (hk j) (hle c hc d hd hcd))

theorem InBall.mul (hA : 0 ≤ A) (hA' : 0 ≤ A') (h : InBall S T W A) (h' : InBall S T W' A') :
    InBall S T (fun c d => W c d * W' c d) (A * A') := by
  intro p q hm hpq j c hc d hd hcd
  have h1 := h p q hm hpq j c hc d hd hcd
  have h2 := h' p q hm hpq j c hc d hd hcd
  have e : (∏ k ∈ univ.erase j, W (p k) (q k) * W' (p k) (q k)) ^ 100
        * (W (p j) (q j) * W' (p j) (q j)) ^ 91 * (W c d * W' c d) ^ 9
      = ((∏ k ∈ univ.erase j, W (p k) (q k)) ^ 100 * W (p j) (q j) ^ 91 * W c d ^ 9)
        * ((∏ k ∈ univ.erase j, W' (p k) (q k)) ^ 100 * W' (p j) (q j) ^ 91 * W' c d ^ 9) := by
    rw [Finset.prod_mul_distrib]
    ring
  show (A * A') ^ 600 ≤ (∏ k ∈ univ.erase j, W (p k) (q k) * W' (p k) (q k)) ^ 100
    * (W (p j) (q j) * W' (p j) (q j)) ^ 91 * (W c d * W' c d) ^ 9
  rw [mul_pow, e]
  exact mul_le_mul h1 h2 (pow_nonneg hA' _) ((pow_nonneg hA _).trans h1)

theorem InBall.swap (h : InBall S T W A) : InBall T S (fun d c => W c d) A :=
  fun p q hm hpq j c hc d hd hcd =>
    h q p hm.symm (fun i => (hpq i).symm) j d hd c hc hcd.symm

/-- The profile of an ordinary edge. -/
theorem inBall_ne (S T : Finset ℕ) : InBall S T (fun c d => if c ≠ d then 1 else 0) 1 := by
  intro p q hm hpq j c hc d hd hcd
  show (1 : ℝ) ^ 600 ≤ (∏ k ∈ univ.erase j, (if p k ≠ q k then (1 : ℝ) else 0)) ^ 100
    * (if p j ≠ q j then (1 : ℝ) else 0) ^ 91 * (if c ≠ d then (1 : ℝ) else 0) ^ 9
  have e : ∀ k, (if p k ≠ q k then (1 : ℝ) else 0) = 1 := fun k => ite_eq_left (hpq k)
  simp only [e, ite_eq_left hcd, Finset.prod_const_one, one_pow, mul_one, le_refl]

theorem Dominant.inBall (hA : 0 ≤ A) (h : Dominant S T W A) : InBall S T W A := by
  intro p q hm hpq j c hc d hd hcd
  have hk : ∀ k, A ≤ W (p k) (q k) := fun k => h _ (hm.mem k).1 _ (hm.mem k).2 (hpq k)
  have h1 : A ^ 5 ≤ ∏ k ∈ univ.erase j, W (p k) (q k) := by
    calc A ^ 5 = ∏ _k ∈ univ.erase j, A := by
          rw [Finset.prod_const, Finset.card_erase_of_mem (mem_univ j)]
          simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => hA) fun k _ => hk k
  calc A ^ 600 = (A ^ 5) ^ 100 * A ^ 91 * A ^ 9 := by ring
    _ ≤ _ := ball_mul_le (pow_nonneg hA _) hA hA h1 (hk j) (h c hc d hd hcd)

theorem Dominant.swap (h : Dominant S T W A) : Dominant T S (fun d c => W c d) A :=
  fun d hd c hc hdc => h c hc d hd (Ne.symm hdc)

theorem Dominant.mul (hA : 0 ≤ A) (hA' : 0 ≤ A') (h : Dominant S T W A)
    (h' : Dominant S T W' A') : Dominant S T (fun c d => W c d * W' c d) (A * A') :=
  fun c hc d hd hcd => mul_le_mul (h c hc d hd hcd) (h' c hc d hd hcd) hA'
    (hA.trans (h c hc d hd hcd))

theorem dominant_ne (S T : Finset ℕ) : Dominant S T (fun c d => if c ≠ d then 1 else 0) 1 :=
  fun c _ d _ hcd => by simp [hcd]

/-! ### The hexagon inequality and the count at a root -/

/-- **The hexagon inequality**: the product of the six good entries is at least `A ^ 6`. -/
theorem InBall.hex (h : InBall S T W A) (hA : 0 ≤ A) (h0 : ∀ c d, 0 ≤ W c d)
    {p q : Fin 6 → ℕ} (hm : Matched S T p q) (hpq : ∀ i, p i ≠ q i) :
    A ^ 6 ≤ ∏ k, W (p k) (q k) := by
  have h1 := h p q hm hpq 0 _ (hm.mem 0).1 _ (hm.mem 0).2 (hpq 0)
  have e : (∏ k ∈ univ.erase (0 : Fin 6), W (p k) (q k)) ^ 100 * W (p 0) (q 0) ^ 91
      * W (p 0) (q 0) ^ 9 = (∏ k, W (p k) (q k)) ^ 100 := by
    rw [← Finset.mul_prod_erase univ (fun k => W (p k) (q k)) (mem_univ (0 : Fin 6))]
    ring
  rw [e] at h1
  have hP0 : 0 ≤ ∏ k, W (p k) (q k) := Finset.prod_nonneg fun k _ => h0 _ _
  have key : (A ^ 6) ^ 100 ≤ (∏ k, W (p k) (q k)) ^ 100 := by
    rw [← pow_mul]
    exact h1
  exact (pow_le_pow_iff_left₀ (pow_nonneg hA _) hP0 (by norm_num)).mp key

/-- **The count at a root**: the profile sums to at least `6 A`. -/
theorem InBall.sum_ge (hS : S.card = 3) (hT : T.card = 3) (h : InBall S T W A) (hA : 0 < A)
    (h0 : ∀ c d, 0 ≤ W c d) : 6 * A ≤ ∑ c ∈ S, ∑ d ∈ T, W c d := by
  obtain ⟨p, q, hpS, hqT, hpq, hm⟩ := exists_matched hS hT
  have hhex := h.hex hA.le h0 hm hpq
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

end Outerplanar
