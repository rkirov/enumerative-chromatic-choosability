/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.BallAdd
import Outerplanar.Square

/-!
# The vertex ball class

When a face is cut (a stretch of ordinary edges has many colourings whatever the colours of its
two ends), the part of the face that carries the loaded edge is only seen through one end vertex:
it is a function `g` of the colour of that vertex. `VBall S g A` is the class of such *vertex
profiles* that the ball class induces:

`A ^ 600 ≤ ∏_{c ∈ S} g c ^ (200 ± 9)`,

with `+9` at one colour and `-9` at another (or at the same one). In index form this is `VIdx`.

* `InBall.vBall_left`, `InBall.vBall_right` — a pair profile in the ball class, summed over the
  colour of one end, is in the vertex ball class at the other end, with the constant doubled;
* `VBall.step` — passing an ordinary edge doubles the constant: `c ↦ ∑_{x ≠ c} g x`;
* `VBall.inBall_left`, `VBall.inBall_right` — a pair profile that depends on one end only, through
  a vertex profile of the class, is in the ball class.
-/

namespace Outerplanar

open Finset

/-! ### Index form -/

/-- The exponent of the index `i`: `200`, with `9` moved from `y` to `x`. -/
def vw (x y i : Fin 3) : ℕ := 200 + (if i = x then 9 else 0) - (if i = y then 9 else 0)

/-- The vertex ball class in index form. -/
def VIdx (h : Fin 3 → ℝ) (A : ℝ) : Prop := ∀ x y : Fin 3, A ^ 600 ≤ ∏ i, h i ^ vw x y i

theorem vw_sum : ∀ x y : Fin 3, vw x y 0 + vw x y 1 + vw x y 2 = 600 := by decide

theorem vw_self : ∀ x i : Fin 3, vw x x i = 200 := by decide

theorem vw_compl : ∀ x y : Fin 3, vw x y 1 + vw x y 2 = vw y x 0 + 200 ∧
    vw x y 0 + vw x y 2 = vw y x 1 + 200 ∧ vw x y 0 + vw x y 1 = vw y x 2 + 200 := by decide

theorem VIdx.mono {h h' : Fin 3 → ℝ} {A : ℝ} (hI : VIdx h A) (h0 : ∀ i, 0 ≤ h i)
    (hle : ∀ i, h i ≤ h' i) : VIdx h' A := fun x y =>
  (hI x y).trans (prod_le_prod₀ (fun i _ => pow_nonneg (h0 i) _)
    fun i _ => pow_le_pow_left₀ (h0 i) (hle i) _)

theorem VIdx.smul {h : Fin 3 → ℝ} {A : ℝ} (hI : VIdx h A) (κ : ℝ) :
    VIdx (fun i => κ * h i) (κ * A) := fun x y => by
  have e : ∏ i, (κ * h i) ^ vw x y i = κ ^ 600 * ∏ i, h i ^ vw x y i := by
    simp only [mul_pow, prod_mul_distrib]
    rw [Fin.prod_univ_three (fun i => κ ^ vw x y i), ← pow_add, ← pow_add, vw_sum]
  rw [e, mul_pow]
  exact mul_le_mul_of_nonneg_left (hI x y) (by positivity)

/-- From squares to the statement. -/
theorem le_of_sq_le_sq' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b :=
  (pow_le_pow_iff_left₀ ha hb (by norm_num)).mp h

theorem two_mul_pow_sq (A : ℝ) : ((2 * A) ^ 600) ^ 2 = 4 ^ 600 * (A ^ 600 * A ^ 600) := by
  calc ((2 * A) ^ 600) ^ 2 = ((2 * A) ^ 2) ^ 600 := by rw [← pow_mul, ← pow_mul, mul_comm]
    _ = (4 * (A * A)) ^ 600 := by congr 1; ring
    _ = 4 ^ 600 * (A ^ 600 * A ^ 600) := by rw [mul_pow, mul_pow]

theorem sq_pow3 (a b c : ℝ) (n m k : ℕ) :
    (a ^ 2) ^ n * (b ^ 2) ^ m * (c ^ 2) ^ k = (a ^ n * b ^ m * c ^ k) ^ 2 := by
  ring

theorem four_mul_le_sq {u v t : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (h : u + v ≤ t) :
    4 * (u * v) ≤ t ^ 2 := by
  have h1 : (u + v) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (add_nonneg hu hv) h 2
  nlinarith [sq_nonneg (u - v)]

/-- **An ordinary edge, in index form**: if `h' i` is at least the sum of the two values of `h`
at the other indices, the constant doubles. -/
theorem VIdx.step {h h' : Fin 3 → ℝ} {A : ℝ} (hI : VIdx h A) (hA : 0 ≤ A) (h0 : ∀ i, 0 ≤ h i)
    (h'0 : ∀ i, 0 ≤ h' i) (s0 : h 1 + h 2 ≤ h' 0) (s1 : h 0 + h 2 ≤ h' 1)
    (s2 : h 0 + h 1 ≤ h' 2) : VIdx h' (2 * A) := by
  intro x y
  rw [Fin.prod_univ_three]
  obtain ⟨c0, c1, c2⟩ := vw_compl x y
  have q0 := four_mul_le_sq (h0 1) (h0 2) s0
  have q1 := four_mul_le_sq (h0 0) (h0 2) s1
  have q2 := four_mul_le_sq (h0 0) (h0 1) s2
  have k1 := hI y x
  have k2 := hI x x
  rw [Fin.prod_univ_three] at k1 k2
  simp only [vw_self] at k2
  have hprod0 : 0 ≤ h' 0 ^ vw x y 0 * h' 1 ^ vw x y 1 * h' 2 ^ vw x y 2 :=
    mul_nonneg (mul_nonneg (pow_nonneg (h'0 0) _) (pow_nonneg (h'0 1) _)) (pow_nonneg (h'0 2) _)
  refine le_of_sq_le_sq' (pow_nonneg (mul_nonneg (by norm_num) hA) _) hprod0 ?_
  have e0 : 0 ≤ 4 * (h 1 * h 2) := by have := h0 1; have := h0 2; positivity
  have e1 : 0 ≤ 4 * (h 0 * h 2) := by have := h0 0; have := h0 2; positivity
  have e2 : 0 ≤ 4 * (h 0 * h 1) := by have := h0 0; have := h0 1; positivity
  calc ((2 * A) ^ 600) ^ 2 = 4 ^ 600 * (A ^ 600 * A ^ 600) := two_mul_pow_sq A
    _ ≤ 4 ^ 600 * ((h 0 ^ vw y x 0 * h 1 ^ vw y x 1 * h 2 ^ vw y x 2)
          * (h 0 ^ 200 * h 1 ^ 200 * h 2 ^ 200)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul k1 k2 (pow_nonneg hA _) ?_) (by norm_num)
        exact (pow_nonneg hA _).trans k1
    _ = (4 * (h 1 * h 2)) ^ vw x y 0 * (4 * (h 0 * h 2)) ^ vw x y 1
          * (4 * (h 0 * h 1)) ^ vw x y 2 := by
        have e600 : (4 : ℝ) ^ 600 = 4 ^ vw x y 0 * 4 ^ vw x y 1 * 4 ^ vw x y 2 := by
          rw [← pow_add, ← pow_add, vw_sum]
        have f0 : h 0 ^ vw y x 0 * h 0 ^ 200 = h 0 ^ vw x y 1 * h 0 ^ vw x y 2 := by
          rw [← pow_add, ← pow_add, c0]
        have f1 : h 1 ^ vw y x 1 * h 1 ^ 200 = h 1 ^ vw x y 0 * h 1 ^ vw x y 2 := by
          rw [← pow_add, ← pow_add, c1]
        have f2 : h 2 ^ vw y x 2 * h 2 ^ 200 = h 2 ^ vw x y 0 * h 2 ^ vw x y 1 := by
          rw [← pow_add, ← pow_add, c2]
        simp only [mul_pow]
        calc 4 ^ 600 * ((h 0 ^ vw y x 0 * h 1 ^ vw y x 1 * h 2 ^ vw y x 2)
              * (h 0 ^ 200 * h 1 ^ 200 * h 2 ^ 200))
            = 4 ^ 600 * ((h 0 ^ vw y x 0 * h 0 ^ 200) * (h 1 ^ vw y x 1 * h 1 ^ 200)
              * (h 2 ^ vw y x 2 * h 2 ^ 200)) := by congr 1; ring
          _ = _ := by
            rw [e600, f0, f1, f2]
            ring
    _ ≤ (h' 0 ^ 2) ^ vw x y 0 * (h' 1 ^ 2) ^ vw x y 1 * (h' 2 ^ 2) ^ vw x y 2 :=
        mul_le_mul (mul_le_mul (pow_le_pow_left₀ e0 q0 _) (pow_le_pow_left₀ e1 q1 _)
          (pow_nonneg e1 _) (pow_nonneg (sq_nonneg _) _)) (pow_le_pow_left₀ e2 q2 _)
          (pow_nonneg e2 _)
          (mul_nonneg (pow_nonneg (sq_nonneg _) _) (pow_nonneg (sq_nonneg _) _))
    _ = (h' 0 ^ vw x y 0 * h' 1 ^ vw x y 1 * h' 2 ^ vw x y 2) ^ 2 := sq_pow3 _ _ _ _ _ _

/-! ### Between pair profiles and vertex profiles, in index form -/

/-- The product over a set with one element removed, as a product over everything. -/
theorem prod_erase_eq_ite {ι : Type*} [Fintype ι] [DecidableEq ι] (j : ι) (f : ι → ℝ) :
    ∏ k ∈ univ.erase j, f k = ∏ k, if k = j then 1 else f k := by
  rw [← Finset.mul_prod_erase univ (fun k => if k = j then 1 else f k) (mem_univ j), ite_eq_left rfl,
    one_mul]
  exact Finset.prod_congr rfl fun k hk => by rw [ite_eq_right (Finset.ne_of_mem_erase hk)]

/-- An inequality of the ball class as one product over the six good pairs. -/
theorem IdxBallAt.mon {E : BMat} {w : Fin 3 → Fin 3 → ℝ} {A : ℝ} (hI : IdxBallAt id E w A)
    (hE : ∀ c d, E c d = true → c = d) (j r : Fin 6) :
    A ^ 600 ≤ ∏ k : Fin 6, w (offPair k).1 (offPair k).2
      ^ ((if k = j then 91 else 100) + (if k = r then 9 else 0)) := by
  have hr : E (offPair r).1 (offPair r).2 = false := by
    by_contra hne
    rw [Bool.not_eq_false] at hne
    exact offPair_ne r (hE _ _ hne)
  have h1 := hI j _ _ hr
  have e : ∏ k : Fin 6, w (offPair k).1 (offPair k).2
        ^ ((if k = j then 91 else 100) + (if k = r then 9 else 0))
      = (∏ k ∈ univ.erase j, w (gp id k).1 (gp id k).2) ^ 100 * w (gp id j).1 (gp id j).2 ^ 91
        * w (offPair r).1 (offPair r).2 ^ 9 := by
    simp only [pow_add, prod_mul_distrib]
    congr 1
    · rw [← Finset.mul_prod_erase univ _ (mem_univ j), ite_eq_left rfl, ← Finset.prod_pow, mul_comm]
      congr 1
      exact Finset.prod_congr rfl fun k hk => by rw [ite_eq_right (Finset.ne_of_mem_erase hk)]; rfl
    · rw [Finset.prod_eq_single r (fun k _ hk => by rw [ite_eq_right hk, pow_zero])
        (fun h => absurd (mem_univ r) h), ite_eq_left rfl]
  rw [e]
  exact h1

/-- The two good pairs with first index `y`. -/
def dn (y : Fin 3) (e : Fin 2) : Fin 6 := ⟨2 * y.val + e.val, by omega⟩

theorem dn_expo (x y : Fin 3) (k : Fin 6) :
    ((if k = dn y 0 then 91 else 100) + (if k = dn x 0 then 9 else 0))
      + ((if k = dn y 1 then 91 else 100) + (if k = dn x 1 then 9 else 0))
      = vw x y (offPair k).1 := by
  fin_cases x <;> fin_cases y <;> fin_cases k <;> rfl

/-- **A pair profile summed over its second index**: the vertex profile
`h i = w i j₁ + w i j₂` (the two indices other than `i`) is in the vertex ball class, with the
constant doubled. -/
theorem IdxBallAt.vertex {E : BMat} {w : Fin 3 → Fin 3 → ℝ} {A : ℝ} (hI : IdxBallAt id E w A)
    (hE : ∀ c d, E c d = true → c = d) (hA : 0 ≤ A) (hw : ∀ c d, 0 ≤ w c d) {h : Fin 3 → ℝ}
    (s0 : w 0 1 + w 0 2 ≤ h 0) (s1 : w 1 0 + w 1 2 ≤ h 1) (s2 : w 2 0 + w 2 1 ≤ h 2) :
    VIdx h (2 * A) := by
  intro x y
  have h0 : ∀ i, 0 ≤ h i := fun i => by
    fin_cases i
    · exact (add_nonneg (hw _ _) (hw _ _)).trans s0
    · exact (add_nonneg (hw _ _) (hw _ _)).trans s1
    · exact (add_nonneg (hw _ _) (hw _ _)).trans s2
  have q0 := four_mul_le_sq (hw 0 1) (hw 0 2) s0
  have q1 := four_mul_le_sq (hw 1 0) (hw 1 2) s1
  have q2 := four_mul_le_sq (hw 2 0) (hw 2 1) s2
  have k1 := hI.mon hE (dn y 0) (dn x 0)
  have k2 := hI.mon hE (dn y 1) (dn x 1)
  have kk : A ^ 600 * A ^ 600 ≤ ∏ k : Fin 6, w (offPair k).1 (offPair k).2
      ^ vw x y (offPair k).1 := by
    have h12 := mul_le_mul k1 k2 (pow_nonneg hA _) ((pow_nonneg hA _).trans k1)
    rw [← prod_mul_distrib] at h12
    refine h12.trans (le_of_eq (Finset.prod_congr rfl fun k _ => ?_))
    rw [← pow_add, dn_expo]
  rw [Fin.prod_univ_six] at kk
  simp only [offPair] at kk
  simp only [Matrix.cons_val] at kk
  rw [Fin.prod_univ_three]
  have hprod0 : 0 ≤ h 0 ^ vw x y 0 * h 1 ^ vw x y 1 * h 2 ^ vw x y 2 :=
    mul_nonneg (mul_nonneg (pow_nonneg (h0 0) _) (pow_nonneg (h0 1) _)) (pow_nonneg (h0 2) _)
  refine le_of_sq_le_sq' (pow_nonneg (mul_nonneg (by norm_num) hA) _) hprod0 ?_
  have e0 : 0 ≤ 4 * (w 0 1 * w 0 2) := by have := hw 0 1; have := hw 0 2; positivity
  have e1 : 0 ≤ 4 * (w 1 0 * w 1 2) := by have := hw 1 0; have := hw 1 2; positivity
  have e2 : 0 ≤ 4 * (w 2 0 * w 2 1) := by have := hw 2 0; have := hw 2 1; positivity
  calc ((2 * A) ^ 600) ^ 2 = 4 ^ 600 * (A ^ 600 * A ^ 600) := two_mul_pow_sq A
    _ ≤ 4 ^ 600 * (w 0 1 ^ vw x y 0 * w 0 2 ^ vw x y 0 * w 1 0 ^ vw x y 1 * w 1 2 ^ vw x y 1
          * w 2 0 ^ vw x y 2 * w 2 1 ^ vw x y 2) :=
        mul_le_mul_of_nonneg_left kk (by norm_num)
    _ = (4 * (w 0 1 * w 0 2)) ^ vw x y 0 * (4 * (w 1 0 * w 1 2)) ^ vw x y 1
          * (4 * (w 2 0 * w 2 1)) ^ vw x y 2 := by
        have e600 : (4 : ℝ) ^ 600 = 4 ^ vw x y 0 * 4 ^ vw x y 1 * 4 ^ vw x y 2 := by
          rw [← pow_add, ← pow_add, vw_sum]
        simp only [mul_pow]
        rw [e600]
        ring
    _ ≤ (h 0 ^ 2) ^ vw x y 0 * (h 1 ^ 2) ^ vw x y 1 * (h 2 ^ 2) ^ vw x y 2 :=
        mul_le_mul (mul_le_mul (pow_le_pow_left₀ e0 q0 _) (pow_le_pow_left₀ e1 q1 _)
          (pow_nonneg e1 _) (pow_nonneg (sq_nonneg _) _)) (pow_le_pow_left₀ e2 q2 _)
          (pow_nonneg e2 _)
          (mul_nonneg (pow_nonneg (sq_nonneg _) _) (pow_nonneg (sq_nonneg _) _))
    _ = (h 0 ^ vw x y 0 * h 1 ^ vw x y 1 * h 2 ^ vw x y 2) ^ 2 := sq_pow3 _ _ _ _ _ _

theorem vw_root (j : Fin 6) (c i : Fin 3) :
    (if (offPair 0).1 = i then (if (0 : Fin 6) = j then 91 else 100) else 0)
      + (if (offPair 1).1 = i then (if (1 : Fin 6) = j then 91 else 100) else 0)
      + (if (offPair 2).1 = i then (if (2 : Fin 6) = j then 91 else 100) else 0)
      + (if (offPair 3).1 = i then (if (3 : Fin 6) = j then 91 else 100) else 0)
      + (if (offPair 4).1 = i then (if (4 : Fin 6) = j then 91 else 100) else 0)
      + (if (offPair 5).1 = i then (if (5 : Fin 6) = j then 91 else 100) else 0)
      + (if c = i then 9 else 0) = vw c (offPair j).1 i := by
  fin_cases j <;> fin_cases c <;> fin_cases i <;> rfl

/-- **A pair profile that depends on its first index only**, through a vertex profile of the
vertex ball class, is in the ball class. -/
theorem VIdx.root {h : Fin 3 → ℝ} {A : ℝ} (hI : VIdx h A) (E : BMat) :
    IdxBallAt id E (fun a _ => h a) A := by
  intro j c d _
  have key := hI c (offPair j).1
  have e : (∏ k ∈ univ.erase j, h (gp id k).1) ^ 100 * h (gp id j).1 ^ 91 * h c ^ 9
      = ∏ i, h i ^ vw c (offPair j).1 i := by
    have e1 : (∏ k ∈ univ.erase j, h (gp id k).1) ^ 100 * h (gp id j).1 ^ 91
        = ∏ k : Fin 6, h (offPair k).1 ^ (if k = j then 91 else 100) := by
      rw [← Finset.mul_prod_erase univ _ (mem_univ j), ite_eq_left rfl, ← Finset.prod_pow, mul_comm]
      congr 1
      exact Finset.prod_congr rfl fun k hk => by rw [ite_eq_right (Finset.ne_of_mem_erase hk)]; rfl
    have e2 : ∀ (a : Fin 3) (n : ℕ), h a ^ n = ∏ i : Fin 3, h i ^ (if a = i then n else 0) :=
      fun a n => by
        rw [Finset.prod_eq_single a (fun i _ hi => by rw [ite_eq_right (Ne.symm hi), pow_zero])
          (fun hh => absurd (mem_univ a) hh), ite_eq_left rfl]
    rw [e1, Fin.prod_univ_six]
    rw [e2 (offPair 0).1, e2 (offPair 1).1, e2 (offPair 2).1, e2 (offPair 3).1, e2 (offPair 4).1,
      e2 (offPair 5).1, e2 c 9]
    simp only [← prod_mul_distrib, ← pow_add]
    exact Finset.prod_congr rfl fun i _ => by rw [vw_root j c i]
  show A ^ 600 ≤ (∏ k ∈ univ.erase j, h (gp id k).1) ^ 100 * h (gp id j).1 ^ 91 * h c ^ 9
  rw [e]
  exact key

/-! ### Colours -/

/-- The vertex ball class: a profile `g` on the colours of the list `S`. -/
def VBall (S : Finset ℕ) (g : ℕ → ℝ) (A : ℝ) : Prop :=
  ∀ ζ : Fin 3 → ℕ, Function.Injective ζ → (∀ i, ζ i ∈ S) → VIdx (fun i => g (ζ i)) A

variable {S T : Finset ℕ} {g g' : ℕ → ℝ} {A : ℝ}

theorem VBall.mono (h : VBall S g A) (h0 : ∀ c ∈ S, 0 ≤ g c) (hle : ∀ c ∈ S, g c ≤ g' c) :
    VBall S g' A := fun ζ hζ hm =>
  (h ζ hζ hm).mono (fun i => h0 _ (hm i)) fun i => hle _ (hm i)

theorem VBall.smul (h : VBall S g A) (κ : ℝ) : VBall S (fun c => κ * g c) (κ * A) :=
  fun ζ hζ hm => (h ζ hζ hm).smul κ

/-- **An ordinary edge**: from a vertex profile on the list `S` to the profile
`c ↦ ∑_{x ∈ S, x ≠ c} g x` on the list `T`; the constant doubles. -/
theorem VBall.step (h : VBall S g A) (hA : 0 ≤ A) (hS : S.card = 3) (h0 : ∀ c ∈ S, 0 ≤ g c) :
    VBall T (fun c => ∑ x ∈ S, (if c ≠ x then 1 else 0) * g x) (2 * A) := by
  intro ζ' hζ' hm'
  obtain ⟨ζ, hζ, hm, hal⟩ := exists_aligned hS hζ'
  have hI := h ζ hζ hm
  have hsum : ∀ i, (∑ x ∈ S, (if ζ' i ≠ x then 1 else 0) * g x)
      = ∑ j, (if ζ' i ≠ ζ j then 1 else 0) * g (ζ j) := fun i =>
    sum_enum hS hζ hm fun x => (if ζ' i ≠ x then 1 else 0) * g x
  have hne : ∀ i j : Fin 3, i ≠ j → ζ' i ≠ ζ j := fun i j hij e => hij (hal j i e.symm)
  have hterm : ∀ i j : Fin 3, 0 ≤ (if ζ' i ≠ ζ j then (1 : ℝ) else 0) * g (ζ j) := fun i j =>
    mul_nonneg (by split_ifs <;> norm_num) (h0 _ (hm j))
  refine hI.step hA (fun i => h0 _ (hm i))
    (fun i => by
      show 0 ≤ ∑ x ∈ S, (if ζ' i ≠ x then 1 else 0) * g x
      rw [hsum]
      exact sum_nonneg fun j _ => hterm i j) ?_ ?_ ?_
  · show g (ζ 1) + g (ζ 2) ≤ ∑ x ∈ S, (if ζ' 0 ≠ x then 1 else 0) * g x
    rw [hsum, Fin.sum_univ_three, ite_eq_left (hne 0 1 (by decide)), ite_eq_left (hne 0 2 (by decide))]
    linarith [hterm 0 0]
  · show g (ζ 0) + g (ζ 2) ≤ ∑ x ∈ S, (if ζ' 1 ≠ x then 1 else 0) * g x
    rw [hsum, Fin.sum_univ_three, ite_eq_left (hne 1 0 (by decide)), ite_eq_left (hne 1 2 (by decide))]
    linarith [hterm 1 1]
  · show g (ζ 0) + g (ζ 1) ≤ ∑ x ∈ S, (if ζ' 2 ≠ x then 1 else 0) * g x
    rw [hsum, Fin.sum_univ_three, ite_eq_left (hne 2 0 (by decide)), ite_eq_left (hne 2 1 (by decide))]
    linarith [hterm 2 2]

variable {W : ℕ → ℕ → ℝ}

/-- **A pair profile summed over the colours of its second end** is a vertex profile of the
class at its first end, with the constant doubled. -/
theorem InBall.vBall_left (h : InBall S T W A) (hA : 0 ≤ A) (hT : T.card = 3)
    (hW : ∀ c d, 0 ≤ W c d) : VBall S (fun s => ∑ t ∈ T, W s t) (2 * A) := by
  intro ζ hζ hm
  obtain ⟨ξ, hξ, hξm, hal⟩ := exists_aligned hT hζ
  have hI := h.idx hζ hξ hm hξm id ⟨Function.injective_id, fun c d hcd =>
    (hal d c (of_decide_eq_true hcd).symm)⟩
  have hsum : ∀ i, (∑ t ∈ T, W (ζ i) t) = ∑ j, W (ζ i) (ξ j) := fun i =>
    sum_enum hT hξ hξm fun t => W (ζ i) t
  refine IdxBallAt.vertex (h := fun i => ∑ t ∈ T, W (ζ i) t) hI (fun c d hcd =>
    (hal d c (of_decide_eq_true hcd).symm)) hA (fun c d => hW _ _) ?_ ?_ ?_
  · show W (ζ 0) (ξ 1) + W (ζ 0) (ξ 2) ≤ ∑ t ∈ T, W (ζ 0) t
    rw [hsum, Fin.sum_univ_three]
    linarith [hW (ζ 0) (ξ 0)]
  · show W (ζ 1) (ξ 0) + W (ζ 1) (ξ 2) ≤ ∑ t ∈ T, W (ζ 1) t
    rw [hsum, Fin.sum_univ_three]
    linarith [hW (ζ 1) (ξ 1)]
  · show W (ζ 2) (ξ 0) + W (ζ 2) (ξ 1) ≤ ∑ t ∈ T, W (ζ 2) t
    rw [hsum, Fin.sum_univ_three]
    linarith [hW (ζ 2) (ξ 2)]

/-- The same at the second end. -/
theorem InBall.vBall_right (h : InBall S T W A) (hA : 0 ≤ A) (hS : S.card = 3)
    (hW : ∀ c d, 0 ≤ W c d) : VBall T (fun t => ∑ s ∈ S, W s t) (2 * A) :=
  h.swap.vBall_left hA hS fun d c => hW c d

/-- **A pair profile that depends on its first end only**, through a vertex profile of the
class. -/
theorem VBall.inBall_left (h : VBall S g A) (hS : S.card = 3) (hT : T.card = 3) :
    InBall S T (fun c _ => g c) A :=
  inBall_of_idx hS hT fun α _ hα _ hαm _ _ =>
    ⟨id, Function.bijective_id, (h α hα hαm).root _⟩

/-- The same for the second end. -/
theorem VBall.inBall_right (h : VBall T g A) (hS : S.card = 3) (hT : T.card = 3) :
    InBall S T (fun _ d => g d) A :=
  (h.inBall_left hT hS).swap

end Outerplanar
