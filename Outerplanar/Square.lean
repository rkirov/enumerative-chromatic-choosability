/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.Loaded
import Outerplanar.OneLoad

/-!
# Squares with one loaded edge: reduction to patterns

A square `u, x₀, x₁, v` has four lists. Enumerate them by `Fin 3`; what the face sum sees of the
lists is the *pattern* `Pat`: for each of the four edges of the cycle, the pairs of indices
with equal colours.

* `genF_le_faceSum` — the face sum of a square with loaded edge `e`, at the root pair of indices
  `(a, b)`, is at least `genF` of the arc counts `sqB₁`, `sqB₂` computed from the pattern;
* `SqOK P e` — the statement `GenOK` for the pattern `P` and the loaded edge `e`, constant `3`;
  it is stronger for a pattern with more equal colours on the three path edges (`SqOK.mono`);
* `SqCover` — every pattern of four lists is, in suitable enumerations, below a pattern for which
  `SqOK` holds. The enumerations are first put in a normal form (each list aligned with the
  previous one around the cycle), in which a pattern is given by four subsets of `Fin 3` and a
  permutation;
* `ballFaceBare_two_of_cover` — `SqCover` gives the ball closure of squares, `BallFaceBare 2`.

`SqCover` itself is a finite statement; it is proved from certificates in
`Outerplanar/SquareCert.lean` and `Outerplanar/SqData/`, and `Outerplanar/SquareThm.lean` states
the results.
-/

namespace Outerplanar

open Finset

/-! ### The face sum of a square -/

theorem pathCol_two (c d : ℕ) (g : Fin 2 → ℕ) :
    pathCol c d g (Fin.castSucc (0 : Fin 3)) = c ∧ pathCol c d g (Fin.succ (0 : Fin 3)) = g 0 ∧
      pathCol c d g (Fin.castSucc (1 : Fin 3)) = g 0 ∧
      pathCol c d g (Fin.succ (1 : Fin 3)) = g 1 ∧
      pathCol c d g (Fin.castSucc (2 : Fin 3)) = g 1 ∧ pathCol c d g (Fin.succ (2 : Fin 3)) = d :=
  ⟨consSnoc_zero _ _ _ _ (by simp), consSnoc_mid _ _ _ _ (0 : Fin 2) (by simp),
    consSnoc_mid _ _ _ _ (0 : Fin 2) (by simp), consSnoc_mid _ _ _ _ (1 : Fin 2) (by simp),
    consSnoc_mid _ _ _ _ (1 : Fin 2) (by simp), consSnoc_last _ _ _ _ (by simp)⟩

theorem pathList_two (Lu Lv : Finset ℕ) (Li : Fin 2 → Finset ℕ) :
    pathList Lu Lv Li (Fin.castSucc (0 : Fin 3)) = Lu ∧
      pathList Lu Lv Li (Fin.succ (0 : Fin 3)) = Li 0 ∧
      pathList Lu Lv Li (Fin.castSucc (1 : Fin 3)) = Li 0 ∧
      pathList Lu Lv Li (Fin.succ (1 : Fin 3)) = Li 1 ∧
      pathList Lu Lv Li (Fin.castSucc (2 : Fin 3)) = Li 1 ∧
      pathList Lu Lv Li (Fin.succ (2 : Fin 3)) = Lv :=
  ⟨consSnoc_zero _ _ _ _ (by simp), consSnoc_mid _ _ _ _ (0 : Fin 2) (by simp),
    consSnoc_mid _ _ _ _ (0 : Fin 2) (by simp), consSnoc_mid _ _ _ _ (1 : Fin 2) (by simp),
    consSnoc_mid _ _ _ _ (1 : Fin 2) (by simp), consSnoc_last _ _ _ _ (by simp)⟩

/-- The face sum of a square as a double sum over the colours of its two interior vertices. -/
theorem faceSum_two (Li : Fin 2 → Finset ℕ) (E : Fin 3 → ℕ → ℕ → ℝ) (c d : ℕ) :
    faceSum Li (fun _ _ => 1) E c d = ∑ x ∈ Li 0, ∑ y ∈ Li 1, E 0 c x * E 1 x y * E 2 y d := by
  unfold faceSum
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_bij' (fun xy _ => ![xy.1, xy.2]) (fun g _ => (g 0, g 1)) ?_ ?_ ?_ ?_ ?_
  · intro xy hxy
    rw [Fintype.mem_piFinset]
    intro j
    fin_cases j
    · exact (mem_product.mp hxy).1
    · exact (mem_product.mp hxy).2
  · intro g hg
    exact mem_product.mpr ⟨Fintype.mem_piFinset.mp hg 0, Fintype.mem_piFinset.mp hg 1⟩
  · intro xy _
    rfl
  · intro g _
    funext j
    fin_cases j <;> rfl
  · intro xy _
    obtain ⟨p0, p1, p2, p3, p4, p5⟩ := pathCol_two c d ![xy.1, xy.2]
    rw [Fin.prod_univ_three, p0, p1, p2, p3, p4, p5]
    simp

/-- A sum over a list of three colours, along an enumeration. -/
theorem sum_enum {L : Finset ℕ} (hL : L.card = 3) {γ : Fin 3 → ℕ} (hγ : Function.Injective γ)
    (hm : ∀ j, γ j ∈ L) (f : ℕ → ℝ) : ∑ x ∈ L, f x = ∑ s, f (γ s) := by
  rw [← image_enum hL hγ hm, Finset.sum_image fun x _ y _ e => hγ e]

/-! ### Patterns -/

/-- The pattern of a square: the pairs of indices with equal colours on the three path edges
`u x₀`, `x₀ x₁`, `x₁ v` and on the root edge `u v`. -/
structure Pat where
  /-- equal colours at `u` and `x₀` -/
  e01 : BMat
  /-- equal colours at `x₀` and `x₁` -/
  e12 : BMat
  /-- equal colours at `x₁` and `v` -/
  e23 : BMat
  /-- equal colours at `u` and `v` -/
  e03 : BMat

/-- The pattern of four enumerated lists. -/
def patOf (α γ₀ γ₁ β : Fin 3 → ℕ) : Pat :=
  ⟨fun a s => decide (α a = γ₀ s), fun s t => decide (γ₀ s = γ₁ t),
    fun t b => decide (γ₁ t = β b), fun a b => decide (α a = β b)⟩

/-- `1` for a pair of different colours. -/
def nb (b : Bool) : ℕ := if b = true then 0 else 1

/-- The number of proper colourings of a path of two ordinary edges, by its end indices. -/
def arc2 (X Y : BMat) (a c : Fin 3) : ℕ :=
  nb (X a 0 || Y 0 c) + nb (X a 1 || Y 1 c) + nb (X a 2 || Y 2 c)

/-- The arc counts between the root end `u` and the loaded edge `e`. -/
def sqB₁ (P : Pat) (e : Fin 3) (a s : Fin 3) : ℕ :=
  if e = 0 then (if a = s then 1 else 0) else if e = 1 then nb (P.e01 a s)
  else arc2 P.e01 P.e12 a s

/-- The pattern on the loaded edge `e`. -/
def sqEl (P : Pat) (e : Fin 3) : BMat :=
  if e = 0 then P.e01 else if e = 1 then P.e12 else P.e23

/-- The arc counts between the loaded edge `e` and the root end `v`. -/
def sqB₂ (P : Pat) (e : Fin 3) (t b : Fin 3) : ℕ :=
  if e = 0 then arc2 P.e12 P.e23 t b else if e = 1 then nb (P.e23 t b)
  else (if t = b then 1 else 0)

/-- The square with pattern `P` and loaded edge `e` maps the ball class to the ball class, with
the constant multiplied by `3`. -/
def SqOK (P : Pat) (e : Fin 3) : Prop := GenOK (sqB₁ P e) (sqEl P e) (sqB₂ P e) P.e03 3

/-- `P` has fewer equal colours than `Q` on the path edges, and the same on the root edge. -/
structure PatLE (P Q : Pat) : Prop where
  h01 : ∀ a s, P.e01 a s = true → Q.e01 a s = true
  h12 : ∀ s t, P.e12 s t = true → Q.e12 s t = true
  h23 : ∀ t b, P.e23 t b = true → Q.e23 t b = true
  h03 : P.e03 = Q.e03

theorem nb_le {p q : Bool} (h : p = true → q = true) : nb q ≤ nb p := by
  cases p <;> cases q <;> simp_all [nb]

theorem nb_or (p q : Bool) : nb (p || q) = nb p * nb q := by
  cases p <;> cases q <;> rfl

theorem arc2_le {X Y X' Y' : BMat} (hX : ∀ a s, X a s = true → X' a s = true)
    (hY : ∀ a s, Y a s = true → Y' a s = true) (a c : Fin 3) : arc2 X' Y' a c ≤ arc2 X Y a c := by
  have key : ∀ s, nb (X' a s || Y' s c) ≤ nb (X a s || Y s c) := fun s => nb_le fun h => by
    rcases Bool.or_eq_true_iff.mp h with h | h
    · exact Bool.or_eq_true_iff.mpr (Or.inl (hX _ _ h))
    · exact Bool.or_eq_true_iff.mpr (Or.inr (hY _ _ h))
  exact Nat.add_le_add (Nat.add_le_add (key 0) (key 1)) (key 2)

theorem SqOK.mono {P Q : Pat} (h : PatLE P Q) {e : Fin 3} (hQ : SqOK Q e) : SqOK P e := by
  unfold SqOK at hQ ⊢
  rw [h.h03]
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

/-! ### The face sum against the index form -/

/-- The profile on the loaded edge `e`, read through the enumerations. -/
def sqW (α γ₀ γ₁ β : Fin 3 → ℕ) (W : ℕ → ℕ → ℝ) (e : Fin 3) (s t : Fin 3) : ℝ :=
  if e = 0 then W (α s) (γ₀ t) else if e = 1 then W (γ₀ s) (γ₁ t) else W (γ₁ s) (β t)

theorem nb_decide_cast (x y : ℕ) : ((nb (decide (x = y)) : ℕ) : ℝ) = if x ≠ y then 1 else 0 := by
  by_cases h : x = y <;> simp [nb, h]

theorem arc2_cast (X Y : BMat) (a c : Fin 3) :
    ((arc2 X Y a c : ℕ) : ℝ) = ∑ s, ((nb (X a s) : ℕ) : ℝ) * ((nb (Y s c) : ℕ) : ℝ) := by
  rw [Fin.sum_univ_three]
  unfold arc2
  simp only [nb_or]
  push_cast
  ring

/-- **The face sum of a square against the index form.** -/
theorem genF_le_faceSum {Li : Fin 2 → Finset ℕ} (hLi : ∀ j, (Li j).card = 3)
    {α γ₀ γ₁ β : Fin 3 → ℕ} (hγ₀ : Function.Injective γ₀) (hγ₁ : Function.Injective γ₁)
    (hγ₀m : ∀ s, γ₀ s ∈ Li 0) (hγ₁m : ∀ t, γ₁ t ∈ Li 1) {W : ℕ → ℕ → ℝ}
    (hW : ∀ c d, 0 ≤ W c d) (e a b : Fin 3) :
    genF (sqB₁ (patOf α γ₀ γ₁ β) e) (sqEl (patOf α γ₀ γ₁ β) e) (sqB₂ (patOf α γ₀ γ₁ β) e)
        (sqW α γ₀ γ₁ β W e) a b
      ≤ faceSum Li (fun _ _ => 1)
        (fun j => if j = e then W else fun c d => if c ≠ d then 1 else 0) (α a) (β b) := by
  have hne0 : ∀ x y : ℕ, (0 : ℝ) ≤ if x ≠ y then 1 else 0 := fun x y => by
    split_ifs <;> norm_num
  rw [faceSum_two, sum_enum (hLi 0) hγ₀ hγ₀m]
  simp only [sum_enum (hLi 1) hγ₁ hγ₁m]
  unfold genF
  fin_cases e
  · -- the loaded edge is `u x₀`
    have hL : ∀ s ∈ (univ : Finset (Fin 3)), s ≠ a →
        (∑ t, if sqEl (patOf α γ₀ γ₁ β) 0 s t = true then (0 : ℝ) else
          ((sqB₁ (patOf α γ₀ γ₁ β) 0 a s : ℕ) : ℝ) * sqW α γ₀ γ₁ β W 0 s t
            * ((sqB₂ (patOf α γ₀ γ₁ β) 0 t b : ℕ) : ℝ)) = 0 := fun s _ hs =>
      Finset.sum_eq_zero fun t _ => by
        simp [sqB₁, Ne.symm hs]
    show (∑ s, ∑ t, if sqEl (patOf α γ₀ γ₁ β) 0 s t = true then (0 : ℝ) else
          ((sqB₁ (patOf α γ₀ γ₁ β) 0 a s : ℕ) : ℝ) * sqW α γ₀ γ₁ β W 0 s t
            * ((sqB₂ (patOf α γ₀ γ₁ β) 0 t b : ℕ) : ℝ)) ≤ _
    rw [Finset.sum_eq_single a hL fun h => absurd (mem_univ a) h]
    refine Finset.sum_le_sum fun s _ => ?_
    have hrhs : (∑ t, (if (0 : Fin 3) = 0 then W else fun c d => if c ≠ d then 1 else 0)
          (α a) (γ₀ s)
        * (if (1 : Fin 3) = 0 then W else fun c d => if c ≠ d then 1 else 0) (γ₀ s) (γ₁ t)
        * (if (2 : Fin 3) = 0 then W else fun c d => if c ≠ d then 1 else 0) (γ₁ t) (β b))
        = W (α a) (γ₀ s) * ((arc2 (patOf α γ₀ γ₁ β).e12 (patOf α γ₀ γ₁ β).e23 s b : ℕ) : ℝ) := by
      rw [arc2_cast, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [patOf, nb_decide_cast]
      simp
    show _ ≤ ∑ t, (if (0 : Fin 3) = 0 then W else fun c d => if c ≠ d then 1 else 0)
          (α a) (γ₀ s)
        * (if (1 : Fin 3) = 0 then W else fun c d => if c ≠ d then 1 else 0) (γ₀ s) (γ₁ t)
        * (if (2 : Fin 3) = 0 then W else fun c d => if c ≠ d then 1 else 0) (γ₁ t) (β b)
    rw [hrhs]
    have hnn : 0 ≤ W (α a) (γ₀ s)
        * ((arc2 (patOf α γ₀ γ₁ β).e12 (patOf α γ₀ γ₁ β).e23 s b : ℕ) : ℝ) :=
      mul_nonneg (hW _ _) (Nat.cast_nonneg _)
    split_ifs
    · exact hnn
    · simp [sqB₁, sqW, sqB₂]
  · -- the loaded edge is `x₀ x₁`
    refine Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun t _ => ?_
    show (if sqEl (patOf α γ₀ γ₁ β) 1 s t = true then (0 : ℝ) else
          ((sqB₁ (patOf α γ₀ γ₁ β) 1 a s : ℕ) : ℝ) * sqW α γ₀ γ₁ β W 1 s t
            * ((sqB₂ (patOf α γ₀ γ₁ β) 1 t b : ℕ) : ℝ))
      ≤ (if (0 : Fin 3) = 1 then W else fun c d => if c ≠ d then 1 else 0) (α a) (γ₀ s)
        * (if (1 : Fin 3) = 1 then W else fun c d => if c ≠ d then 1 else 0) (γ₀ s) (γ₁ t)
        * (if (2 : Fin 3) = 1 then W else fun c d => if c ≠ d then 1 else 0) (γ₁ t) (β b)
    have e0 : (if (0 : Fin 3) = 1 then W else fun c d => if c ≠ d then 1 else 0)
        = fun c d => if c ≠ d then 1 else 0 := ite_eq_right (by decide)
    have e2 : (if (2 : Fin 3) = 1 then W else fun c d => if c ≠ d then 1 else 0)
        = fun c d => if c ≠ d then 1 else 0 := ite_eq_right (by decide)
    rw [e0, e2, ite_eq_left rfl]
    split_ifs with hE
    · exact mul_nonneg (mul_nonneg (hne0 _ _) (hW _ _)) (hne0 _ _)
    · by_cases h1 : α a = γ₀ s <;> by_cases h2 : γ₁ t = β b <;>
        simp [sqB₁, sqB₂, sqW, patOf, nb, h1, h2]
  · -- the loaded edge is `x₁ v`
    have hL : ∀ s ∈ (univ : Finset (Fin 3)), ∀ t ∈ (univ : Finset (Fin 3)), t ≠ b →
        (if sqEl (patOf α γ₀ γ₁ β) 2 s t = true then (0 : ℝ) else
          ((sqB₁ (patOf α γ₀ γ₁ β) 2 a s : ℕ) : ℝ) * sqW α γ₀ γ₁ β W 2 s t
            * ((sqB₂ (patOf α γ₀ γ₁ β) 2 t b : ℕ) : ℝ)) = 0 := fun s _ t _ ht => by
      simp [sqB₂, ht]
    show (∑ s, ∑ t, if sqEl (patOf α γ₀ γ₁ β) 2 s t = true then (0 : ℝ) else
          ((sqB₁ (patOf α γ₀ γ₁ β) 2 a s : ℕ) : ℝ) * sqW α γ₀ γ₁ β W 2 s t
            * ((sqB₂ (patOf α γ₀ γ₁ β) 2 t b : ℕ) : ℝ))
      ≤ ∑ s, ∑ t, (if (0 : Fin 3) = 2 then W else fun c d => if c ≠ d then 1 else 0)
          (α a) (γ₀ s)
        * (if (1 : Fin 3) = 2 then W else fun c d => if c ≠ d then 1 else 0) (γ₀ s) (γ₁ t)
        * (if (2 : Fin 3) = 2 then W else fun c d => if c ≠ d then 1 else 0) (γ₁ t) (β b)
    have e0 : (if (0 : Fin 3) = 2 then W else fun c d => if c ≠ d then 1 else 0)
        = fun c d => if c ≠ d then 1 else 0 := ite_eq_right (by decide)
    have e1 : (if (1 : Fin 3) = 2 then W else fun c d => if c ≠ d then 1 else 0)
        = fun c d => if c ≠ d then 1 else 0 := ite_eq_right (by decide)
    rw [e0, e1, ite_eq_left rfl, Finset.sum_comm (s := (univ : Finset (Fin 3)))
      (f := fun s t => (if α a ≠ γ₀ s then (1 : ℝ) else 0) * (if γ₀ s ≠ γ₁ t then 1 else 0)
        * W (γ₁ t) (β b))]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [Finset.sum_eq_single b (hL s (mem_univ s)) fun h => absurd (mem_univ b) h]
    have hrhs : (∑ y, (if α a ≠ γ₀ y then (1 : ℝ) else 0) * (if γ₀ y ≠ γ₁ s then 1 else 0)
          * W (γ₁ s) (β b))
        = ((arc2 (patOf α γ₀ γ₁ β).e01 (patOf α γ₀ γ₁ β).e12 a s : ℕ) : ℝ) * W (γ₁ s) (β b) := by
      rw [arc2_cast, Finset.sum_mul]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [patOf, nb_decide_cast]
    rw [hrhs]
    have hnn : 0 ≤ ((arc2 (patOf α γ₀ γ₁ β).e01 (patOf α γ₀ γ₁ β).e12 a s : ℕ) : ℝ)
        * W (γ₁ s) (β b) := mul_nonneg (Nat.cast_nonneg _) (hW _ _)
    split_ifs
    · exact hnn
    · simp [sqB₁, sqW, sqB₂]

/-! ### Normal form of the enumerations, and the covering statement -/

/-- The pattern of enumerations in normal form, renumbered. In normal form the enumeration of
`x₀` is aligned with that of `u`, the one of `x₁` with that of `x₀`, and `v` has an enumeration
aligned with that of `x₁`, in which the `b`-th colour of the given enumeration of `v` has index
`ρ b`; `d0`, `d1`, `d2`, `dr` say which indices carry equal colours. The renumberings are `π`
(at both `u` and `v`), `π₀`, `π₁`. -/
def normPat (d0 d1 d2 dr : Fin 3 → Bool) (ρ π π₀ π₁ : Fin 3 → Fin 3) : Pat :=
  ⟨fun a s => decide (π a = π₀ s) && d0 (π a), fun s t => decide (π₀ s = π₁ t) && d1 (π₀ s),
    fun t b => decide (π₁ t = ρ (π b)) && d2 (π₁ t), fun a b => decide (a = b) && dr (π a)⟩

/-- What four lists force on a pattern in normal form: three equal colours around the square
give the fourth. -/
structure NormCons (d0 d1 d2 dr : Fin 3 → Bool) (ρ : Fin 3 → Fin 3) : Prop where
  c1 : ∀ b, d0 (ρ b) = true → d1 (ρ b) = true → d2 (ρ b) = true → ρ b = b ∧ dr b = true
  c2 : ∀ a, d0 a = true → d1 a = true → dr a = true → ρ a = a ∧ d2 a = true
  c3 : ∀ a, d0 a = true → d2 (ρ a) = true → dr a = true → ρ a = a ∧ d1 a = true
  c4 : ∀ a, d1 (ρ a) = true → d2 (ρ a) = true → dr a = true → ρ a = a ∧ d0 a = true

/-- **The covering statement**: every pattern in normal form that four lists can have is, after
renumbering, below a pattern for which `SqOK` holds at every loaded edge. -/
def SqCover : Prop :=
  ∀ (d0 d1 d2 dr : Fin 3 → Bool) (ρ : Fin 3 → Fin 3), Function.Bijective ρ →
    NormCons d0 d1 d2 dr ρ →
    ∃ π π₀ π₁ : Fin 3 → Fin 3, Function.Bijective π ∧ Function.Bijective π₀ ∧
      Function.Bijective π₁ ∧ ∃ Q : Pat, (∀ e, SqOK Q e) ∧ PatLE (normPat d0 d1 d2 dr ρ π π₀ π₁) Q

/-- An enumeration of a list of three colours aligned with a given enumeration. -/
theorem exists_aligned {L : Finset ℕ} (hL : L.card = 3) {α : Fin 3 → ℕ}
    (hα : Function.Injective α) :
    ∃ γ : Fin 3 → ℕ, Function.Injective γ ∧ (∀ c, γ c ∈ L) ∧ ∀ c a, γ c = α a → a = c := by
  obtain ⟨γ, -, hγ, -, hγm, -, hγa, -, -⟩ := exists_aligned_pair hL hα hα fun a b e => hα e
  exact ⟨γ, hγ, hγm, hγa⟩

/-- **Squares preserve the ball class**, given the covering statement. -/
theorem ballFaceBare_two_of_cover (hcov : SqCover) : BallFaceBare 2 := by
  intro Lu Lv Li hLu hLv hLi j₀ W hW A hA hin
  have h3 : faceConst3 2 = ((3 : ℕ) : ℝ) := by norm_num [faceConst3]
  rw [h3]
  refine inBall_of_idx hLu hLv fun α β hα hβ hαm hβm hal => ?_
  -- enumerations in normal form
  obtain ⟨g₀, hg₀, hg₀m, hg₀a⟩ := exists_aligned (hLi 0) hα
  obtain ⟨g₁, hg₁, hg₁m, hg₁a⟩ := exists_aligned (hLi 1) hg₀
  obtain ⟨δ, hδ, hδm, hδa⟩ := exists_aligned hLv hg₁
  have hρex : ∀ b, ∃ t, δ t = β b := fun b => by
    have h := hβm b
    rw [← image_enum hLv hδ hδm] at h
    obtain ⟨t, -, ht⟩ := mem_image.mp h
    exact ⟨t, ht⟩
  choose ρ hρ using hρex
  have hρinj : Function.Injective ρ := fun b b' e => hβ (by rw [← hρ b, ← hρ b', e])
  have hρb : Function.Bijective ρ := ⟨hρinj, Finite.injective_iff_surjective.mp hρinj⟩
  -- the pattern in normal form
  have e01 : ∀ a s, α a = g₀ s ↔ a = s ∧ decide (α a = g₀ a) = true := fun a s =>
    ⟨fun e => by
      obtain rfl := hg₀a s a e.symm
      exact ⟨rfl, decide_eq_true e⟩, fun ⟨e, h⟩ => by rw [← e]; exact of_decide_eq_true h⟩
  have e12 : ∀ s t, g₀ s = g₁ t ↔ s = t ∧ decide (g₀ s = g₁ s) = true := fun s t =>
    ⟨fun e => by
      obtain rfl := hg₁a t s e.symm
      exact ⟨rfl, decide_eq_true e⟩, fun ⟨e, h⟩ => by rw [← e]; exact of_decide_eq_true h⟩
  have e23 : ∀ t b, g₁ t = β b ↔ t = ρ b ∧ decide (g₁ t = δ t) = true := fun t b =>
    ⟨fun e => by
      have e' : δ (ρ b) = g₁ t := by rw [hρ b, e]
      obtain rfl := hδa (ρ b) t e'
      exact ⟨rfl, decide_eq_true e'.symm⟩, fun ⟨e, h⟩ => by
      rw [← hρ b, ← e]; exact of_decide_eq_true h⟩
  have e03 : ∀ a b, α a = β b ↔ a = b ∧ decide (α a = β a) = true := fun a b =>
    ⟨fun e => by
      obtain rfl := hal a b e
      exact ⟨rfl, decide_eq_true e⟩, fun ⟨e, h⟩ => by rw [← e]; exact of_decide_eq_true h⟩
  have hcons : NormCons (fun a => decide (α a = g₀ a)) (fun s => decide (g₀ s = g₁ s))
      (fun t => decide (g₁ t = δ t)) (fun a => decide (α a = β a)) ρ := by
    refine ⟨fun b h0 h1 h2 => ?_, fun a h0 h1 hr => ?_, fun a h0 h2 hr => ?_,
      fun a h1 h2 hr => ?_⟩
    · have e : α (ρ b) = β b := by
        rw [of_decide_eq_true h0, of_decide_eq_true h1, of_decide_eq_true h2, hρ b]
      obtain h := hal _ _ e
      exact ⟨h, by rw [h] at e; exact decide_eq_true e⟩
    · have e : g₁ a = β a := by
        rw [← of_decide_eq_true h1, ← of_decide_eq_true h0, of_decide_eq_true hr]
      have h := ((e23 a a).mp e).1
      exact ⟨h.symm, ((e23 a a).mp e).2⟩
    · have e : g₀ a = g₁ (ρ a) := by
        rw [← of_decide_eq_true h0, of_decide_eq_true hr, of_decide_eq_true h2, hρ a]
      have h := ((e12 a (ρ a)).mp e).1
      exact ⟨h.symm, ((e12 a (ρ a)).mp e).2⟩
    · have e : α a = g₀ (ρ a) := by
        rw [of_decide_eq_true h1, of_decide_eq_true h2, hρ a, of_decide_eq_true hr]
      have h := ((e01 a (ρ a)).mp e).1
      exact ⟨h.symm, ((e01 a (ρ a)).mp e).2⟩
  obtain ⟨π, π₀, π₁, hπ, hπ₀, hπ₁, Q, hQ, hle⟩ := hcov _ _ _ _ ρ hρb hcons
  refine ⟨π, hπ, ?_⟩
  -- the renumbered enumerations
  have hα' : Function.Injective fun a => α (π a) := hα.comp hπ.1
  have hβ' : Function.Injective fun b => β (π b) := hβ.comp hπ.1
  have hγ₀ : Function.Injective fun s => g₀ (π₀ s) := hg₀.comp hπ₀.1
  have hγ₁ : Function.Injective fun t => g₁ (π₁ t) := hg₁.comp hπ₁.1
  have hP : patOf (fun a => α (π a)) (fun s => g₀ (π₀ s)) (fun t => g₁ (π₁ t))
        (fun b => β (π b))
      = normPat (fun a => decide (α a = g₀ a)) (fun s => decide (g₀ s = g₁ s))
        (fun t => decide (g₁ t = δ t)) (fun a => decide (α a = β a)) ρ π π₀ π₁ := by
    unfold patOf normPat
    congr 1
    · funext a s
      rw [Bool.eq_iff_iff, decide_eq_true_iff, Bool.and_eq_true, decide_eq_true_iff]
      exact e01 _ _
    · funext s t
      rw [Bool.eq_iff_iff, decide_eq_true_iff, Bool.and_eq_true, decide_eq_true_iff]
      exact e12 _ _
    · funext t b
      rw [Bool.eq_iff_iff, decide_eq_true_iff, Bool.and_eq_true, decide_eq_true_iff]
      exact e23 _ _
    · funext a b
      rw [Bool.eq_iff_iff, decide_eq_true_iff, Bool.and_eq_true, decide_eq_true_iff]
      exact (e03 _ _).trans ⟨fun ⟨e, h⟩ => ⟨hπ.1 e, h⟩, fun ⟨e, h⟩ => ⟨by rw [e], h⟩⟩
  have hok : SqOK (patOf (fun a => α (π a)) (fun s => g₀ (π₀ s)) (fun t => g₁ (π₁ t))
      (fun b => β (π b))) j₀ := by
    rw [hP]
    exact (hQ j₀).mono hle
  -- the loaded edge in index form
  obtain ⟨l0, l1, l2, l3, l4, l5⟩ := pathList_two Lu Lv Li
  have hidx : IdxBall (sqEl (patOf (fun a => α (π a)) (fun s => g₀ (π₀ s))
      (fun t => g₁ (π₁ t)) (fun b => β (π b))) j₀)
      (sqW (fun a => α (π a)) (fun s => g₀ (π₀ s)) (fun t => g₁ (π₁ t)) (fun b => β (π b)) W j₀)
      A := by
    fin_cases j₀
    · have h := hin
      rw [show Fin.castSucc (⟨0, by decide⟩ : Fin 3) = Fin.castSucc (0 : Fin 3) from rfl,
        show Fin.succ (⟨0, by decide⟩ : Fin 3) = Fin.succ (0 : Fin 3) from rfl, l0, l1] at h
      exact h.idx hα' hγ₀ (fun a => hαm _) fun s => hg₀m _
    · have h := hin
      rw [show Fin.castSucc (⟨1, by decide⟩ : Fin 3) = Fin.castSucc (1 : Fin 3) from rfl,
        show Fin.succ (⟨1, by decide⟩ : Fin 3) = Fin.succ (1 : Fin 3) from rfl, l2, l3] at h
      exact h.idx hγ₀ hγ₁ (fun s => hg₀m _) fun t => hg₁m _
    · have h := hin
      rw [show Fin.castSucc (⟨2, by decide⟩ : Fin 3) = Fin.castSucc (2 : Fin 3) from rfl,
        show Fin.succ (⟨2, by decide⟩ : Fin 3) = Fin.succ (2 : Fin 3) from rfl, l4, l5] at h
      exact h.idx hγ₁ hβ' (fun t => hg₁m _) fun b => hβm _
  have hsqW : ∀ s t, 0 ≤ sqW (fun a => α (π a)) (fun s => g₀ (π₀ s)) (fun t => g₁ (π₁ t))
      (fun b => β (π b)) W j₀ s t := fun s t => by
    unfold sqW
    split_ifs <;> exact hW _ _
  exact (hok _ hsqW A hA hidx).mono (genF_nonneg _ _ _ hsqW) fun a b =>
    genF_le_faceSum hLi hγ₀ hγ₁ (fun s => hg₀m _) (fun t => hg₁m _) hW j₀ a b

end Outerplanar
