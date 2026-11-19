/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.Loaded
import Outerplanar.BallKernel

/-!
# Certificates for a face with one loaded edge

`GenOK B₁ El B₂ Er α` (`Outerplanar/Loaded.lean`) is a family of inequalities, one for every
*instance*: a donor `j` among the six good root pairs and a recipient root pair `(c, d)` outside
`Er`. This file contains a checker for certificates of such instances and its soundness proof.

The face is given by numbers (`GCase`): the arc counts packed with 8 bits per entry, the two
patterns with one bit per entry. A certificate of an instance (`Inst`) consists of

* a matching `sg` of the loaded edge extending `El` (an index into the six permutations);
* a denominator `D` and a table `k` of natural numbers, `7 × 9`, packed with 12 bits per entry,
  with rows summing to `D`: row `i` is the conditional law, given the `i`-th root pair, of the
  pair on the loaded edge (the six good pairs of the matching, then its completed pairs). The
  seven root pairs are the six good ones and the recipient, with weights `n = 100`, except `91`
  at the donor and `9` at the recipient; `f i y = n i * k i y` are the joint masses;
* a plan: a list of vertices of the ball of the loaded edge (donor, recipient, multiplicity)
  whose weight vectors add up to `s` times the column sums of `f`.

`checkInst` checks this and the entropy inequality of `ball_instance_of_child`, all in natural
numbers; `checkCase` runs through the instances; `checkCase_sound` concludes `GenOK`.
The checks are evaluated by the kernel on concrete data (`decide +kernel`), so they are written
with explicit sums and with shifts of numerals rather than with `Finset` and lists.
-/

namespace Outerplanar

open Finset

/-! ### Explicit sums, products and conjunctions -/

/-- `g 0 + … + g 6`. -/
def sum7 (g : ℕ → ℕ) : ℕ := g 0 + g 1 + g 2 + g 3 + g 4 + g 5 + g 6

/-- `g 0 + … + g 8`. -/
def sum9 (g : ℕ → ℕ) : ℕ := g 0 + g 1 + g 2 + g 3 + g 4 + g 5 + g 6 + g 7 + g 8

/-- `g 0 * … * g 6`. -/
def prod7 (g : ℕ → ℕ) : ℕ := g 0 * g 1 * g 2 * g 3 * g 4 * g 5 * g 6

/-- `g 0 * … * g 8`. -/
def prod9 (g : ℕ → ℕ) : ℕ := g 0 * g 1 * g 2 * g 3 * g 4 * g 5 * g 6 * g 7 * g 8

/-- `p 0 && p 1 && p 2`. -/
def all3 (p : ℕ → Bool) : Bool := p 0 && p 1 && p 2

/-- `p 0 && … && p 5`. -/
def all6 (p : ℕ → Bool) : Bool := p 0 && p 1 && p 2 && p 3 && p 4 && p 5

/-- `p 0 && … && p 6`. -/
def all7 (p : ℕ → Bool) : Bool := p 0 && p 1 && p 2 && p 3 && p 4 && p 5 && p 6

/-- `p 0 && … && p 8`. -/
def all9 (p : ℕ → Bool) : Bool := p 0 && p 1 && p 2 && p 3 && p 4 && p 5 && p 6 && p 7 && p 8

theorem all3_lt {p : ℕ → Bool} (h : all3 p = true) {x : ℕ} (hx : x < 3) : p x = true := by
  simp only [all3, Bool.and_eq_true] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  interval_cases x
  exacts [h0, h1, h2]

theorem all6_lt {p : ℕ → Bool} (h : all6 p = true) {x : ℕ} (hx : x < 6) : p x = true := by
  simp only [all6, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := h
  interval_cases x
  exacts [h0, h1, h2, h3, h4, h5]

theorem all7_lt {p : ℕ → Bool} (h : all7 p = true) {x : ℕ} (hx : x < 7) : p x = true := by
  simp only [all7, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  interval_cases x
  exacts [h0, h1, h2, h3, h4, h5, h6]

theorem all9_lt {p : ℕ → Bool} (h : all9 p = true) {x : ℕ} (hx : x < 9) : p x = true := by
  simp only [all9, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  interval_cases x
  exacts [h0, h1, h2, h3, h4, h5, h6, h7, h8]

theorem sum9_mul (a : ℕ) (g : ℕ → ℕ) : sum9 (fun y => a * g y) = a * sum9 g := by
  unfold sum9
  ring

/-- The index of a column. -/
def colIdx : Col → ℕ
  | Sum.inl k => k.val
  | Sum.inr a => 6 + a.val

theorem colIdx_lt (y : Col) : colIdx y < 9 := by
  cases y with
  | inl k => exact lt_trans k.isLt (by norm_num)
  | inr a =>
    have := a.isLt
    show 6 + a.val < 9
    omega

theorem colIdx_inj {y z : Col} (h : colIdx y = colIdx z) : y = z := by
  cases y with
  | inl k =>
    cases z with
    | inl k' => exact congrArg Sum.inl (Fin.ext h)
    | inr a' =>
      exfalso
      have := k.isLt
      simp only [colIdx] at h
      omega
  | inr a =>
    cases z with
    | inl k' =>
      exfalso
      have := k'.isLt
      simp only [colIdx] at h
      omega
    | inr a' =>
      refine congrArg Sum.inr (Fin.ext ?_)
      simp only [colIdx] at h
      omega

theorem sum_col (g : ℕ → ℕ) : ∑ y : Col, g (colIdx y) = sum9 g := by
  rw [Fintype.sum_sum_type, Fin.sum_univ_six, Fin.sum_univ_three]
  show g 0 + g 1 + g 2 + g 3 + g 4 + g 5 + (g 6 + g 7 + g 8) = _
  unfold sum9
  ring

theorem prod_col (g : ℕ → ℕ) : ∏ y : Col, g (colIdx y) = prod9 g := by
  rw [Fintype.prod_sum_type, Fin.prod_univ_six, Fin.prod_univ_three]
  show g 0 * g 1 * g 2 * g 3 * g 4 * g 5 * (g 6 * g 7 * g 8) = _
  unfold prod9
  ring

theorem sum_fin7 (g : ℕ → ℕ) : ∑ i : Fin 7, g i.val = sum7 g := by
  rw [Fin.sum_univ_seven]
  rfl

theorem prod_fin7 (g : ℕ → ℕ) : ∏ i : Fin 7, g i.val = prod7 g := by
  rw [Fin.prod_univ_seven]
  rfl

/-! ### Packed tables -/

/-- The `i`-th digit of `c` in base `2 ^ b`. -/
def dig (b c i : ℕ) : ℕ := (c >>> (b * i)) % 2 ^ b

/-- The `i`-th bit of `c`. -/
def bitAt (c i : ℕ) : Bool := (c >>> i) % 2 == 1

/-- A face with one loaded edge, as numbers: `b1`, `b2` hold the arc counts (8 bits per entry),
`el`, `er` the patterns on the loaded edge and on the root edge (1 bit per entry); entry
`(x, y)` is at position `3 x + y`. -/
structure GCase where
  /-- arc counts between the root end `u` and the loaded edge -/
  b1 : ℕ
  /-- equal colours on the loaded edge -/
  el : ℕ
  /-- arc counts between the loaded edge and the root end `v` -/
  b2 : ℕ
  /-- equal colours on the root edge -/
  er : ℕ

/-- The arc counts at the root end `u`. -/
def GCase.B₁ (C : GCase) (a s : Fin 3) : ℕ := dig 8 C.b1 (3 * a.val + s.val)

/-- The arc counts at the root end `v`. -/
def GCase.B₂ (C : GCase) (t b : Fin 3) : ℕ := dig 8 C.b2 (3 * t.val + b.val)

/-- The pattern on the loaded edge. -/
def GCase.El (C : GCase) : BMat := fun s t => bitAt C.el (3 * s.val + t.val)

/-- The pattern on the root edge. -/
def GCase.Er (C : GCase) : BMat := fun a b => bitAt C.er (3 * a.val + b.val)

/-- The first index of the `k`-th good pair (`offPair`). -/
def offA (k : ℕ) : ℕ := dig 2 2640 k

/-- The second index of the `k`-th good pair (`offPair`). -/
def offB (k : ℕ) : ℕ := dig 2 1161 k

theorem offA_val : ∀ k : Fin 6, offA k.val = (offPair k).1.val := by decide +kernel

theorem offB_val : ∀ k : Fin 6, offB k.val = (offPair k).2.val := by decide +kernel

/-- The six permutations of three indices, on numbers. -/
def permN (sg x : ℕ) : ℕ := dig 2 6746936868 (3 * sg + x)

/-- The six permutations of three indices. -/
def perm6 (sg : ℕ) (x : Fin 3) : Fin 3 := ⟨permN sg x.val % 3, Nat.mod_lt _ (by norm_num)⟩

theorem perm6_val : ∀ sg : Fin 6, ∀ x : Fin 3, (perm6 sg.val x).val = permN sg.val x.val := by
  decide +kernel

theorem perm6_inj : ∀ sg : Fin 6, Function.Injective (perm6 sg.val) := by decide +kernel

theorem perm6_bij (sg : Fin 6) : Function.Bijective (perm6 sg.val) :=
  ⟨perm6_inj sg, Finite.injective_iff_surjective.mp (perm6_inj sg)⟩

/-! ### Rows and columns -/

/-- The root pair of row `i`: the six good pairs, then the recipient `(c, d)`. -/
def rp (c d : Fin 3) (i : Fin 7) : Fin 3 × Fin 3 :=
  if h : i.val < 6 then offPair ⟨i.val, h⟩ else (c, d)

/-- First index of the root pair of row `i`, on numbers. -/
def rowA (c i : ℕ) : ℕ := if i < 6 then offA i else c

/-- Second index of the root pair of row `i`, on numbers. -/
def rowB (d i : ℕ) : ℕ := if i < 6 then offB i else d

theorem rowA_val (c d : Fin 3) (i : Fin 7) : rowA c.val i.val = (rp c d i).1.val := by
  unfold rowA rp
  by_cases h : i.val < 6
  · rw [ite_eq_left h, dite_eq_left h]
    exact offA_val ⟨i.val, h⟩
  · rw [ite_eq_right h, dite_eq_right h]

theorem rowB_val (c d : Fin 3) (i : Fin 7) : rowB d.val i.val = (rp c d i).2.val := by
  unfold rowB rp
  by_cases h : i.val < 6
  · rw [ite_eq_left h, dite_eq_left h]
    exact offB_val ⟨i.val, h⟩
  · rw [ite_eq_right h, dite_eq_right h]

/-- The pair of indices on the loaded edge of a column, for the matching `σ`: its six good
pairs, then its completed pairs. -/
def colPair (σ : Fin 3 → Fin 3) : Col → Fin 3 × Fin 3
  | Sum.inl k => gp σ k
  | Sum.inr a => (a, σ a)

/-- First index of the pair of column `y`, on numbers. -/
def colS (y : ℕ) : ℕ := if y < 6 then offA y else y - 6

/-- Second index of the pair of column `y` for the matching `sg`, on numbers. -/
def colT (sg y : ℕ) : ℕ := permN sg (if y < 6 then offB y else y - 6)

theorem colS_val (σ : Fin 3 → Fin 3) (y : Col) : colS (colIdx y) = (colPair σ y).1.val := by
  cases y with
  | inl k =>
    show (if k.val < 6 then offA k.val else k.val - 6) = (offPair k).1.val
    rw [ite_eq_left k.isLt]
    exact offA_val k
  | inr a =>
    show (if 6 + a.val < 6 then offA (6 + a.val) else 6 + a.val - 6) = a.val
    rw [ite_eq_right (by omega)]
    omega

theorem colT_val (sg : Fin 6) (y : Col) :
    colT sg.val (colIdx y) = (colPair (perm6 sg.val) y).2.val := by
  cases y with
  | inl k =>
    show permN sg.val (if k.val < 6 then offB k.val else k.val - 6)
      = (perm6 sg.val (offPair k).2).val
    rw [ite_eq_left k.isLt, offB_val k, perm6_val sg]
  | inr a =>
    show permN sg.val (if 6 + a.val < 6 then offB (6 + a.val) else 6 + a.val - 6)
      = (perm6 sg.val a).val
    rw [ite_eq_right (by omega), perm6_val sg, Nat.add_sub_cancel_left]

theorem sum_colPair {σ : Fin 3 → Fin 3} (hσ : Function.Bijective σ) (g : Fin 3 → Fin 3 → ℝ) :
    ∑ y : Col, g (colPair σ y).1 (colPair σ y).2 = ∑ s, ∑ t, g s t := by
  have h : ∀ s, ∑ t, g s t = ∑ b, g s (σ b) := fun s => (hσ.sum_comp (g s)).symm
  simp only [h]
  rw [Fintype.sum_sum_type, Fin.sum_univ_six]
  simp only [Fin.sum_univ_three, colPair, gp, offPair]
  simp only [Matrix.cons_val]
  ring

/-- The number of threads: colourings of the face with root pair `(a, b)` and the pair
`(s, t)` on the loaded edge. -/
def tN (C : GCase) (a b s t : ℕ) : ℕ :=
  if bitAt C.el (3 * s + t) = true then 0 else dig 8 C.b1 (3 * a + s) * dig 8 C.b2 (3 * t + b)

theorem tN_val (C : GCase) (a b s t : Fin 3) :
    tN C a.val b.val s.val t.val = if C.El s t = true then 0 else C.B₁ a s * C.B₂ t b := rfl

/-- The profile of the loaded edge on the columns of the matching `σ`. A completed pair of
equal colours carries no thread; its column is given the value of a good pair. -/
def wCol (σ : Fin 3 → Fin 3) (E : BMat) (w : Fin 3 → Fin 3 → ℝ) : Col → ℝ
  | Sum.inl k => w (gp σ k).1 (gp σ k).2
  | Sum.inr a => if E a (σ a) = true then w (gp σ 0).1 (gp σ 0).2 else w a (σ a)

theorem wCol_nonneg {σ : Fin 3 → Fin 3} {E : BMat} {w : Fin 3 → Fin 3 → ℝ}
    (hw : ∀ s t, 0 ≤ w s t) (y : Col) : 0 ≤ wCol σ E w y := by
  cases y with
  | inl k => exact hw _ _
  | inr a =>
    show 0 ≤ if E a (σ a) = true then w (gp σ 0).1 (gp σ 0).2 else w a (σ a)
    split_ifs <;> exact hw _ _

/-- The ball inequalities of the loaded edge, on columns. -/
theorem wCol_ball {σ : Fin 3 → Fin 3} {E : BMat} {w : Fin 3 → Fin 3 → ℝ} {A : ℝ}
    (hσ : Compat σ E) (h : IdxBallAt σ E w A) (y : Fin 6) (z : Col) :
    A ^ 600 ≤ mono (wCol σ E w) (bv y z) := by
  rw [mono_bv]
  have hgood : ∀ k : Fin 6, E (gp σ k).1 (gp σ k).2 = false := fun k => by
    by_contra hne
    rw [Bool.not_eq_false] at hne
    exact offPair_ne k (hσ.1 (hσ.2 _ _ hne))
  cases z with
  | inl k => exact h y _ _ (hgood k)
  | inr a =>
    by_cases hE : E a (σ a) = true
    · have h1 := h y _ _ (hgood 0)
      show A ^ 600 ≤ (∏ k ∈ univ.erase y, w (gp σ k).1 (gp σ k).2) ^ 100
        * w (gp σ y).1 (gp σ y).2 ^ 91
        * (if E a (σ a) = true then w (gp σ 0).1 (gp σ 0).2 else w a (σ a)) ^ 9
      rw [ite_eq_left hE]
      exact h1
    · have h1 := h y a (σ a) (by simpa using hE)
      show A ^ 600 ≤ (∏ k ∈ univ.erase y, w (gp σ k).1 (gp σ k).2) ^ 100
        * w (gp σ y).1 (gp σ y).2 ^ 91
        * (if E a (σ a) = true then w (gp σ 0).1 (gp σ 0).2 else w a (σ a)) ^ 9
      rw [ite_eq_right hE]
      exact h1

/-- The profile of the face as a sum over columns of threads. -/
theorem sum_threads (C : GCase) (sg : Fin 6) (w : Fin 3 → Fin 3 → ℝ) (a b : Fin 3) :
    ∑ y : Col, ((tN C a.val b.val (colS (colIdx y)) (colT sg.val (colIdx y)) : ℕ) : ℝ)
        * wCol (perm6 sg.val) C.El w y
      = genF C.B₁ C.El C.B₂ w a b := by
  unfold genF
  rw [← sum_colPair (perm6_bij sg)
    (fun s t => if C.El s t = true then 0 else (C.B₁ a s : ℝ) * w s t * (C.B₂ t b : ℝ))]
  refine Finset.sum_congr rfl fun y _ => ?_
  have e : tN C a.val b.val (colS (colIdx y)) (colT sg.val (colIdx y))
      = if C.El (colPair (perm6 sg.val) y).1 (colPair (perm6 sg.val) y).2 = true then 0
        else C.B₁ a (colPair (perm6 sg.val) y).1 * C.B₂ (colPair (perm6 sg.val) y).2 b := by
    rw [colS_val (perm6 sg.val) y, colT_val sg y]
    rfl
  rw [e]
  cases y with
  | inl k =>
    show ((if C.El (gp (perm6 sg.val) k).1 (gp (perm6 sg.val) k).2 = true then 0
        else C.B₁ a (gp (perm6 sg.val) k).1 * C.B₂ (gp (perm6 sg.val) k).2 b : ℕ) : ℝ)
        * w (gp (perm6 sg.val) k).1 (gp (perm6 sg.val) k).2
      = if C.El (gp (perm6 sg.val) k).1 (gp (perm6 sg.val) k).2 = true then 0
        else (C.B₁ a (gp (perm6 sg.val) k).1 : ℝ) * w (gp (perm6 sg.val) k).1
          (gp (perm6 sg.val) k).2 * (C.B₂ (gp (perm6 sg.val) k).2 b : ℝ)
    split_ifs
    · simp
    · push_cast
      ring
  | inr a' =>
    show ((if C.El a' (perm6 sg.val a') = true then 0
        else C.B₁ a a' * C.B₂ (perm6 sg.val a') b : ℕ) : ℝ)
        * (if C.El a' (perm6 sg.val a') = true
          then w (gp (perm6 sg.val) 0).1 (gp (perm6 sg.val) 0).2 else w a' (perm6 sg.val a'))
      = if C.El a' (perm6 sg.val a') = true then 0
        else (C.B₁ a a' : ℝ) * w a' (perm6 sg.val a') * (C.B₂ (perm6 sg.val a') b : ℝ)
    split_ifs
    · simp
    · push_cast
      ring

/-! ### Plans -/

/-- The weight vector of a vertex of the ball of the loaded edge, on numbers (`bv`). -/
def bvN (yd z t : ℕ) : ℕ :=
  (if t < 6 then (if t = yd then 91 else 100) else 0) + (if t = z then 9 else 0)

/-- The column with index `z`. -/
def colOf (z : ℕ) : Col :=
  if h : z < 6 then Sum.inl ⟨z, h⟩ else Sum.inr ⟨(z - 6) % 3, Nat.mod_lt _ (by norm_num)⟩

theorem colIdx_colOf {z : ℕ} (hz : z < 9) : colIdx (colOf z) = z := by
  unfold colOf
  by_cases h : z < 6
  · rw [dite_eq_left h]
    rfl
  · rw [dite_eq_right h]
    show 6 + (z - 6) % 3 = z
    omega

theorem bv_eq {yd z : ℕ} (hy : yd < 6) (hz : z < 9) (t : Col) :
    bv ⟨yd, hy⟩ (colOf z) t = bvN yd z (colIdx t) := by
  have e2 : (if t = colOf z then 9 else 0) = if colIdx t = z then 9 else 0 := by
    by_cases h : t = colOf z
    · rw [ite_eq_left h, ite_eq_left (by rw [h, colIdx_colOf hz])]
    · rw [ite_eq_right h, ite_eq_right fun h' => h (colIdx_inj (by rw [h', colIdx_colOf hz]))]
  unfold bv bvN
  rw [e2]
  congr 1
  cases t with
  | inl k =>
    show (if k = ⟨yd, hy⟩ then 91 else 100) = if k.val < 6 then (if k.val = yd then 91 else 100)
      else 0
    rw [ite_eq_left k.isLt]
    by_cases h : k = ⟨yd, hy⟩
    · rw [ite_eq_left h, ite_eq_left (by rw [h])]
    · rw [ite_eq_right h, ite_eq_right fun h' => h (Fin.ext h')]
  | inr a =>
    show (0 : ℕ) = if 6 + a.val < 6 then (if 6 + a.val = yd then 91 else 100) else 0
    rw [ite_eq_right (by omega)]

/-- The sum of the weight vectors of a plan, at the column with index `t`. -/
def planSum (plan : List (ℕ × ℕ × ℕ)) (t : ℕ) : ℕ :=
  (plan.map fun p => p.2.2 * bvN p.1 p.2.1 t).sum

/-- The total multiplicity of a plan. -/
def planTot (plan : List (ℕ × ℕ × ℕ)) : ℕ := (plan.map fun p => p.2.2).sum

/-- The entries of a plan name donors and columns. -/
def planOK (plan : List (ℕ × ℕ × ℕ)) : Bool :=
  plan.all fun p => decide (p.1 < 6) && decide (p.2.1 < 9)

/-- The lower bound given by a plan of ball vertices. -/
theorem planN_bound {w : Col → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hball : ∀ (y : Fin 6) (z : Col), A ^ 600 ≤ mono w (bv y z)) :
    ∀ plan : List (ℕ × ℕ × ℕ), planOK plan = true →
      A ^ (600 * planTot plan) ≤ mono w fun t => planSum plan (colIdx t)
  | [], _ => by simp [planTot, planSum, mono]
  | p :: ps, h => by
    simp only [planOK, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hp1, hp2⟩, hps⟩ := h
    have ih := planN_bound hA hball ps hps
    have e : (fun t => planSum (p :: ps) (colIdx t))
        = p.2.2 • bv ⟨p.1, hp1⟩ (colOf p.2.1) + fun t => planSum ps (colIdx t) := by
      funext t
      simp only [planSum, List.map_cons, List.sum_cons, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        bv_eq hp1 hp2]
    have e2 : planTot (p :: ps) = p.2.2 + planTot ps := by simp [planTot]
    rw [e, mono_add, mono_smul, e2, mul_add, pow_add, pow_mul]
    have h1 := hball ⟨p.1, hp1⟩ (colOf p.2.1)
    exact mul_le_mul (pow_le_pow_left₀ (pow_nonneg hA _) h1 _) ih (pow_nonneg hA _)
      (pow_nonneg ((pow_nonneg hA _).trans h1) _)

/-! ### The checker -/

/-- A certificate of one instance. -/
structure Inst where
  /-- the matching of the loaded edge, an index into `perm6` -/
  sg : ℕ
  /-- the common denominator of the kernel -/
  D : ℕ
  /-- the plan decomposes `s` times the column sums -/
  s : ℕ
  /-- the kernel table, `7 × 9`, 12 bits per entry -/
  k : ℕ
  /-- the plan: donor column, recipient column, multiplicity -/
  plan : List (ℕ × ℕ × ℕ)

/-- A placeholder. -/
def Inst.zero : Inst := ⟨0, 0, 0, 0, []⟩

/-- The entry of the kernel table at row `i`, column `y`. -/
def Inst.kk (I : Inst) (i y : ℕ) : ℕ := dig 12 I.k (9 * i + y)

/-- The weight of root row `i`: `9` at the recipient, `91` at the donor `j`, else `100`. -/
def nW (j i : ℕ) : ℕ := if i = 6 then 9 else if i = j then 91 else 100

/-- The joint masses. -/
def Inst.f (I : Inst) (j i y : ℕ) : ℕ := nW j i * I.kk i y

/-- The check of one instance: donor `j`, recipient `(c, d)`. -/
def checkInst (α : ℕ) (C : GCase) (j c d : ℕ) (I : Inst) : Bool :=
  decide (I.sg < 6) && decide (0 < I.D) && decide (0 < I.s) &&
  all3 (fun s => all3 fun t => !bitAt C.el (3 * s + t) || permN I.sg s == t) &&
  all7 (fun i => sum9 (I.kk i) == I.D) &&
  planOK I.plan && (planTot I.plan == I.s * I.D) &&
  all9 (fun t => I.s * sum7 (fun i => I.f j i t) == planSum I.plan t) &&
  decide (α ^ (600 * I.D) * prod7 (fun i => prod9 fun y => I.f j i y ^ I.f j i y)
    ≤ prod7 (fun i => sum9 (I.f j i) ^ sum9 (I.f j i)) *
      prod7 (fun i => prod9 fun y =>
        tN C (rowA c i) (rowB d i) (colS y) (colT I.sg y) ^ I.f j i y))

/-- The product over the seven root rows. -/
theorem prod_rows (j : Fin 6) (F : Fin 7 → ℝ) (G : Fin 6 → ℝ) (x : ℝ)
    (hF : ∀ k : Fin 6, F k.castSucc = G k) (hl : F (Fin.last 6) = x) :
    ∏ i : Fin 7, F i ^ nW j.val i.val = (∏ k ∈ univ.erase j, G k) ^ 100 * G j ^ 91 * x ^ 9 := by
  rw [Fin.prod_univ_castSucc]
  have h6 : nW j.val (Fin.last 6).val = 9 := by
    show (if (6 : ℕ) = 6 then 9 else if 6 = j.val then 91 else 100) = 9
    rw [ite_eq_left rfl]
  have hk : ∀ k : Fin 6, nW j.val (k.castSucc).val = if k = j then 91 else 100 := fun k => by
    have hlt := k.isLt
    show (if k.val = 6 then 9 else if k.val = j.val then 91 else 100) = _
    rw [ite_eq_right (by omega)]
    by_cases h : k = j
    · rw [ite_eq_left h, ite_eq_left (by rw [h])]
    · rw [ite_eq_right h, ite_eq_right fun h' => h (Fin.ext h')]
  rw [h6, hl]
  congr 1
  simp only [hk, hF]
  rw [← Finset.mul_prod_erase univ _ (mem_univ j), ite_eq_left rfl, ← Finset.prod_pow, mul_comm]
  congr 1
  exact Finset.prod_congr rfl fun k hk' => by rw [ite_eq_right (Finset.ne_of_mem_erase hk')]

/-- **Soundness of the check of one instance.** -/
theorem checkInst_sound {α : ℕ} {C : GCase} {j : Fin 6} {c d : Fin 3} {I : Inst}
    (h : checkInst α C j.val c.val d.val I = true) {w : Fin 3 → Fin 3 → ℝ}
    (hw : ∀ s t, 0 ≤ w s t) {A : ℝ} (hA : 0 < A) (hball : IdxBall C.El w A) :
    ((α : ℝ) * A) ^ 600 ≤
      (∏ k ∈ univ.erase j, genF C.B₁ C.El C.B₂ w (offPair k).1 (offPair k).2) ^ 100
        * genF C.B₁ C.El C.B₂ w (offPair j).1 (offPair j).2 ^ 91
        * genF C.B₁ C.El C.B₂ w c d ^ 9 := by
  simp only [checkInst, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hsg, hD⟩, hs⟩, hcompat⟩, hrows⟩, hpok⟩, hptot⟩, hplan⟩, hnum⟩ := h
  -- the matching
  have hσ : Compat (perm6 I.sg) C.El := ⟨perm6_inj ⟨I.sg, hsg⟩, fun s t hst => by
    have h1 := all3_lt (all3_lt hcompat s.isLt) t.isLt
    have h2 : bitAt C.el (3 * s.val + t.val) = true := hst
    rw [h2] at h1
    simp only [Bool.not_true, Bool.false_or, beq_iff_eq] at h1
    exact Fin.ext ((perm6_val ⟨I.sg, hsg⟩ s).trans h1)⟩
  have hI := hball _ hσ
  -- the rows
  have hF : ∀ i : Fin 7,
      ∑ y : Col, ((tN C (rowA c.val i.val) (rowB d.val i.val) (colS (colIdx y))
          (colT I.sg (colIdx y)) : ℕ) : ℝ) * wCol (perm6 I.sg) C.El w y
        ≤ genF C.B₁ C.El C.B₂ w (rp c d i).1 (rp c d i).2 := fun i => by
    rw [rowA_val c d i, rowB_val c d i]
    exact (sum_threads C ⟨I.sg, hsg⟩ w _ _).le
  have hF0 : ∀ i : Fin 7, 0 ≤ genF C.B₁ C.El C.B₂ w (rp c d i).1 (rp c d i).2 := fun i =>
    genF_nonneg _ _ _ hw _ _
  have hrow : ∀ i : Fin 7, ∑ y : Col, I.f j.val i.val (colIdx y) = I.D * nW j.val i.val := by
    intro i
    rw [sum_col (I.f j.val i.val)]
    have h1 := all7_lt hrows i.isLt
    rw [beq_iff_eq] at h1
    show sum9 (fun y => nW j.val i.val * I.kk i.val y) = _
    rw [sum9_mul, h1, mul_comm]
  -- the child side
  have hchild : A ^ (600 * I.D)
      ≤ mono (wCol (perm6 I.sg) C.El w) fun y => ∑ i : Fin 7, I.f j.val i.val (colIdx y) := by
    have hp := planN_bound hA.le (wCol_ball hσ hI) I.plan hpok
    have e : (fun t : Col => planSum I.plan (colIdx t))
        = I.s • fun y : Col => ∑ i : Fin 7, I.f j.val i.val (colIdx y) := by
      funext t
      have h1 := all9_lt hplan (colIdx_lt t)
      rw [beq_iff_eq] at h1
      rw [Pi.smul_apply, smul_eq_mul, sum_fin7 (fun i => I.f j.val i (colIdx t))]
      exact h1.symm
    rw [e, mono_smul, hptot, show 600 * (I.s * I.D) = 600 * I.D * I.s by ring, pow_mul] at hp
    exact (pow_le_pow_iff_left₀ (pow_nonneg hA.le _) (mono_nonneg (wCol_nonneg hw) _) hs.ne').mp hp
  -- the entropy inequality
  have hnum' : α ^ (600 * I.D)
        * ∏ i : Fin 7, ∏ y : Col, I.f j.val i.val (colIdx y) ^ I.f j.val i.val (colIdx y)
      ≤ (∏ i : Fin 7, (∑ y : Col, I.f j.val i.val (colIdx y))
            ^ (∑ y : Col, I.f j.val i.val (colIdx y)))
        * ∏ i : Fin 7, ∏ y : Col, tN C (rowA c.val i.val) (rowB d.val i.val) (colS (colIdx y))
            (colT I.sg (colIdx y)) ^ I.f j.val i.val (colIdx y) := by
    have e1 : ∏ i : Fin 7, ∏ y : Col, I.f j.val i.val (colIdx y) ^ I.f j.val i.val (colIdx y)
        = prod7 fun i => prod9 fun y => I.f j.val i y ^ I.f j.val i y := by
      rw [← prod_fin7 fun i => prod9 fun y => I.f j.val i y ^ I.f j.val i y]
      exact Finset.prod_congr rfl fun i _ =>
        prod_col fun y => I.f j.val i.val y ^ I.f j.val i.val y
    have e2 : ∏ i : Fin 7, (∑ y : Col, I.f j.val i.val (colIdx y))
          ^ (∑ y : Col, I.f j.val i.val (colIdx y))
        = prod7 fun i => sum9 (I.f j.val i) ^ sum9 (I.f j.val i) := by
      rw [← prod_fin7 fun i => sum9 (I.f j.val i) ^ sum9 (I.f j.val i)]
      exact Finset.prod_congr rfl fun i _ => by rw [sum_col (I.f j.val i.val)]
    have e3 : ∏ i : Fin 7, ∏ y : Col, tN C (rowA c.val i.val) (rowB d.val i.val)
          (colS (colIdx y)) (colT I.sg (colIdx y)) ^ I.f j.val i.val (colIdx y)
        = prod7 fun i => prod9 fun y =>
          tN C (rowA c.val i) (rowB d.val i) (colS y) (colT I.sg y) ^ I.f j.val i y := by
      rw [← prod_fin7 fun i => prod9 fun y =>
        tN C (rowA c.val i) (rowB d.val i) (colS y) (colT I.sg y) ^ I.f j.val i y]
      exact Finset.prod_congr rfl fun i _ => prod_col fun y =>
        tN C (rowA c.val i.val) (rowB d.val i.val) (colS y) (colT I.sg y) ^ I.f j.val i.val y
    rw [e1, e2, e3]
    exact hnum
  have key := ball_instance_of_child (wCol_nonneg hw) hA.le
    (fun (i : Fin 7) (y : Col) => tN C (rowA c.val i.val) (rowB d.val i.val) (colS (colIdx y))
      (colT I.sg (colIdx y)))
    (fun (i : Fin 7) (y : Col) => I.f j.val i.val (colIdx y)) hF hF0
    (fun i : Fin 7 => nW j.val i.val) I.D hD hrow hchild α hnum'
  rw [prod_rows j (fun i => genF C.B₁ C.El C.B₂ w (rp c d i).1 (rp c d i).2)
    (fun k => genF C.B₁ C.El C.B₂ w (offPair k).1 (offPair k).2) (genF C.B₁ C.El C.B₂ w c d)
    (fun k => by
      have hk : (k.castSucc : Fin 7).val < 6 := k.isLt
      show genF C.B₁ C.El C.B₂ w (rp c d k.castSucc).1 (rp c d k.castSucc).2 = _
      unfold rp
      rw [dite_eq_left hk]
      rfl)
    (by
      show genF C.B₁ C.El C.B₂ w (rp c d (Fin.last 6)).1 (rp c d (Fin.last 6)).2 = _
      unfold rp
      rw [dite_eq_right (by simp)])] at key
  exact key

/-- The check of a face: one certificate for every donor `j` and every recipient `(c, d)`
outside the pattern of the root edge, at position `9 j + 3 c + d` of the list. -/
def checkCase (α : ℕ) (C : GCase) (L : List Inst) : Bool :=
  all6 fun j => all3 fun c => all3 fun d =>
    bitAt C.er (3 * c + d) || checkInst α C j c d (L.getD (9 * j + 3 * c + d) Inst.zero)

/-- **Soundness of the checker.** -/
theorem checkCase_sound {α : ℕ} {C : GCase} {L : List Inst} (h : checkCase α C L = true) :
    GenOK C.B₁ C.El C.B₂ C.Er α := by
  intro w hw A hA hball j c d hcd
  have h1 := all3_lt (all3_lt (all6_lt h j.isLt) c.isLt) d.isLt
  have h2 : bitAt C.er (3 * c.val + d.val) = false := hcd
  rw [h2, Bool.false_or] at h1
  exact checkInst_sound h1 hw hA hball

end Outerplanar
