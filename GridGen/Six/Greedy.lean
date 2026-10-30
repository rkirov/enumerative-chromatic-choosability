/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Height six: greedy minimality of the interval relaxation

The number of proper colourings of a six-row path from lists `A₁, …, A₆` is, by
inclusion–exclusion over the five consecutive intersections, a polynomial `N6z` in the list sizes
`nᵢ`, the consecutive intersections `eᵢ = |Aᵢ ∩ Aᵢ₊₁|`, the triple ones `tᵢ`, the quadruple ones
`qᵢ`, the fivefold ones `pᵢ` and the sixfold one `x` (`GridGen/Six/Count.lean`). Every real
system satisfies the *interval relaxation*: an interval of length `L ≥ 2` lies between
`max (0, |I(a, b-1)| + |I(a+1, b)| - |I(a+1, b-1)|)` and `min (|I(a, b-1)|, |I(a+1, b)|)`.

**Greedy minimality** (`greedy_min6`): over the relaxation (only the bounds used below), `N6z` is
at least its value `N6g` at the *alternating greedy profile*: triples at their lower bound,
quadruples at their upper bound, fivefold intersections at their lower bound, the sixfold one at
its upper bound. Codex (OpenAI) found the rule and checked it at all 614,383 nonempty relaxations
with sizes in `{5, 6}` (`ai_research_notes/cx/h6k6/NOTE.md`); the independent review
`ai_research_notes/H6_K6_REVIEW_2026-10-29.md` §3 re-enumerated it. The proof here is symbolic:

* `N6z` is affine in `(q, p, x)`, with slope `-1` in `x`, `+n₆` and `+n₁` in `p₁`, `p₂`, and
  `-(n₅n₆ - e₅)`, `-n₁n₆`, `-(n₁n₂ - e₁)` in `q₁, q₂, q₃` (`N6z_split`). Pushing `x` up, then the
  `p`'s down and the `q`'s up to the greedy values given the actual triples costs nothing
  (`step_qpx`): each move of a `q` changes the `p` bounds by at most as much, and the `q` slopes
  dominate.
* With `q, p, x` greedy in the triples, the value `H6` is nondecreasing in each triple
  (`mono_t1` … `mono_t4`): the direct slope of `t₁` is the count of the path of rows `4..6`, which
  dominates the induced moves of `q₁`, `p₁`, `x`, and similarly for the others.
-/

namespace GridGen.Six

/-- The count of a six-row column as a polynomial in its interval profile. -/
def N6z (n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2 t3 t4 q1 q2 q3 p1 p2 x : ℤ) : ℤ :=
  - x + p1 * n6 + q1 * e5 - q1 * n5 * n6 + t1 * t4 - t1 * e4 * n6 - t1 * n4 * e5
    + t1 * n4 * n5 * n6 + e1 * q3 - e1 * t3 * n6 - e1 * e3 * e5 + e1 * e3 * n5 * n6
    - e1 * n3 * t4 + e1 * n3 * e4 * n6 + e1 * n3 * n4 * e5 - e1 * n3 * n4 * n5 * n6 + n1 * p2
    - n1 * q2 * n6 - n1 * t2 * e5 + n1 * t2 * n5 * n6 - n1 * e2 * t4 + n1 * e2 * e4 * n6
    + n1 * e2 * n4 * e5 - n1 * e2 * n4 * n5 * n6 - n1 * n2 * q3 + n1 * n2 * t3 * n6
    + n1 * n2 * e3 * e5 - n1 * n2 * e3 * n5 * n6 + n1 * n2 * n3 * t4 - n1 * n2 * n3 * e4 * n6
    - n1 * n2 * n3 * n4 * e5 + n1 * n2 * n3 * n4 * n5 * n6

/-- The part of `N6z` without `q, p, x`. -/
def B6 (n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2 t3 t4 : ℤ) : ℤ :=
  N6z n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2 t3 t4 0 0 0 0 0 0

theorem N6z_split (n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2 t3 t4 q1 q2 q3 p1 p2 x : ℤ) :
    N6z n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2 t3 t4 q1 q2 q3 p1 p2 x
      = B6 n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2 t3 t4 - (n5 * n6 - e5) * q1 - n1 * n6 * q2
        - (n1 * n2 - e1) * q3 + n6 * p1 + n1 * p2 - x := by
  unfold B6 N6z; ring

/-- The value with `q, p, x` greedy in the triples. -/
def H6 (n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2 t3 t4 : ℤ) : ℤ :=
  N6z n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2 t3 t4 (min t1 t2) (min t2 t3) (min t3 t4)
    (max 0 (min t1 t2 + min t2 t3 - t2)) (max 0 (min t2 t3 + min t3 t4 - t3))
    (min (max 0 (min t1 t2 + min t2 t3 - t2)) (max 0 (min t2 t3 + min t3 t4 - t3)))

/-- **The greedy value**: triples at `max (0, eᵢ + eᵢ₊₁ - nᵢ₊₁)`, the rest greedy in them. -/
def N6g (n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 : ℤ) : ℤ :=
  H6 n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 (max 0 (e1 + e2 - n2)) (max 0 (e2 + e3 - n3))
    (max 0 (e3 + e4 - n4)) (max 0 (e4 + e5 - n5))

/-! ### Elementary moves of minima and maxima -/

theorem min_move {a b a' b' : ℤ} (ha : a ≤ a') (hb : b ≤ b') :
    0 ≤ min a' b' - min a b ∧ min a' b' - min a b ≤ (a' - a) + (b' - b) := by
  constructor
  · have := min_le_min ha hb; linarith
  · rcases le_total a b with h | h <;> rcases le_total a' b' with h' | h' <;>
      simp only [min_eq_left, min_eq_right, h, h'] <;> linarith

theorem min_move1 {a b a' : ℤ} (ha : a ≤ a') :
    0 ≤ min a' b - min a b ∧ min a' b - min a b ≤ a' - a := by
  have := min_move ha (le_refl b); simpa using this

theorem min_move2 {a b b' : ℤ} (hb : b ≤ b') :
    0 ≤ min a b' - min a b ∧ min a b' - min a b ≤ b' - b := by
  have := min_move (le_refl a) hb; simpa using this

/-- `max 0` is monotone and `1`-Lipschitz. -/
theorem max0_move {u u' : ℤ} : min 0 (u' - u) ≤ max 0 u' - max 0 u ∧
    max 0 u' - max 0 u ≤ max 0 (u' - u) := by
  constructor <;> rcases le_total 0 u with h | h <;> rcases le_total 0 u' with h' | h' <;>
    rcases le_total 0 (u' - u) with h'' | h'' <;>
    simp only [max_eq_left, max_eq_right, min_eq_left, min_eq_right, h, h', h''] <;> linarith

theorem min_move_gen {a b a' b' : ℤ} : min (a' - a) (b' - b) ≤ min a' b' - min a b ∧
    min a' b' - min a b ≤ max (a' - a) (b' - b) := by
  constructor <;> rcases le_total a b with h | h <;> rcases le_total a' b' with h' | h' <;>
    rcases le_total (a' - a) (b' - b) with h'' | h'' <;>
    simp only [max_eq_left, max_eq_right, min_eq_left, min_eq_right, h, h', h''] <;> linarith

/-! ### Step 1: `q, p, x` to their greedy values given the triples -/

theorem step_qpx {n1 n2 n5 n6 e1 e5 t1 t2 t3 t4 q1 q2 q3 p1 p2 x : ℤ}
    (hn1 : 2 ≤ n1) (hn2 : 2 ≤ n2) (hn5 : 2 ≤ n5) (hn6 : 2 ≤ n6) (he1 : e1 ≤ n1) (he5 : e5 ≤ n5)
    (hq1 : q1 ≤ t1) (hq1' : q1 ≤ t2) (hq2 : q2 ≤ t2) (hq2' : q2 ≤ t3) (hq3 : q3 ≤ t3)
    (hq3' : q3 ≤ t4) (hp1 : 0 ≤ p1) (hp1' : q1 + q2 - t2 ≤ p1) (hp2 : 0 ≤ p2)
    (hp2' : q2 + q3 - t3 ≤ p2) (hx : x ≤ p1) (hx' : x ≤ p2) (n3 n4 e2 e3 e4 : ℤ) :
    H6 n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2 t3 t4
      ≤ N6z n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2 t3 t4 q1 q2 q3 p1 p2 x := by
  unfold H6
  rw [N6z_split, N6z_split]
  set m1 := min t1 t2 with hm1
  set m2 := min t2 t3 with hm2
  set m3 := min t3 t4 with hm3
  set P1 := max 0 (m1 + m2 - t2) with hP1
  set P2 := max 0 (m2 + m3 - t3) with hP2
  have d1 : q1 ≤ m1 := le_min hq1 hq1'
  have d2 : q2 ≤ m2 := le_min hq2 hq2'
  have d3 : q3 ≤ m3 := le_min hq3 hq3'
  -- the actual `p`'s lie above the bounds of the actual `q`'s
  have g1 : P1 - (m1 - q1) - (m2 - q2) ≤ p1 := by
    rw [hP1]
    rcases le_total 0 (m1 + m2 - t2) with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have g2 : P2 - (m2 - q2) - (m3 - q3) ≤ p2 := by
    rw [hP2]
    rcases le_total 0 (m2 + m3 - t3) with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  -- the sixfold term
  have gx : x ≤ min p1 p2 := le_min hx hx'
  have gm := (min_move_gen (a := P1) (b := P2) (a' := p1) (b' := p2)).2
  -- slopes
  have s1 : 0 ≤ (n5 * n6 - e5 - n6) * (m1 - q1) := by
    apply mul_nonneg _ (by linarith); nlinarith
  have s2 : 0 ≤ (n1 * n6 - n6 - n1) * (m2 - q2) := by
    apply mul_nonneg _ (by linarith); nlinarith
  have s3 : 0 ≤ (n1 * n2 - e1 - n1) * (m3 - q3) := by
    apply mul_nonneg _ (by linarith); nlinarith
  rcases le_total (p1 - P1) (p2 - P2) with h | h
  · rw [max_eq_right h] at gm
    have a1 : n6 * (P1 - (m1 - q1) - (m2 - q2)) ≤ n6 * p1 :=
      mul_le_mul_of_nonneg_left g1 (by linarith)
    have a2 : (n1 - 1) * (P2 - (m2 - q2) - (m3 - q3)) ≤ (n1 - 1) * p2 :=
      mul_le_mul_of_nonneg_left g2 (by linarith)
    nlinarith
  · rw [max_eq_left h] at gm
    have a1 : (n6 - 1) * (P1 - (m1 - q1) - (m2 - q2)) ≤ (n6 - 1) * p1 :=
      mul_le_mul_of_nonneg_left g1 (by linarith)
    have a2 : n1 * (P2 - (m2 - q2) - (m3 - q3)) ≤ n1 * p2 :=
      mul_le_mul_of_nonneg_left g2 (by linarith)
    nlinarith

/-! ### Step 2: the triples to their lower bounds -/

theorem B6_t1 (n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t1' t2 t3 t4 : ℤ) :
    B6 n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1' t2 t3 t4 - B6 n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2 t3 t4
      = (t1' - t1) * (n4 * n5 * n6 - e4 * n6 - n4 * e5 + t4) := by
  unfold B6 N6z; ring

theorem B6_t2 (n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2 t2' t3 t4 : ℤ) :
    B6 n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2' t3 t4 - B6 n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2 t3 t4
      = (t2' - t2) * (n1 * (n5 * n6 - e5)) := by
  unfold B6 N6z; ring

theorem B6_t3 (n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2 t3 t3' t4 : ℤ) :
    B6 n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2 t3' t4 - B6 n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2 t3 t4
      = (t3' - t3) * (n6 * (n1 * n2 - e1)) := by
  unfold B6 N6z; ring

theorem B6_t4 (n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2 t3 t4 t4' : ℤ) :
    B6 n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2 t3 t4' - B6 n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2 t3 t4
      = (t4' - t4) * (n1 * n2 * n3 - e1 * n3 - n1 * e2 + t1) := by
  unfold B6 N6z; ring

section mono

variable {n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 : ℤ}
  (hn1 : 5 ≤ n1) (hn2 : 5 ≤ n2) (hn3 : 5 ≤ n3) (hn4 : 5 ≤ n4) (hn5 : 5 ≤ n5) (hn6 : 5 ≤ n6)
  (he1 : e1 ≤ n1) (he1' : e1 ≤ n2) (he2 : e2 ≤ n2) (he4 : e4 ≤ n5) (he5 : e5 ≤ n5)
  (he5' : e5 ≤ n6)
include hn1 hn2 hn3 hn4 hn5 hn6 he1 he1' he2 he4 he5 he5'

theorem mono_t1 {t1 t1' t2 t3 t4 : ℤ} (h : t1 ≤ t1') (ht4 : 0 ≤ t4) :
    H6 n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2 t3 t4
      ≤ H6 n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1' t2 t3 t4 := by
  unfold H6
  rw [N6z_split, N6z_split]
  have hB := B6_t1 n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t1' t2 t3 t4
  have hm := min_move1 (b := t2) h
  set m := min t1 t2
  set m' := min t1' t2
  set m2 := min t2 t3
  set m3 := min t3 t4
  set P2 := max 0 (m2 + m3 - t3)
  have hP := max0_move (u := m + m2 - t2) (u' := m' + m2 - t2)
  rw [show m' + m2 - t2 - (m + m2 - t2) = m' - m by ring, min_eq_left hm.1,
    max_eq_right hm.1] at hP
  set P := max 0 (m + m2 - t2)
  set P' := max 0 (m' + m2 - t2)
  have hX := min_move1 (b := P2) (show P ≤ P' by linarith)
  have k1 : 0 ≤ (n4 * n5 * n6 - e4 * n6 - n4 * e5 + t4 - (n5 * n6 - e5)) * (t1' - t1) := by
    apply mul_nonneg _ (by linarith)
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ n4 - 5 by linarith) (show (0 : ℤ) ≤ n6 - 5 by linarith),
      mul_nonneg (show (0 : ℤ) ≤ n5 - e4 by linarith) (show (0 : ℤ) ≤ n6 by linarith),
      mul_nonneg (show (0 : ℤ) ≤ n5 - e5 by linarith) (show (0 : ℤ) ≤ n4 - 1 by linarith),
      mul_nonneg (show (0 : ℤ) ≤ n5 by linarith)
        (mul_nonneg (show (0 : ℤ) ≤ n4 - 5 by linarith) (show (0 : ℤ) ≤ n6 - 5 by linarith))]
  have k2 : (n5 * n6 - e5) * (m' - m) ≤ (n5 * n6 - e5) * (t1' - t1) :=
    mul_le_mul_of_nonneg_left hm.2 (by nlinarith)
  have k3 : 0 ≤ (n6 - 1) * (P' - P) := mul_nonneg (by linarith) (by linarith)
  nlinarith

theorem mono_t4 {t1 t2 t3 t4 t4' : ℤ} (h : t4 ≤ t4') (ht1 : 0 ≤ t1) :
    H6 n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2 t3 t4
      ≤ H6 n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2 t3 t4' := by
  unfold H6
  rw [N6z_split, N6z_split]
  have hB := B6_t4 n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2 t3 t4 t4'
  have hm := min_move2 (a := t3) h
  set m := min t3 t4
  set m' := min t3 t4'
  set m1 := min t1 t2
  set m2 := min t2 t3
  set P1 := max 0 (m1 + m2 - t2)
  have hP := max0_move (u := m2 + m - t3) (u' := m2 + m' - t3)
  rw [show m2 + m' - t3 - (m2 + m - t3) = m' - m by ring, min_eq_left hm.1,
    max_eq_right hm.1] at hP
  set P := max 0 (m2 + m - t3)
  set P' := max 0 (m2 + m' - t3)
  have hX := min_move2 (a := P1) (show P ≤ P' by linarith)
  have k1 : 0 ≤ (n1 * n2 * n3 - e1 * n3 - n1 * e2 + t1 - (n1 * n2 - e1)) * (t4' - t4) := by
    apply mul_nonneg _ (by linarith)
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ n1 - 5 by linarith) (show (0 : ℤ) ≤ n3 - 5 by linarith),
      mul_nonneg (show (0 : ℤ) ≤ n2 - e1 by linarith) (show (0 : ℤ) ≤ n3 - 1 by linarith),
      mul_nonneg (show (0 : ℤ) ≤ n2 - e2 by linarith) (show (0 : ℤ) ≤ n1 by linarith),
      mul_nonneg (show (0 : ℤ) ≤ n2 by linarith)
        (mul_nonneg (show (0 : ℤ) ≤ n1 - 5 by linarith) (show (0 : ℤ) ≤ n3 - 5 by linarith))]
  have k2 : (n1 * n2 - e1) * (m' - m) ≤ (n1 * n2 - e1) * (t4' - t4) :=
    mul_le_mul_of_nonneg_left hm.2 (by nlinarith)
  have k3 : 0 ≤ (n1 - 1) * (P' - P) := mul_nonneg (by linarith) (by linarith)
  nlinarith

theorem mono_t2 {t1 t2 t2' t3 t4 : ℤ} (h : t2 ≤ t2') :
    H6 n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2 t3 t4
      ≤ H6 n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2' t3 t4 := by
  unfold H6
  rw [N6z_split, N6z_split]
  have hB := B6_t2 n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2 t2' t3 t4
  have h1 := min_move2 (a := t1) h
  have h2 := min_move1 (b := t3) h
  set a := min t1 t2
  set a' := min t1 t2'
  set b := min t2 t3
  set b' := min t2' t3
  set c := min t3 t4
  have hP1 := max0_move (u := a + b - t2) (u' := a' + b' - t2')
  have hP2 := max0_move (u := b + c - t3) (u' := b' + c - t3)
  rw [show b' + c - t3 - (b + c - t3) = b' - b by ring, min_eq_left h2.1,
    max_eq_right h2.1] at hP2
  have l1 : min 0 (a' + b' - t2' - (a + b - t2)) ≥ -(t2' - t2) := le_min (by linarith) (by linarith)
  have l2 : max 0 (a' + b' - t2' - (a + b - t2)) ≤ t2' - t2 := max_le (by linarith) (by linarith)
  set P := max 0 (a + b - t2)
  set P' := max 0 (a' + b' - t2')
  set Q := max 0 (b + c - t3)
  set Q' := max 0 (b' + c - t3)
  have hX := (min_move_gen (a := P) (b := Q) (a' := P') (b' := Q')).2
  have hX' : max (P' - P) (Q' - Q) ≤ t2' - t2 := max_le (by linarith) (by linarith)
  have k1 : 0 ≤ (n1 * (n5 * n6 - e5) - (n5 * n6 - e5) - n1 * n6 - n6 - 1) * (t2' - t2) := by
    apply mul_nonneg _ (by linarith)
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ n1 - 5 by linarith) (show (0 : ℤ) ≤ n6 - 5 by linarith),
      mul_nonneg (show (0 : ℤ) ≤ n5 - e5 by linarith) (show (0 : ℤ) ≤ n1 - 1 by linarith),
      mul_nonneg (show (0 : ℤ) ≤ n5 - 5 by linarith) (show (0 : ℤ) ≤ n6 - 5 by linarith),
      mul_nonneg (show (0 : ℤ) ≤ n1 - 5 by linarith)
        (mul_nonneg (show (0 : ℤ) ≤ n5 - 5 by linarith) (show (0 : ℤ) ≤ n6 - 5 by linarith)),
      mul_nonneg (show (0 : ℤ) ≤ n1 - 5 by linarith) (show (0 : ℤ) ≤ n5 - 5 by linarith)]
  have k2 : (n5 * n6 - e5) * (a' - a) ≤ (n5 * n6 - e5) * (t2' - t2) :=
    mul_le_mul_of_nonneg_left h1.2 (by nlinarith)
  have k3 : n1 * n6 * (b' - b) ≤ n1 * n6 * (t2' - t2) :=
    mul_le_mul_of_nonneg_left h2.2 (by nlinarith)
  have k4 : n6 * (-(t2' - t2)) ≤ n6 * (P' - P) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have k5 : 0 ≤ n1 * (Q' - Q) := mul_nonneg (by linarith) (by linarith)
  have k6 : (n5 * n6 - e5) * (t2' - t2) - (n5 * n6 - e5) * (a' - a) ≥ 0 := by linarith
  nlinarith

theorem mono_t3 {t1 t2 t3 t3' t4 : ℤ} (h : t3 ≤ t3') :
    H6 n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2 t3 t4
      ≤ H6 n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2 t3' t4 := by
  unfold H6
  rw [N6z_split, N6z_split]
  have hB := B6_t3 n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2 t3 t3' t4
  have h1 := min_move2 (a := t2) h
  have h2 := min_move1 (b := t4) h
  set a := min t1 t2
  set b := min t2 t3
  set b' := min t2 t3'
  set c := min t3 t4
  set c' := min t3' t4
  have hP1 := max0_move (u := a + b - t2) (u' := a + b' - t2)
  have hP2 := max0_move (u := b + c - t3) (u' := b' + c' - t3')
  rw [show a + b' - t2 - (a + b - t2) = b' - b by ring, min_eq_left h1.1,
    max_eq_right h1.1] at hP1
  have l1 : min 0 (b' + c' - t3' - (b + c - t3)) ≥ -(t3' - t3) := le_min (by linarith) (by linarith)
  have l2 : max 0 (b' + c' - t3' - (b + c - t3)) ≤ t3' - t3 := max_le (by linarith) (by linarith)
  set P := max 0 (a + b - t2)
  set P' := max 0 (a + b' - t2)
  set Q := max 0 (b + c - t3)
  set Q' := max 0 (b' + c' - t3')
  have hX := (min_move_gen (a := P) (b := Q) (a' := P') (b' := Q')).2
  have hX' : max (P' - P) (Q' - Q) ≤ t3' - t3 := max_le (by linarith) (by linarith)
  have k1 : 0 ≤ (n6 * (n1 * n2 - e1) - (n1 * n2 - e1) - n1 * n6 - n1 - 1) * (t3' - t3) := by
    apply mul_nonneg _ (by linarith)
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ n1 - 5 by linarith) (show (0 : ℤ) ≤ n6 - 5 by linarith),
      mul_nonneg (show (0 : ℤ) ≤ n2 - e1 by linarith) (show (0 : ℤ) ≤ n6 - 1 by linarith),
      mul_nonneg (show (0 : ℤ) ≤ n1 - 5 by linarith) (show (0 : ℤ) ≤ n2 - 5 by linarith),
      mul_nonneg (show (0 : ℤ) ≤ n6 - 5 by linarith)
        (mul_nonneg (show (0 : ℤ) ≤ n1 - 5 by linarith) (show (0 : ℤ) ≤ n2 - 5 by linarith)),
      mul_nonneg (show (0 : ℤ) ≤ n6 - 5 by linarith) (show (0 : ℤ) ≤ n2 - 5 by linarith)]
  have k2 : (n1 * n2 - e1) * (c' - c) ≤ (n1 * n2 - e1) * (t3' - t3) :=
    mul_le_mul_of_nonneg_left h2.2 (by nlinarith)
  have k3 : n1 * n6 * (b' - b) ≤ n1 * n6 * (t3' - t3) :=
    mul_le_mul_of_nonneg_left h1.2 (by nlinarith)
  have k4 : n1 * (-(t3' - t3)) ≤ n1 * (Q' - Q) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have k5 : 0 ≤ n6 * (P' - P) := mul_nonneg (by linarith) (by linarith)
  nlinarith

end mono

/-- **Greedy minimality** at height six. -/
theorem greedy_min6 {n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2 t3 t4 q1 q2 q3 p1 p2 x : ℤ}
    (hn1 : 5 ≤ n1) (hn2 : 5 ≤ n2) (hn3 : 5 ≤ n3) (hn4 : 5 ≤ n4) (hn5 : 5 ≤ n5) (hn6 : 5 ≤ n6)
    (he1 : e1 ≤ n1) (he1' : e1 ≤ n2) (he2 : e2 ≤ n2) (he4 : e4 ≤ n5) (he5 : e5 ≤ n5)
    (he5' : e5 ≤ n6)
    (ht1 : 0 ≤ t1) (ht1' : e1 + e2 - n2 ≤ t1) (ht2 : 0 ≤ t2) (ht2' : e2 + e3 - n3 ≤ t2)
    (ht3 : 0 ≤ t3) (ht3' : e3 + e4 - n4 ≤ t3) (ht4 : 0 ≤ t4) (ht4' : e4 + e5 - n5 ≤ t4)
    (hq1 : q1 ≤ t1) (hq1' : q1 ≤ t2) (hq2 : q2 ≤ t2) (hq2' : q2 ≤ t3) (hq3 : q3 ≤ t3)
    (hq3' : q3 ≤ t4) (hp1 : 0 ≤ p1) (hp1' : q1 + q2 - t2 ≤ p1) (hp2 : 0 ≤ p2)
    (hp2' : q2 + q3 - t3 ≤ p2) (hx : x ≤ p1) (hx' : x ≤ p2) :
    N6g n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5
      ≤ N6z n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2 t3 t4 q1 q2 q3 p1 p2 x := by
  have s0 := step_qpx (n1 := n1) (n2 := n2) (n5 := n5) (n6 := n6) (by linarith) (by linarith) (by linarith) (by linarith) he1 he5 hq1 hq1'
    hq2 hq2' hq3 hq3' hp1 hp1' hp2 hp2' hx hx' n3 n4 e2 e3 e4
  have T1 : max 0 (e1 + e2 - n2) ≤ t1 := max_le ht1 ht1'
  have T2 : max 0 (e2 + e3 - n3) ≤ t2 := max_le ht2 ht2'
  have T3 : max 0 (e3 + e4 - n4) ≤ t3 := max_le ht3 ht3'
  have T4 : max 0 (e4 + e5 - n5) ≤ t4 := max_le ht4 ht4'
  have s1 := mono_t1 hn1 hn2 hn3 hn4 hn5 hn6 (e3 := e3) he1 he1' he2 he4 he5 he5' (t2 := t2) (t3 := t3) T1 ht4
  have s2 := mono_t2 hn1 hn2 hn3 hn4 hn5 hn6 (e3 := e3) he1 he1' he2 he4 he5 he5' (t1 := max 0 (e1 + e2 - n2))
    (t3 := t3) (t4 := t4) T2
  have s3 := mono_t3 hn1 hn2 hn3 hn4 hn5 hn6 (e3 := e3) he1 he1' he2 he4 he5 he5' (t1 := max 0 (e1 + e2 - n2))
    (t2 := max 0 (e2 + e3 - n3)) (t4 := t4) T3
  have s4 := mono_t4 hn1 hn2 hn3 hn4 hn5 hn6 (e3 := e3) he1 he1' he2 he4 he5 he5' (t1 := max 0 (e1 + e2 - n2))
    (t2 := max 0 (e2 + e3 - n3)) (t3 := max 0 (e3 + e4 - n4)) T4 (le_max_left _ _)
  unfold N6g
  linarith

end GridGen.Six
