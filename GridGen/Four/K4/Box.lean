/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.K4.Leaf

/-!
# Height four at `k = 4`: the box bound

A set of column types whose successor lists have fixed sizes `n₁, …, n₄` (each `3` or `4`) and
whose eleven larger intersection sizes lie in intervals `[lo_J, hi_J]` is bounded below at once.
At a weight `w`, `⟪cls D, w⟫` is a polynomial in the intersection sizes whose only products are
`e₁₂e₃₄`, `a₁₃a₂₄` and `a₁₄e₂₃` (`dot_cls_poly`): with `α = w_A - 2w_B + w_D`, `β = w_B - w_D`,
`γ = w_C - w_D`, `δ = w_D`,

  `⟪cls D, w⟫ = δ n₁n₂n₃n₄ + (−δn₃n₄ e₁₂ − δn₁n₂ e₃₄ + δ e₁₂e₃₄) + (βn₂n₄ a₁₃ + βn₁n₃ a₂₄ + α a₁₃a₂₄)
      + (γn₂n₃ a₁₄ − δn₁n₄ e₂₃ − γ a₁₄e₂₃) + n₄(δ−β) t₁₂₃ + n₁(δ−β) t₂₃₄ − n₃(β+γ) a₁₂₄
      − n₂(β+γ) a₁₃₄ + (−α+2β+2γ−δ) q`.

Its minimum over the box separates: a linear term is smallest at an end of its interval
(`smin_le`), a bilinear term `c_u u + c_v v + d uv` at a corner of its rectangle (`pmin_le`).
`rayZ` computes this minimum minus `⟪hrow, w⟫`; `boxV` takes it at the four rays `F₀, …, F₃`
and, for the tail valuation, at the centre `2c* = (20000, 18907, 17186, 17816)` of the doubled tail
box minus `1280`: a seam vector has `|d₂|, |d₃|, |d₄| ≤ 256`, and the corners differ from `2c*` by
`(0, ±1, ±2, ±2)` (`boxV_sound`). Codex's (OpenAI) classification
(`ai_research_notes/cx/h4k4b/NOTE.md`) is certified with these boxes as in the review's design
(`ai_research_notes/H4_K4_REVIEW_2026-10-26.md`, `H4_K4_CERT_LEVERS_2026-10-26.md`).
-/

namespace GridGen.Four.K4

open Finset GridGen.Four

/-! ### Separable minima -/

theorem smin_le (c lo hi x : ℤ) (h1 : lo ≤ x) (h2 : x ≤ hi) : min (c * lo) (c * hi) ≤ c * x := by
  rcases le_total 0 c with hc | hc
  · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left h1 hc)
  · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left h2 hc)

theorem aff_le (a b u0 u1 u : ℤ) (h1 : u0 ≤ u) (h2 : u ≤ u1) :
    min (a + b * u0) (a + b * u1) ≤ a + b * u := by
  have := smin_le b u0 u1 u h1 h2
  rw [min_add_add_left]
  linarith

theorem pmin_le (cu cv d u0 u1 v0 v1 u v : ℤ) (hu1 : u0 ≤ u) (hu2 : u ≤ u1) (hv1 : v0 ≤ v)
    (hv2 : v ≤ v1) :
    min (min (cu * u0 + cv * v0 + d * u0 * v0) (cu * u1 + cv * v0 + d * u1 * v0))
        (min (cu * u0 + cv * v1 + d * u0 * v1) (cu * u1 + cv * v1 + d * u1 * v1))
      ≤ cu * u + cv * v + d * u * v := by
  -- in `u` at fixed `v`
  have hU := aff_le (cv * v) (cu + d * v) u0 u1 u hu1 hu2
  -- in `v` at `u = u0` and `u = u1`
  have hV0 := aff_le (cu * u0) (cv + d * u0) v0 v1 v hv1 hv2
  have hV1 := aff_le (cu * u1) (cv + d * u1) v0 v1 v hv1 hv2
  have e : cu * u + cv * v + d * u * v = cv * v + (cu + d * v) * u := by ring
  have e0 : cv * v + (cu + d * v) * u0 = cu * u0 + (cv + d * u0) * v := by ring
  have e1 : cv * v + (cu + d * v) * u1 = cu * u1 + (cv + d * u1) * v := by ring
  have c00 : cu * u0 + (cv + d * u0) * v0 = cu * u0 + cv * v0 + d * u0 * v0 := by ring
  have c01 : cu * u0 + (cv + d * u0) * v1 = cu * u0 + cv * v1 + d * u0 * v1 := by ring
  have c10 : cu * u1 + (cv + d * u1) * v0 = cu * u1 + cv * v0 + d * u1 * v0 := by ring
  have c11 : cu * u1 + (cv + d * u1) * v1 = cu * u1 + cv * v1 + d * u1 * v1 := by ring
  rw [e]
  rw [e0, e1] at hU
  rw [c00, c01] at hV0
  rw [c10, c11] at hV1
  refine le_trans ?_ hU
  apply le_min
  · exact le_trans (min_le_min (min_le_left _ _) (min_le_left _ _)) hV0
  · exact le_trans (min_le_min (min_le_right _ _) (min_le_right _ _)) hV1

/-! ### The polynomial -/

/-- **`⟪cls D, w⟫` as a polynomial** with three bilinear products. -/
theorem dot_cls_poly (D : Dat) (w : Q) :
    dot (cls D) w =
      w.2.2.2 * D.n1 * D.n2 * D.n3 * D.n4
      + ((-(w.2.2.2 * D.n3 * D.n4)) * D.e12 + (-(w.2.2.2 * D.n1 * D.n2)) * D.e34
          + w.2.2.2 * D.e12 * D.e34)
      + (((w.2.1 - w.2.2.2) * D.n2 * D.n4) * D.a13 + ((w.2.1 - w.2.2.2) * D.n1 * D.n3) * D.a24
          + (w.1 - 2 * w.2.1 + w.2.2.2) * D.a13 * D.a24)
      + (((w.2.2.1 - w.2.2.2) * D.n2 * D.n3) * D.a14 + (-(w.2.2.2 * D.n1 * D.n4)) * D.e23
          + (-(w.2.2.1 - w.2.2.2)) * D.a14 * D.e23)
      + (D.n4 * (w.2.2.2 - (w.2.1 - w.2.2.2))) * D.t123
      + (D.n1 * (w.2.2.2 - (w.2.1 - w.2.2.2))) * D.t234
      + (-(D.n3 * ((w.2.1 - w.2.2.2) + (w.2.2.1 - w.2.2.2)))) * D.a124
      + (-(D.n2 * ((w.2.1 - w.2.2.2) + (w.2.2.1 - w.2.2.2)))) * D.a134
      + (-(w.1 - 2 * w.2.1 + w.2.2.2) + 2 * (w.2.1 - w.2.2.2) + 2 * (w.2.2.1 - w.2.2.2)
          - w.2.2.2) * D.q := by
  obtain ⟨w0, w1, w2, w3⟩ := w
  simp only [cls, dot]
  ring

/-! ### The box minimum in `Nat`-pair arithmetic -/

/-- Intervals for the eleven larger intersections. -/
structure X11 where
  (e12 e23 e34 a13 a24 a14 t123 t234 a124 a134 q : ℕ)

/-- `d u v - (a u + b v)` at a corner, as a pair. -/
def cornN (a b d u v : ℕ) : Zp := ⟨Nat.mul d (Nat.mul u v), Nat.add (Nat.mul a u) (Nat.mul b v)⟩

/-- **Minimum over the corners of a rectangle** of `d u v - a u - b v` (`a, b, d ≥ 0`). -/
def pminN (a b d u0 u1 v0 v1 : ℕ) : Zp :=
  Zp.min (Zp.min (cornN a b d u0 v0) (cornN a b d u1 v0))
    (Zp.min (cornN a b d u0 v1) (cornN a b d u1 v1))

/-- **The box minimum at one weight**, minus `hw = ⟪hrow, w⟫` and `extra`, for a weight with
`α = al`, `β = be`, `γ = -gm`, `δ = de` (all four nonnegative, `gm ≤ be ≤ de`). The signs fix where
each separable term is smallest: the linear terms with nonnegative coefficient (`t₁₂₃, t₂₃₄`) and
the product `βn₂n₄ a₁₃ + βn₁n₃ a₂₄ + α a₁₃a₂₄` at the lower ends, the other linear terms at the upper
ends; only the two products with negative linear coefficients need all four corners. The value
is a single pair of naturals (positive part, negative part), which keeps the kernel's work to a
few dozen `Nat` operations. -/
def rayZ (n1 n2 n3 n4 al be gm de hw extra : ℕ) (lo hi : X11) : Zp :=
  let p1 := pminN (Nat.mul (Nat.mul n3 n4) de) (Nat.mul (Nat.mul n1 n2) de) de
    lo.e12 hi.e12 lo.e34 hi.e34
  let p3 := pminN (Nat.mul (Nat.mul n2 n3) gm) (Nat.mul (Nat.mul n1 n4) de) gm
    lo.a14 hi.a14 lo.e23 hi.e23
  let bg := Nat.sub be gm
  let db := Nat.sub de be
  ⟨Nat.add (Nat.add (Nat.mul (Nat.mul (Nat.mul n1 n2) (Nat.mul n3 n4)) de) (Nat.add p1.p p3.p))
      (Nat.add (Nat.add (Nat.mul (Nat.mul (Nat.mul n2 n4) be) lo.a13)
          (Nat.add (Nat.mul (Nat.mul (Nat.mul n1 n3) be) lo.a24) (Nat.mul (Nat.mul al lo.a13) lo.a24)))
        (Nat.add (Nat.mul (Nat.mul n4 db) lo.t123) (Nat.mul (Nat.mul n1 db) lo.t234))),
    Nat.add (Nat.add (Nat.add hw extra) (Nat.add p1.n p3.n))
      (Nat.add (Nat.add (Nat.mul (Nat.mul n3 bg) hi.a124) (Nat.mul (Nat.mul n2 bg) hi.a134))
        (Nat.mul (Nat.sub (Nat.add al de) (Nat.add bg bg)) hi.q))⟩

/-- `⟪h, w⟫` for naturals. -/
def dotNN (h : ℕ × ℕ × ℕ × ℕ) (w0 w1 w2 w3 : ℕ) : ℕ :=
  Nat.add (Nat.add (Nat.mul h.1 w0) (Nat.mul h.2.1 w1)) (Nat.add (Nat.mul h.2.2.1 w2) (Nat.mul h.2.2.2 w3))

/-- **The five box valuations**, for the class with transfer row `h`. -/
def boxV (n1 n2 n3 n4 : ℕ) (h : ℕ × ℕ × ℕ × ℕ) (lo hi : X11) : V5 :=
  ⟨rayZ n1 n2 n3 n4 0 0 0 1 (dotNN h 1 1 1 1) 0 lo hi,
    rayZ n1 n2 n3 n4 0 2 1 37 (dotNN h 41 39 36 37) 0 lo hi,
    rayZ n1 n2 n3 n4 0 85 48 1409 (dotNN h 1579 1494 1361 1409) 0 lo hi,
    rayZ n1 n2 n3 n4 0 3291 1893 53789 (dotNN h 60371 57080 51896 53789) 0 lo hi,
    rayZ n1 n2 n3 n4 2 1091 630 17816 (dotNN h 20000 18907 17186 17816) 1280 lo hi⟩
/-! ### Soundness -/

/-- A data vector in the box. -/
def InBox (n1 n2 n3 n4 : ℕ) (lo hi : X11) (D : Dat) : Prop :=
  D.n1 = n1 ∧ D.n2 = n2 ∧ D.n3 = n3 ∧ D.n4 = n4 ∧
  (lo.e12 : ℤ) ≤ D.e12 ∧ D.e12 ≤ hi.e12 ∧ (lo.e23 : ℤ) ≤ D.e23 ∧ D.e23 ≤ hi.e23 ∧
  (lo.e34 : ℤ) ≤ D.e34 ∧ D.e34 ≤ hi.e34 ∧ (lo.a13 : ℤ) ≤ D.a13 ∧ D.a13 ≤ hi.a13 ∧
  (lo.a24 : ℤ) ≤ D.a24 ∧ D.a24 ≤ hi.a24 ∧ (lo.a14 : ℤ) ≤ D.a14 ∧ D.a14 ≤ hi.a14 ∧
  (lo.t123 : ℤ) ≤ D.t123 ∧ D.t123 ≤ hi.t123 ∧ (lo.t234 : ℤ) ≤ D.t234 ∧ D.t234 ≤ hi.t234 ∧
  (lo.a124 : ℤ) ≤ D.a124 ∧ D.a124 ≤ hi.a124 ∧ (lo.a134 : ℤ) ≤ D.a134 ∧ D.a134 ≤ hi.a134 ∧
  (lo.q : ℤ) ≤ D.q ∧ D.q ≤ hi.q

theorem pminN_le (a b d u0 u1 v0 v1 : ℕ) (u v : ℤ) (hu1 : (u0 : ℤ) ≤ u) (hu2 : u ≤ u1)
    (hv1 : (v0 : ℤ) ≤ v) (hv2 : v ≤ v1) :
    ((pminN a b d u0 u1 v0 v1).p : ℤ) - (pminN a b d u0 u1 v0 v1).n
      ≤ (-(a : ℤ)) * u + (-(b : ℤ)) * v + (d : ℤ) * u * v := by
  have key := pmin_le (-(a : ℤ)) (-(b : ℤ)) d u0 u1 v0 v1 u v hu1 hu2 hv1 hv2
  have hc : ∀ x y : ℕ, (cornN a b d x y).val = (-(a : ℤ)) * x + (-(b : ℤ)) * y + d * x * y := by
    intro x y
    simp only [cornN, Zp.val_mk, Nat.mul_eq, Nat.add_eq]
    push_cast; ring
  show (pminN a b d u0 u1 v0 v1).val ≤ _
  simp only [pminN, Zp.val_min, hc]
  exact key

/-- The box minimum bounds the polynomial on the box, at a weight with the given `α, β, γ, δ`. -/
theorem rayZ_le (n1 n2 n3 n4 al be gm de hw extra : ℕ) (lo hi : X11) (D : Dat)
    (hD : InBox n1 n2 n3 n4 lo hi D) (w : Q) (hal : (al : ℤ) = w.1 - 2 * w.2.1 + w.2.2.2)
    (hbe : (be : ℤ) = w.2.1 - w.2.2.2) (hga : (gm : ℤ) = -(w.2.2.1 - w.2.2.2))
    (hde : (de : ℤ) = w.2.2.2) (hgb : gm ≤ be) (hbd : be ≤ de) (hq : (be - gm) + (be - gm) ≤ al + de) :
    (rayZ n1 n2 n3 n4 al be gm de hw extra lo hi).val ≤ dot (cls D) w - hw - extra := by
  obtain ⟨hn1, hn2, hn3, hn4, l1, u1, l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8, l9, u9,
    l10, u10, l11, u11⟩ := hD
  have p1 := pminN_le (Nat.mul (Nat.mul n3 n4) de) (Nat.mul (Nat.mul n1 n2) de) de
    lo.e12 hi.e12 lo.e34 hi.e34 D.e12 D.e34 l1 u1 l3 u3
  have p3 := pminN_le (Nat.mul (Nat.mul n2 n3) gm) (Nat.mul (Nat.mul n1 n4) de) gm
    lo.a14 hi.a14 lo.e23 hi.e23 D.a14 D.e23 l6 u6 l2 u2
  -- the product term at the lower corner
  have z4 : (0 : ℤ) ≤ lo.a13 := Nat.cast_nonneg _
  have z5 : (0 : ℤ) ≤ lo.a24 := Nat.cast_nonneg _
  have m45 : (lo.a13 : ℤ) * lo.a24 ≤ D.a13 * D.a24 := mul_le_mul l4 l5 z5 (z4.trans l4)
  have q1 : ((n2 * n4 * be : ℕ) : ℤ) * lo.a13 ≤ ((n2 * n4 * be : ℕ) : ℤ) * D.a13 :=
    mul_le_mul_of_nonneg_left l4 (Nat.cast_nonneg _)
  have q2 : ((n1 * n3 * be : ℕ) : ℤ) * lo.a24 ≤ ((n1 * n3 * be : ℕ) : ℤ) * D.a24 :=
    mul_le_mul_of_nonneg_left l5 (Nat.cast_nonneg _)
  have q3 : (al : ℤ) * (lo.a13 * lo.a24) ≤ (al : ℤ) * (D.a13 * D.a24) :=
    mul_le_mul_of_nonneg_left m45 (Nat.cast_nonneg _)
  -- the linear terms
  have s1 : ((n4 * (de - be) : ℕ) : ℤ) * lo.t123 ≤ ((n4 * (de - be) : ℕ) : ℤ) * D.t123 :=
    mul_le_mul_of_nonneg_left l7 (Nat.cast_nonneg _)
  have s2 : ((n1 * (de - be) : ℕ) : ℤ) * lo.t234 ≤ ((n1 * (de - be) : ℕ) : ℤ) * D.t234 :=
    mul_le_mul_of_nonneg_left l8 (Nat.cast_nonneg _)
  have s3 : ((n3 * (be - gm) : ℕ) : ℤ) * D.a124 ≤ ((n3 * (be - gm) : ℕ) : ℤ) * hi.a124 :=
    mul_le_mul_of_nonneg_left u9 (Nat.cast_nonneg _)
  have s4 : ((n2 * (be - gm) : ℕ) : ℤ) * D.a134 ≤ ((n2 * (be - gm) : ℕ) : ℤ) * hi.a134 :=
    mul_le_mul_of_nonneg_left u10 (Nat.cast_nonneg _)
  have s5 : ((al + de - ((be - gm) + (be - gm)) : ℕ) : ℤ) * D.q
      ≤ ((al + de - ((be - gm) + (be - gm)) : ℕ) : ℤ) * hi.q :=
    mul_le_mul_of_nonneg_left u11 (Nat.cast_nonneg _)
  obtain ⟨w0, w1, w2, w3⟩ := w
  simp only at hal hbe hga hde
  have e3 : w3 = de := hde.symm
  have e1 : w1 = be + de := by linarith
  have e2 : w2 = de - gm := by linarith
  have e0 : w0 = al + 2 * be + de := by linarith
  rw [dot_cls_poly, hn1, hn2, hn3, hn4]
  simp only [e0, e1, e2, e3]
  have hv : (rayZ n1 n2 n3 n4 al be gm de hw extra lo hi).val
      = ((n1 * n2 * (n3 * n4) * de : ℕ) : ℤ) + (((pminN (n3 * n4 * de) (n1 * n2 * de) de
          lo.e12 hi.e12 lo.e34 hi.e34).p : ℤ) - (pminN (n3 * n4 * de) (n1 * n2 * de) de
          lo.e12 hi.e12 lo.e34 hi.e34).n)
        + (((pminN (n2 * n3 * gm) (n1 * n4 * de) gm lo.a14 hi.a14 lo.e23 hi.e23).p : ℤ)
          - (pminN (n2 * n3 * gm) (n1 * n4 * de) gm lo.a14 hi.a14 lo.e23 hi.e23).n)
        + ((n2 * n4 * be : ℕ) : ℤ) * lo.a13 + ((n1 * n3 * be : ℕ) : ℤ) * lo.a24
        + (al : ℤ) * (lo.a13 * lo.a24)
        + ((n4 * (de - be) : ℕ) : ℤ) * lo.t123 + ((n1 * (de - be) : ℕ) : ℤ) * lo.t234
        - hw - extra
        - ((n3 * (be - gm) : ℕ) : ℤ) * hi.a124 - ((n2 * (be - gm) : ℕ) : ℤ) * hi.a134
        - ((al + de - ((be - gm) + (be - gm)) : ℕ) : ℤ) * hi.q := by
    simp only [rayZ, Zp.val_mk, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
    push_cast
    ring
  rw [hv]
  simp only [Nat.mul_eq] at p1 p3
  push_cast [Nat.cast_sub hgb, Nat.cast_sub hbd, Nat.cast_sub hq] at p1 p3 q1 q2 q3 s1 s2 s3 s4 s5 ⊢
  linear_combination p1 + p3 + q1 + q2 + q3 + s1 + s2 + s3 + s4 + s5

/-- A transfer row as a class vector. -/
def hQ (h : ℕ × ℕ × ℕ × ℕ) : Q := ((h.1 : ℤ), (h.2.1 : ℤ), (h.2.2.1 : ℤ), (h.2.2.2 : ℤ))

theorem dotNN_eq (h : ℕ × ℕ × ℕ × ℕ) (w0 w1 w2 w3 : ℕ) :
    ((dotNN h w0 w1 w2 w3 : ℕ) : ℤ) = dot (hQ h) (w0, w1, w2, w3) := by
  simp only [dotNN, hQ, dot, Nat.add_eq, Nat.mul_eq]; push_cast; ring

/-- **Soundness of a box**: for a data vector in the box whose seam vector has its last three
entries at most `256` in absolute value, the box valuations bound the families. -/
theorem boxV_sound (n1 n2 n3 n4 : ℕ) (h : ℕ × ℕ × ℕ × ℕ) (lo hi : X11) (D : Dat)
    (hD : InBox n1 n2 n3 n4 lo hi D)
    (hb : |(cls D - hQ h).2.1| ≤ 256 ∧ |(cls D - hQ h).2.2.1| ≤ 256 ∧ |(cls D - hQ h).2.2.2| ≤ 256)
    (k : Fin 5) (w : Q) (hw : w ∈ famW k) :
    ((boxV n1 n2 n3 n4 h lo hi).get k).val ≤ dot (cls D - hQ h) w := by
  have hsub : ∀ v : Q, dot (cls D - hQ h) v = dot (cls D) v - dot (hQ h) v := fun v => dot_sub _ _ _
  fin_cases k <;> simp only [famW, List.mem_cons, List.mem_nil_iff, or_false] at hw
  · subst hw
    have := rayZ_le n1 n2 n3 n4 0 0 0 1 (dotNN h 1 1 1 1) 0 lo hi D hD (1, 1, 1, 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
    rw [dotNN_eq] at this
    simpa [boxV, V5.get, hsub] using this
  · subst hw
    have := rayZ_le n1 n2 n3 n4 0 2 1 37 (dotNN h 41 39 36 37) 0 lo hi D hD (41, 39, 36, 37)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
    rw [dotNN_eq] at this
    simpa [boxV, V5.get, hsub] using this
  · subst hw
    have := rayZ_le n1 n2 n3 n4 0 85 48 1409 (dotNN h 1579 1494 1361 1409) 0 lo hi D hD
      (1579, 1494, 1361, 1409) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
    rw [dotNN_eq] at this
    simpa [boxV, V5.get, hsub] using this
  · subst hw
    have := rayZ_le n1 n2 n3 n4 0 3291 1893 53789 (dotNN h 60371 57080 51896 53789) 0 lo hi D hD
      (60371, 57080, 51896, 53789) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
    rw [dotNN_eq] at this
    simpa [boxV, V5.get, hsub] using this
  · have hc := rayZ_le n1 n2 n3 n4 2 1091 630 17816 (dotNN h 20000 18907 17186 17816) 1280 lo hi D
      hD (20000, 18907, 17186, 17816) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
    rw [dotNN_eq] at hc
    replace hc := hc.trans_eq (show _ = dot (cls D - hQ h) (20000, 18907, 17186, 17816) - 1280 by
      rw [hsub]; norm_num)
    simp only [boxV, V5.get]
    obtain ⟨b1, b2, b3⟩ := hb
    rw [abs_le] at b1 b2 b3
    generalize (rayZ n1 n2 n3 n4 2 1091 630 17816 (dotNN h 20000 18907 17186 17816) 1280 lo hi).val
      = r at hc ⊢
    generalize cls D - hQ h = d at hc b1 b2 b3 ⊢
    obtain ⟨d0, d1, d2, d3⟩ := d
    simp only [dot] at hc ⊢
    simp only at b1 b2 b3
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [dot] <;> nlinarith [b1.1, b1.2, b2.1, b2.2, b3.1, b3.2]

end GridGen.Four.K4
