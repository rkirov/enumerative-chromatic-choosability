/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.Local

/-!
# Height five: the count of a column from its interval profile

`ai_research_notes/H5_K6_ANALYTIC_2026-10-23.md` §1.3, Lemmas 5–6.

The number of proper colourings of a five-row path from lists `A₁, …, A₅` is a polynomial `N5z`
in the list sizes `nᵢ`, the consecutive intersections `a, b, c, d` (`|A₁ ∩ A₂|`, …), the triple
intersections `t₁, t₂, t₃`, the quadruple ones `q₁, q₂` and the fivefold one `f`
(`card_sts_N5z`, from `card_sts_formula`). Every real system satisfies the relaxation
`tᵢ ≥ max (0, ·)`, `q ≤ min` of its two triples, `f ≥ max (0, q₁ + q₂ - t₂)`.

**Greedy minimality** (Lemma 5, `greedy_min`). Over the relaxation, `N5z` is smallest at the
greedy profile: every `t` at its lower bound, `q` the minimum of its two `t`'s, `f` at its lower
bound. `N5z` is affine in `(t, q, f)` with slope `+1` in `f` and `-n₅`, `-n₁` in `q₁`, `q₂`, and
after pushing `f` and the `q`'s to their bounds the slopes in the `t`'s stay positive.

**The universal constant** (Lemma 6, `kapOK`). At the greedy profile, for every
`nᵢ ∈ {5, 6}` and `0 ≤ eⱼ ≤ min (nⱼ₋₁, nⱼ)`,
`128018 · N5(greedy) · n₂n₃n₄ ≥ 123125 · ∏ⱼ (nⱼ₋₁nⱼ - eⱼ)`, so
`|sts A| ≥ κ · n₁ ∏ⱼ (nⱼ - eⱼ/nⱼ₋₁)` with `κ = 123125/128018`. The check is a Boolean function
of the five sizes (`kapOK`), evaluated by `decide` in `GridGen/Five/Kappa5.lean`.
-/

namespace GridGen.Five

open Finset

/-- The count of a five-row column as a polynomial in its interval profile. -/
def N5z (n1 n2 n3 n4 n5 a b c d t1 t2 t3 q1 q2 f : ℤ) : ℤ :=
  n1 * n2 * n3 * n4 * n5 - a * n3 * n4 * n5 - n1 * b * n4 * n5 - n1 * n2 * c * n5
    - n1 * n2 * n3 * d + t1 * n4 * n5 + a * c * n5 + a * n3 * d + n1 * t2 * n5 + n1 * b * d
    + n1 * n2 * t3 - q1 * n5 - t1 * d - a * t3 - n1 * q2 + f

/-- The count from the interval profile. -/
theorem card_sts_N5z (A₁ A₂ A₃ A₄ A₅ : Finset ℕ) :
    ((sts A₁ A₂ A₃ A₄ A₅).card : ℤ) =
      N5z A₁.card A₂.card A₃.card A₄.card A₅.card (A₁ ∩ A₂).card (A₂ ∩ A₃).card
        (A₃ ∩ A₄).card (A₄ ∩ A₅).card (A₁ ∩ A₂ ∩ A₃).card (A₂ ∩ A₃ ∩ A₄).card
        (A₃ ∩ A₄ ∩ A₅).card (A₁ ∩ A₂ ∩ A₃ ∩ A₄).card (A₂ ∩ A₃ ∩ A₄ ∩ A₅).card
        (A₁ ∩ A₂ ∩ A₃ ∩ A₄ ∩ A₅).card := by
  rw [card_sts_formula]
  unfold N5z
  ring

/-- The greedy profile value. -/
def N5g (n1 n2 n3 n4 n5 a b c d : ℤ) : ℤ :=
  N5z n1 n2 n3 n4 n5 a b c d (max 0 (a + b - n2)) (max 0 (b + c - n3)) (max 0 (c + d - n4))
    (min (max 0 (a + b - n2)) (max 0 (b + c - n3))) (min (max 0 (b + c - n3)) (max 0 (c + d - n4)))
    (max 0 (min (max 0 (a + b - n2)) (max 0 (b + c - n3))
      + min (max 0 (b + c - n3)) (max 0 (c + d - n4)) - max 0 (b + c - n3)))

/-- **Greedy minimality** (Lemma 5). -/
theorem greedy_min {n1 n2 n3 n4 n5 a b c d t1 t2 t3 q1 q2 f : ℤ}
    (hn1 : 5 ≤ n1) (hn2 : 5 ≤ n2) (hn4 : 5 ≤ n4) (hn5 : 5 ≤ n5)
    (ha : a ≤ n1) (hd : d ≤ n5)
    (ht1 : 0 ≤ t1) (ht1' : a + b - n2 ≤ t1) (ht2 : 0 ≤ t2) (ht2' : b + c - n3 ≤ t2)
    (ht3 : 0 ≤ t3) (ht3' : c + d - n4 ≤ t3)
    (hq1 : q1 ≤ t1) (hq1' : q1 ≤ t2) (hq2 : q2 ≤ t2) (hq2' : q2 ≤ t3)
    (hf : 0 ≤ f) (hf' : q1 + q2 - t2 ≤ f) :
    N5g n1 n2 n3 n4 n5 a b c d ≤ N5z n1 n2 n3 n4 n5 a b c d t1 t2 t3 q1 q2 f := by
  unfold N5g
  set T1 := max 0 (a + b - n2) with hT1
  set T2 := max 0 (b + c - n3) with hT2
  set T3 := max 0 (c + d - n4) with hT3
  set M1 := min T1 T2 with hM1
  set M2 := min T2 T3 with hM2
  set F := max 0 (M1 + M2 - T2) with hF
  set m1 := min t1 t2 with hm1
  set m2 := min t2 t3 with hm2
  -- the actual profile dominates the greedy one
  have D1 : T1 ≤ t1 := max_le ht1 ht1'
  have D2 : T2 ≤ t2 := max_le ht2 ht2'
  have D3 : T3 ≤ t3 := max_le ht3 ht3'
  have hT10 : 0 ≤ T1 := le_max_left _ _
  have hT20 : 0 ≤ T2 := le_max_left _ _
  have hT30 : 0 ≤ T3 := le_max_left _ _
  have e1 : q1 ≤ m1 := le_min hq1 hq1'
  have e2 : q2 ≤ m2 := le_min hq2 hq2'
  -- the minima move by at most the sum of the moves
  have g1 : m1 - M1 ≤ (t1 - T1) + (t2 - T2) := by
    rw [hm1, hM1]; rcases le_total t1 t2 with h | h <;> rcases le_total T1 T2 with h' | h' <;>
      simp only [min_eq_left, min_eq_right, h, h'] <;> linarith
  have g2 : m2 - M2 ≤ (t2 - T2) + (t3 - T3) := by
    rw [hm2, hM2]; rcases le_total t2 t3 with h | h <;> rcases le_total T2 T3 with h' | h' <;>
      simp only [min_eq_left, min_eq_right, h, h'] <;> linarith
  have g1' : M1 ≤ m1 := min_le_min D1 D2
  have g2' : M2 ≤ m2 := min_le_min D2 D3
  have hm1t2 : m1 ≤ t2 := min_le_right _ _
  have hm2t2 : m2 ≤ t2 := min_le_left _ _
  -- the fivefold term
  have gF : F ≤ f + (m1 - q1) + (m2 - q2) + (t2 - T2) := by
    rw [hF]; refine max_le (by linarith) (by linarith)
  -- slopes
  have s1 : 0 ≤ (n4 * n5 - d - n5) * (t1 - T1) := by
    apply mul_nonneg _ (by linarith); nlinarith
  have s2 : 0 ≤ (n1 * n5 - n1 - n5 - 1) * (t2 - T2) := by
    apply mul_nonneg _ (by linarith); nlinarith
  have s3 : 0 ≤ (n1 * n2 - a - n1) * (t3 - T3) := by
    apply mul_nonneg _ (by linarith); nlinarith
  have s4 : 0 ≤ (n5 - 1) * (m1 - q1) := mul_nonneg (by linarith) (by linarith)
  have s5 : 0 ≤ (n1 - 1) * (m2 - q2) := mul_nonneg (by linarith) (by linarith)
  have s6 : n5 * (q1 - M1) ≤ n5 * ((t1 - T1) + (t2 - T2) - (m1 - q1)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have s7 : n1 * (q2 - M2) ≤ n1 * ((t2 - T2) + (t3 - T3) - (m2 - q2)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  unfold N5z
  nlinarith

/-! ### The universal constant: the Boolean check -/

/-- `p i` for all `i ≤ m`. -/
def allUpTo (p : ℕ → Bool) : ℕ → Bool
  | 0 => p 0
  | m + 1 => p (m + 1) && allUpTo p m

theorem allUpTo_spec {p : ℕ → Bool} : ∀ {m : ℕ}, allUpTo p m = true → ∀ i ≤ m, p i = true
  | 0, h, i, hi => by rw [Nat.le_zero.mp hi]; exact h
  | m + 1, h, i, hi => by
    simp only [allUpTo, Bool.and_eq_true] at h
    rcases Nat.lt_or_ge i (m + 1) with h' | h'
    · exact allUpTo_spec h.2 i (by omega)
    · rw [show i = m + 1 by omega]; exact h.1

/-- The greedy profile in natural numbers: the positive and negative parts of `N5z`. -/
def kapP (n1 n2 n3 n4 n5 a b c d : ℕ) : ℕ :=
  let t1 := a + b - n2
  let t2 := b + c - n3
  let t3 := c + d - n4
  n1 * n2 * n3 * n4 * n5 + t1 * n4 * n5 + a * c * n5 + a * n3 * d + n1 * t2 * n5 + n1 * b * d
    + n1 * n2 * t3 + (min t1 t2 + min t2 t3 - t2)

def kapM (n1 n2 n3 n4 n5 a b c d : ℕ) : ℕ :=
  let t1 := a + b - n2
  let t2 := b + c - n3
  let t3 := c + d - n4
  a * n3 * n4 * n5 + n1 * b * n4 * n5 + n1 * n2 * c * n5 + n1 * n2 * n3 * d + min t1 t2 * n5
    + t1 * d + a * t3 + n1 * min t2 t3

/-- The check at one profile. -/
def kapAt (n1 n2 n3 n4 n5 a b c d : ℕ) : Bool :=
  decide (128018 * kapM n1 n2 n3 n4 n5 a b c d * (n2 * n3 * n4)
      + 123125 * ((n1 * n2 - a) * (n2 * n3 - b) * (n3 * n4 - c) * (n4 * n5 - d))
    ≤ 128018 * kapP n1 n2 n3 n4 n5 a b c d * (n2 * n3 * n4))

/-- The check over all consecutive intersections, for fixed sizes. -/
def kapOK (n1 n2 n3 n4 n5 : ℕ) : Bool :=
  allUpTo (fun a => allUpTo (fun b => allUpTo (fun c => allUpTo (fun d =>
    kapAt n1 n2 n3 n4 n5 a b c d) (min n4 n5)) (min n3 n4)) (min n2 n3)) (min n1 n2)

theorem kapP_kapM {n1 n2 n3 n4 n5 a b c d : ℕ} :
    (kapP n1 n2 n3 n4 n5 a b c d : ℤ) - kapM n1 n2 n3 n4 n5 a b c d
      = N5g n1 n2 n3 n4 n5 a b c d := by
  simp only [kapP, kapM, N5g, N5z]
  have c1 : ((a + b - n2 : ℕ) : ℤ) = max 0 ((a : ℤ) + b - n2) := by omega
  have c2 : ((b + c - n3 : ℕ) : ℤ) = max 0 ((b : ℤ) + c - n3) := by omega
  have c3 : ((c + d - n4 : ℕ) : ℤ) = max 0 ((c : ℤ) + d - n4) := by omega
  have cf : ((min (a + b - n2) (b + c - n3) + min (b + c - n3) (c + d - n4) - (b + c - n3) : ℕ)
      : ℤ) = max 0 (min (max 0 ((a : ℤ) + b - n2)) (max 0 ((b : ℤ) + c - n3))
        + min (max 0 ((b : ℤ) + c - n3)) (max 0 ((c : ℤ) + d - n4))
        - max 0 ((b : ℤ) + c - n3)) := by
    rw [← c1, ← c2, ← c3]; omega
  push_cast
  rw [cf, c1, c2, c3]
  ring

theorem le_mul_of_le_min {a x y : ℕ} (h : a ≤ min x y) : a ≤ x * y := by
  rcases Nat.eq_zero_or_pos y with h0 | h0
  · subst h0; simp at h; omega
  · exact le_trans (le_trans h (min_le_left _ _)) (Nat.le_mul_of_pos_right _ h0)

/-- **The universal constant at the greedy profile**, from the check. -/
theorem kapOK_sound {n1 n2 n3 n4 n5 : ℕ} (h : kapOK n1 n2 n3 n4 n5 = true) {a b c d : ℕ}
    (ha : a ≤ min n1 n2) (hb : b ≤ min n2 n3) (hc : c ≤ min n3 n4) (hd : d ≤ min n4 n5) :
    123125 * (((n1 : ℤ) * n2 - a) * ((n2 : ℤ) * n3 - b) * ((n3 : ℤ) * n4 - c)
        * ((n4 : ℤ) * n5 - d))
      ≤ 128018 * N5g n1 n2 n3 n4 n5 a b c d * (n2 * n3 * n4) := by
  have h1 := allUpTo_spec h a ha
  have h2 := allUpTo_spec h1 b hb
  have h3 := allUpTo_spec h2 c hc
  have h4 := allUpTo_spec h3 d hd
  simp only [kapAt, decide_eq_true_eq] at h4
  rw [← kapP_kapM]
  have p1 : a ≤ n1 * n2 := le_mul_of_le_min ha
  have hh : (((n1 * n2 - a) * (n2 * n3 - b) * (n3 * n4 - c) * (n4 * n5 - d) : ℕ) : ℤ)
      = ((n1 : ℤ) * n2 - a) * ((n2 : ℤ) * n3 - b) * ((n3 : ℤ) * n4 - c) * ((n4 : ℤ) * n5 - d) := by
    have q2 : b ≤ n2 * n3 := le_mul_of_le_min hb
    have q3 : c ≤ n3 * n4 := le_mul_of_le_min hc
    have q4 : d ≤ n4 * n5 := le_mul_of_le_min hd
    push_cast [Nat.cast_sub p1, Nat.cast_sub q2, Nat.cast_sub q3, Nat.cast_sub q4]
    ring
  have h4' := (Nat.cast_le (α := ℤ)).mpr h4
  push_cast at h4'
  rw [← hh]
  push_cast
  linarith

end GridGen.Five
