/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import NonPersistence.BadList

/-!
# Two pieces of arithmetic

**Bernoulli, in natural numbers.** Zhang–Dong bound their error term with logarithms and get the
threshold `t₀ = ⌈k² log((7k+1)/2)⌉`. Nothing that sharp is needed: the theorem asks only for
*some* explicit threshold per `k`, and a cruder one keeps the whole comparison inside `ℕ`. What
`mul_pow_lt_pow` says is that `Q^t` beats any fixed multiple of `(Q-1)^t` once `t` is linear in
that multiple — which is Bernoulli's inequality, proved here by a two-line induction.

**Four-periodic products.** The apex lists cycle with period four, so a product over `4t` steps is
the fourth-block product raised to the `t`.
-/

open Finset

namespace ZhangDong

/-! ### Bernoulli -/

/-- `(Q + 1)^t · Q ≥ Q^t · (Q + t)`: Bernoulli's inequality, cleared of denominators so that it
lives in `ℕ`. -/
theorem pow_succ_mul_le (Q : ℕ) : ∀ t : ℕ, Q ^ t * (Q + t) ≤ (Q + 1) ^ t * Q := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
      have h : (Q + 1) ^ (t + 1) * Q = (Q + 1) * ((Q + 1) ^ t * Q) := by ring
      calc Q ^ (t + 1) * (Q + (t + 1))
          ≤ Q ^ (t + 1) * (Q + (t + 1)) + Q ^ t * t := Nat.le_add_right _ _
        _ = (Q + 1) * (Q ^ t * (Q + t)) + (Q ^ t * Q * Q - Q ^ t * Q * Q) := by
            simp only [Nat.sub_self, Nat.add_zero]
            ring
        _ ≤ (Q + 1) * ((Q + 1) ^ t * Q) := by
            simp only [Nat.sub_self, Nat.add_zero]
            exact Nat.mul_le_mul_left _ ih
        _ = (Q + 1) ^ (t + 1) * Q := h.symm

/-- **The comparison the counterexample needs.** Once `t` is at least `Q · N`, the `t`-th power of
`Q + 1` beats `N` copies of the `t`-th power of `Q`.

Applied with `Q = k² - 1` and `N` the number of colorings of `H m` from the bad lists, this is
what makes the deficit at the apexes overwhelm the surplus of base colorings. -/
theorem mul_pow_lt_pow {Q N t : ℕ} (hQ : 1 ≤ Q) (ht : Q * N ≤ t) :
    N * Q ^ t < (Q + 1) ^ t := by
  have hQpos : 0 < Q := hQ
  have hQt : 0 < Q ^ t := pow_pos hQpos t
  -- from Bernoulli, `Q^t * (Q + t) ≤ (Q+1)^t * Q`
  have hb := pow_succ_mul_le Q t
  -- and `Q + t ≥ Q * (N + 1)`
  have hge : Q * (N + 1) ≤ Q + t := by
    have : Q * (N + 1) = Q * N + Q := by ring
    omega
  have h1 : Q ^ t * (Q * (N + 1)) ≤ (Q + 1) ^ t * Q :=
    le_trans (Nat.mul_le_mul_left _ hge) hb
  have h2 : (Q ^ t * (N + 1)) * Q ≤ (Q + 1) ^ t * Q := by
    calc (Q ^ t * (N + 1)) * Q = Q ^ t * (Q * (N + 1)) := by ring
      _ ≤ (Q + 1) ^ t * Q := h1
  have h3 : Q ^ t * (N + 1) ≤ (Q + 1) ^ t := Nat.le_of_mul_le_mul_right h2 hQpos
  calc N * Q ^ t < Q ^ t * (N + 1) := by nlinarith
    _ ≤ (Q + 1) ^ t := h3

/-! ### Four-periodic products -/

/-- A product over `4t` steps of a four-periodic function is the block product to the `t`. -/
theorem prod_range_four_mul (g : ℕ → ℕ) : ∀ t : ℕ,
    ∏ i ∈ Finset.range (4 * t), g (i % 4) = (∏ j ∈ Finset.range 4, g j) ^ t := by
  intro t
  induction t with
  | zero => norm_num
  | succ t ih =>
      have hstep : 4 * (t + 1) = 4 * t + 1 + 1 + 1 + 1 := by ring
      rw [hstep, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
        Finset.prod_range_succ, ih]
      have e0 : (4 * t) % 4 = 0 := by omega
      have e1 : (4 * t + 1) % 4 = 1 := by omega
      have e2 : (4 * t + 1 + 1) % 4 = 2 := by omega
      have e3 : (4 * t + 1 + 1 + 1) % 4 = 3 := by omega
      rw [e0, e1, e2, e3]
      have hfour : ∏ j ∈ Finset.range 4, g j = g 0 * g 1 * g 2 * g 3 := by
        rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
          Finset.prod_range_one]
      rw [hfour, pow_succ]
      ring

end ZhangDong
