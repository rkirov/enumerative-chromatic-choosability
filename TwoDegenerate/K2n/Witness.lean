/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import TwoDegenerate.K2n.Count
import Mathlib.Tactic.Ring

/-!
# A balanced family of list assignments on `K₂,ₙ`

This is the family of Lemma 11 of Kaul, Kumar, Liu, Mudrock, Rewers, Shin, Tanahara and To,
*Bounding the list color function threshold from above* (Involve 16 (2023)). The hubs get
`A = {0, …, k-1}` and `B = {0, …, k-3} ∪ {k, k+1}`, which share `k - 2` colours; right vertex `w`
gets `{0, …, k-3} ∪ {a, b}` with `(a, b)` running through `(k-2, k)`, `(k-1, k+1)`, `(k-2, k+1)`,
`(k-1, k)` as `w mod 4 = 0, 1, 2, 3`.

For `n = 4q + s` the count is `∑_{a,b} c_{ab} G_{ab}^q` with `G_{ab} ≤ (k-1)⁴`, so once it is below
`k (k-1)^s ((k-1)⁴)^q` at one `q` it stays below for every larger `q` (`sum_geom_lt`), and
`k (k-1)ⁿ ≤ P(K₂,ₙ, k)`. Kaul et al. use Theorem 14 of Kaul–Kumar–Mudrock–Rewers–Shin–To
(arXiv:2202.03431) for large `n`; this induction replaces it.
-/

namespace SimpleGraph.TwoDegenerate.K2n

open Finset

/-- The hub lists. -/
def hubA (k : ℕ) : Finset ℕ := range k
def hubB (k : ℕ) : Finset ℕ := range (k - 2) ∪ {k, k + 1}

/-- The list of a right vertex of type `t mod 4`. -/
def rightT (k t : ℕ) : Finset ℕ :=
  range (k - 2) ∪
    (if t % 4 = 0 then {k - 2, k} else if t % 4 = 1 then {k - 1, k + 1}
      else if t % 4 = 2 then {k - 2, k + 1} else {k - 1, k})

/-- The witness list assignment on `K₂,ₙ`. -/
def witness (k n : ℕ) : ListAssignment (Fin 2 ⊕ Fin n) :=
  Sum.elim (fun i => if i = 0 then hubA k else hubB k) (fun w => rightT k w.val)

theorem rightT_mod (k t : ℕ) : rightT k (t % 4) = rightT k t := by
  simp only [rightT, Nat.mod_mod]

/-- `|T_t \ {a, b}|`. -/
def cnt (k a b t : ℕ) : ℕ := (rightT k t \ {a, b}).card

/-- The count at `n = 4q + s`, as a sum of geometric terms. -/
def S (k s q : ℕ) : ℕ :=
  ∑ a ∈ hubA k, ∑ b ∈ hubB k,
    (∏ t ∈ range s, cnt k a b t) * (∏ t ∈ range 4, cnt k a b t) ^ q

theorem prod_range_four_mul (h : ℕ → ℕ) (q : ℕ) :
    ∏ w ∈ range (4 * q), h (w % 4) = (∏ t ∈ range 4, h t) ^ q := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show 4 * (q + 1) = 4 * q + 4 by ring, prod_range_add, ih, pow_succ]
    congr 1
    refine prod_congr rfl fun x hx => ?_
    rw [Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod,
      Nat.mod_eq_of_lt (mem_range.mp hx)]

theorem prod_range_mod_four (h : ℕ → ℕ) (q s : ℕ) (hs : s ≤ 4) :
    ∏ w ∈ range (4 * q + s), h (w % 4) = (∏ t ∈ range s, h t) * (∏ t ∈ range 4, h t) ^ q := by
  rw [prod_range_add, prod_range_four_mul, mul_comm]
  congr 1
  refine prod_congr rfl fun x hx => ?_
  rw [Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod,
    Nat.mod_eq_of_lt (lt_of_lt_of_le (mem_range.mp hx) hs)]

theorem col_witness (k q s : ℕ) (hs : s ≤ 4) :
    (completeBipartiteGraph (Fin 2) (Fin (4 * q + s))).col (witness k (4 * q + s)) = S k s q := by
  rw [col_completeBipartite_two_right]
  simp only [witness, Sum.elim_inl, Sum.elim_inr]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  rw [Fin.prod_univ_eq_prod_range (fun w => (rightT k w \ {a, b}).card)]
  rw [prod_congr rfl fun w _ => by rw [← rightT_mod]]
  exact prod_range_mod_four (fun t => cnt k a b t) q s hs

/-- Once below the geometric bound at `q₀`, below it for good: every ratio `G_p ≤ R`. -/
theorem sum_geom_lt {ι : Type*} (P : Finset ι) (c G : ι → ℕ) {R D q₀ : ℕ} (hR : 0 < R)
    (hG : ∀ p ∈ P, G p ≤ R) (h₀ : ∑ p ∈ P, c p * G p ^ q₀ < D * R ^ q₀) :
    ∀ q, q₀ ≤ q → ∑ p ∈ P, c p * G p ^ q < D * R ^ q := by
  intro q hq
  induction q, hq using Nat.le_induction with
  | base => exact h₀
  | succ q _ ih =>
    calc ∑ p ∈ P, c p * G p ^ (q + 1) ≤ ∑ p ∈ P, c p * G p ^ q * R :=
          sum_le_sum fun p hp => by
            rw [pow_succ, ← mul_assoc]; exact Nat.mul_le_mul_left _ (hG p hp)
      _ = R * ∑ p ∈ P, c p * G p ^ q := by rw [← sum_mul, mul_comm]
      _ < R * (D * R ^ q) := Nat.mul_lt_mul_of_pos_left ih hR
      _ = D * R ^ (q + 1) := by ring

/-- The witness beats the constant count at `n = 4q + s` for every `q ≥ q₀`, given the two
finite checks at `q₀`. -/
theorem col_witness_lt {k s q₀ : ℕ} (hk : 2 ≤ k) (hs : s < 4)
    (hG : ∀ a ∈ hubA k, ∀ b ∈ hubB k, ∏ t ∈ range 4, cnt k a b t ≤ (k - 1) ^ 4)
    (h₀ : S k s q₀ < k * (k - 1) ^ s * ((k - 1) ^ 4) ^ q₀) (q : ℕ) (hq : q₀ ≤ q) :
    (completeBipartiteGraph (Fin 2) (Fin (4 * q + s))).col (witness k (4 * q + s)) <
      (completeBipartiteGraph (Fin 2) (Fin (4 * q + s))).colConst k := by
  have hR : 0 < (k - 1) ^ 4 := Nat.pow_pos (by omega)
  have key := sum_geom_lt (hubA k ×ˢ hubB k)
    (fun p => ∏ t ∈ range s, cnt k p.1 p.2 t) (fun p => ∏ t ∈ range 4, cnt k p.1 p.2 t) hR
    (fun p hp => hG p.1 (mem_product.mp hp).1 p.2 (mem_product.mp hp).2)
    (by rw [sum_product]; exact h₀) q hq
  rw [sum_product] at key
  rw [col_witness k q s hs.le, colConst_K2n]
  calc S k s q < k * (k - 1) ^ s * ((k - 1) ^ 4) ^ q := key
    _ = k * (k - 1) ^ (4 * q + s) := by rw [← pow_mul, mul_assoc, ← pow_add, add_comm]
    _ ≤ _ := Nat.le_add_right _ _

end SimpleGraph.TwoDegenerate.K2n
