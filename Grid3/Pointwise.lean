/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Grid3.Middle

/-!
# The pointwise deficiency bound

For a state `s = (a, b, c)` and a next column `(T, M, B)` of `k`-lists, the successor count is
`∑_{m ∈ M \ b} |T \ {a, m}| · |B \ {c, m}|`, and each factor splits as the uniform value
`k - 2 + [a = m]` plus a nonnegative *bonus* `dT T a m`. Dropping the products of bonuses and
using `k - 2` for the uniform factors gives the lower bound `LB s ≤ dH s` on the deficiency,
which is exact at uniform and is what the pair lemmas are proved from.
-/

open Finset

namespace Grid3

/-- The integer indicator of a proposition. -/
def ind (p : Prop) [Decidable p] : ℤ := if p then 1 else 0

@[simp] theorem ind_true {p : Prop} [Decidable p] (h : p) : ind p = 1 := by simp [ind, h]
@[simp] theorem ind_false {p : Prop} [Decidable p] (h : ¬ p) : ind p = 0 := by simp [ind, h]
theorem ind_nonneg (p : Prop) [Decidable p] : 0 ≤ ind p := by unfold ind; split_ifs <;> norm_num
theorem ind_le_one (p : Prop) [Decidable p] : ind p ≤ 1 := by unfold ind; split_ifs <;> norm_num
theorem ind_not (p : Prop) [Decidable p] : ind (¬ p) = 1 - ind p := by
  unfold ind; split_ifs <;> simp_all

theorem eqInd_eq_ind (s : State) : (eqInd s : ℤ) = ind (s.1 = s.2.2) := by
  unfold eqInd ind IsEq; by_cases h : s.1 = s.2.2 <;> simp [h]

/-! ### Cardinalities of punctured lists -/

theorem card_erase_int (T : Finset ℕ) (a : ℕ) : ((T.erase a).card : ℤ) = T.card - ind (a ∈ T) := by
  by_cases h : a ∈ T
  · rw [Finset.card_erase_of_mem h, ind_true h]
    have := Finset.card_pos.mpr ⟨a, h⟩
    push_cast [Nat.cast_sub this]; ring
  · rw [Finset.erase_eq_of_notMem h, ind_false h]; simp

theorem card_erase_erase_int (T : Finset ℕ) (a m : ℕ) :
    (((T.erase a).erase m).card : ℤ) = T.card - ind (a ∈ T) - ind (a ≠ m ∧ m ∈ T) := by
  rw [card_erase_int (T.erase a) m, card_erase_int T a]
  congr 1
  unfold ind
  by_cases h : m ∈ T.erase a
  · rw [if_pos h, if_pos (by rw [Finset.mem_erase] at h; exact ⟨Ne.symm h.1, h.2⟩)]
  · rw [if_neg h, if_neg (by intro h'; exact h (Finset.mem_erase.mpr ⟨Ne.symm h'.1, h'.2⟩))]

/-- The bonus of the top (or bottom) factor over its uniform value. -/
def dT (T : Finset ℕ) (a m : ℕ) : ℤ := ind (m ∉ T) * ind (a ≠ m) + ind (a ∉ T)

theorem dT_nonneg (T : Finset ℕ) (a m : ℕ) : 0 ≤ dT T a m := by
  unfold dT; exact add_nonneg (mul_nonneg (ind_nonneg _) (ind_nonneg _)) (ind_nonneg _)

/-- **The split.** `|T \ {a, m}| = (k - 2 + [a = m]) + dT T a m`. -/
theorem card_erase_erase_split {k : ℕ} {T : Finset ℕ} (hT : T.card = k) (a m : ℕ) :
    (((T.erase a).erase m).card : ℤ) = ((k : ℤ) - 2 + ind (a = m)) + dT T a m := by
  rw [card_erase_erase_int, hT]
  unfold dT ind
  by_cases ham : a = m
  · subst ham
    by_cases ha : a ∈ T <;> simp [ha] <;> omega
  · by_cases ha : a ∈ T <;> by_cases hm : m ∈ T <;> simp [ha, hm, ham] <;> omega

/-- The successor count as a sum over the next middle colour. -/
theorem succ_eq_sum (T M B : Finset ℕ) (a b c : ℕ) :
    succ T M B (a, b, c)
      = ∑ m ∈ M.erase b, ((T.erase a).erase m).card * ((B.erase c).erase m).card := by
  rw [succ_eq_card, card_states]

/-! ### The bound -/

/-- The lower bound on the deficiency of `(a, b, c)`. -/
def LB (k : ℕ) (T M B : Finset ℕ) (s : State) : ℤ :=
  ((k : ℤ) - 2) ^ 2 * ind (s.2.1 ∉ M) - ((k : ℤ) - 2) * (ind (s.1 ∉ M) + ind (s.2.2 ∉ M))
    - ind (s.1 = s.2.2) * ind (s.1 ∉ M)
    + ((k : ℤ) - 2) * (∑ m ∈ M.erase s.2.1, dT T s.1 m + ∑ m ∈ M.erase s.2.1, dT B s.2.2 m)

/-- The uniform part of the product sum, in closed form. -/
theorem sum_uniform_part (k : ℕ) (M : Finset ℕ) {a b c : ℕ} (hab : a ≠ b) (hcb : c ≠ b) :
    ∑ m ∈ M.erase b, ((k : ℤ) - 2 + ind (a = m)) * ((k : ℤ) - 2 + ind (c = m))
      = ((k : ℤ) - 2) ^ 2 * (M.erase b).card + ((k : ℤ) - 2) * (ind (a ∈ M) + ind (c ∈ M))
        + ind (a = c) * ind (a ∈ M) := by
  have hpt : ∀ m ∈ M.erase b, ((k : ℤ) - 2 + ind (a = m)) * ((k : ℤ) - 2 + ind (c = m))
      = ((k : ℤ) - 2) ^ 2 + ((k : ℤ) - 2) * (if a = m then 1 else 0)
        + ((k : ℤ) - 2) * (if c = m then 1 else 0) + (if a = m then (if c = m then 1 else 0) else 0) := by
    intro m _
    unfold ind
    split_ifs <;> ring
  rw [Finset.sum_congr rfl hpt]
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum,
    Finset.sum_ite_eq]
  have ha : a ∈ M.erase b ↔ a ∈ M := by rw [Finset.mem_erase]; exact ⟨fun h => h.2, fun h => ⟨hab, h⟩⟩
  have hc : c ∈ M.erase b ↔ c ∈ M := by rw [Finset.mem_erase]; exact ⟨fun h => h.2, fun h => ⟨hcb, h⟩⟩
  unfold ind
  by_cases hac : a = c
  · subst hac
    by_cases haM : a ∈ M <;> simp [ha, haM] <;> ring
  · by_cases haM : a ∈ M <;> by_cases hcM : c ∈ M <;> simp [ha, hc, haM, hcM, hac, Ne.symm hac] <;> ring

/-- **The pointwise bound.** -/
theorem LB_le_dH {k : ℕ} (hk : 2 ≤ k) {T M B : Finset ℕ} (hT : T.card = k) (hM : M.card = k)
    (hB : B.card = k) {a b c : ℕ} (hab : a ≠ b) (hbc : b ≠ c) :
    LB k T M B (a, b, c) ≤ dH k T M B (a, b, c) := by
  unfold dH
  rw [succ_eq_sum, eqInd_eq_ind]
  push_cast
  -- each product is at least the uniform product plus `(k-2)` times the bonuses
  have hterm : ∀ m ∈ M.erase b,
      ((k : ℤ) - 2 + ind (a = m)) * ((k : ℤ) - 2 + ind (c = m))
          + ((k : ℤ) - 2) * (dT T a m + dT B c m)
        ≤ (((T.erase a).erase m).card : ℤ) * (((B.erase c).erase m).card : ℤ) := by
    intro m _
    rw [card_erase_erase_split hT, card_erase_erase_split hB]
    have h1 := dT_nonneg T a m
    have h2 := dT_nonneg B c m
    have h3 := ind_nonneg (a = m)
    have h4 := ind_nonneg (c = m)
    have hk2 : (0 : ℤ) ≤ (k : ℤ) - 2 := by omega
    nlinarith [mul_nonneg h1 h2, mul_nonneg h3 h2, mul_nonneg h1 h4, mul_nonneg hk2 h1,
      mul_nonneg hk2 h2]
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, sum_uniform_part k M hab (Ne.symm hbc), ← Finset.mul_sum,
    Finset.sum_add_distrib] at hsum
  unfold LB
  simp only
  rw [card_erase_int M b, hM] at hsum
  rw [ind_not, ind_not, ind_not]
  have hene : ((ene k : ℕ) : ℤ) = ((k : ℤ) - 1) * ((k : ℤ) - 2) ^ 2 + 2 * ((k : ℤ) - 2) := by
    unfold ene; push_cast [Nat.cast_sub hk, Nat.cast_sub (by omega : 1 ≤ k)]; ring
  rw [hene]
  linarith [hsum]

end Grid3
