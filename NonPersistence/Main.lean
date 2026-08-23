/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import NonPersistence.Compare

/-!
# Non-persistence (Zhang–Dong, Theorem 6)

For every `k ≥ 3` there are graphs with `P(G, k) = P_ℓ(G, k) > 0` and `P(G, k+1) > P_ℓ(G, k+1)`,
and arbitrarily large ones, so infinitely many.

This refutes Kirov–Naimi 2016, §6, Question 2 — *is an `n`-colorable `n`-monophilic graph
necessarily `(n+1)`-monophilic?* — equivalently `ν(G) = τ(G)`. `OpenProblems.lean` carries that
question in the direction the paper conjectured; `not_persistence` below is its answer.

## The threshold

Zhang–Dong take `t₀ = ⌈k² log((7k+1)/2)⌉` and compute the count at `k + 1` exactly (their
Lemma 11). Neither is needed. Because the surplus of agreeing base colorings is bounded below by
**one** (`card_SbadA_lt`), and the apex deficit `(k² - 1)/k²` compounds, any threshold linear in
the number of base colorings works — here `t₀ m = (m + 2)(m + 4) · |Sbad m|`, proved by Bernoulli
in `ℕ`. The constant is far worse than Zhang–Dong's and the theorem is the same.
-/

open Finset SimpleGraph

namespace ZhangDong

/-! ### Both counts, collapsed to sums over the base -/

theorem col_zd_eq (m t : ℕ) :
    (zd m t).col (Lbad m t)
      = ∑ θ ∈ Sbad m, ∏ i ∈ Finset.range (4 * t), (A m i \ (sPair m).image θ).card := by
  have h := sum_col_iterCone (H m) (sPair m) (LH m) (A m) (4 * t) (fun _ => 1)
  simp only [mul_one] at h
  rw [SimpleGraph.col, Finset.card_eq_sum_ones]
  exact h

theorem colConst_zd_eq (m t : ℕ) :
    (zd m t).colConst (m + 4)
      = ∑ f ∈ Tconst m, ∏ _i ∈ Finset.range (4 * t),
          (Finset.range (m + 4) \ (sPair m).image f).card := by
  have hconst : constList (TowerV (Option (Option (XV m))) (4 * t)) (m + 4)
      = towerListF (constList (Option (Option (XV m))) (m + 4))
          (fun _ => Finset.range (m + 4)) (4 * t) :=
    (towerListF_constList (m + 4) (4 * t)).symm
  have h := sum_col_iterCone (H m) (sPair m) (constList (Option (Option (XV m))) (m + 4))
    (fun _ => Finset.range (m + 4)) (4 * t) (fun _ => 1)
  simp only [mul_one] at h
  rw [SimpleGraph.colConst, hconst, SimpleGraph.col, Finset.card_eq_sum_ones]
  exact h

/-! ### The two bounds -/

theorem col_zd_le (m t : ℕ) :
    (zd m t).col (Lbad m t)
      ≤ (SbadA m).card * (m + 3) ^ (4 * t)
        + (Sbad m).card * ((m + 3) ^ 2 * ((m + 2) * (m + 4))) ^ t := by
  rw [col_zd_eq]
  rw [← Finset.sum_filter_add_sum_filter_not (Sbad m) (fun θ => θ (s₁ m) = θ (s₂ m))]
  refine Nat.add_le_add ?_ ?_
  · have hA : ∀ θ ∈ (Sbad m).filter (fun θ => θ (s₁ m) = θ (s₂ m)),
        ∏ i ∈ Finset.range (4 * t), (A m i \ (sPair m).image θ).card = (m + 3) ^ (4 * t) := by
      intro θ hθ
      rw [Finset.mem_filter] at hθ
      exact prod_eq_of_agree hθ.1 hθ.2 t
    rw [Finset.sum_congr rfl hA, Finset.sum_const, smul_eq_mul]
    exact le_rfl
  · have hle : ∑ θ ∈ (Sbad m).filter (fun θ => ¬ (θ (s₁ m) = θ (s₂ m))),
        ∏ i ∈ Finset.range (4 * t), (A m i \ (sPair m).image θ).card
          ≤ ∑ _θ ∈ (Sbad m).filter (fun θ => ¬ (θ (s₁ m) = θ (s₂ m))),
              ((m + 3) ^ 2 * ((m + 2) * (m + 4))) ^ t := by
      refine Finset.sum_le_sum fun θ hθ => ?_
      rw [Finset.mem_filter] at hθ
      exact prod_le_of_disagree hθ.1 hθ.2 t
    refine le_trans hle ?_
    rw [Finset.sum_const, smul_eq_mul]
    exact Nat.mul_le_mul_right _ (Finset.card_le_card (Finset.filter_subset _ _))

theorem le_colConst_zd (m t : ℕ) :
    (TconstA m).card * (m + 3) ^ (4 * t) ≤ (zd m t).colConst (m + 4) := by
  rw [colConst_zd_eq]
  have hsub : (TconstA m) ⊆ Tconst m := Finset.filter_subset _ _
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum_of_subset hsub)
  have hA : ∀ f ∈ TconstA m,
      ∏ _i ∈ Finset.range (4 * t), (Finset.range (m + 4) \ (sPair m).image f).card
        = (m + 3) ^ (4 * t) := by
    intro f hf
    rw [TconstA, Finset.mem_filter] at hf
    exact prod_eq_of_agree_const hf.1 hf.2 t
  rw [Finset.sum_congr rfl hA, Finset.sum_const, smul_eq_mul]

/-! ### The threshold and the strict inequality -/

/-- The threshold: any `t` at least this makes the bad assignment win. Explicit, and far from
optimal — see the module docstring. -/
def t₀ (m : ℕ) : ℕ := (m + 2) * (m + 4) * (Sbad m).card

/-- **Zhang–Dong, Proposition 12.** Past the threshold the bad `(k+1)`-list assignment admits
strictly fewer colorings than the full palette. -/
theorem col_lt_colConst (m t : ℕ) (ht : t₀ m ≤ t) :
    (zd m t).col (Lbad m t) < (zd m t).colConst (m + 4) := by
  -- the error term is beaten by Bernoulli
  have hQ : 1 ≤ (m + 2) * (m + 4) := by nlinarith
  have hbern : (Sbad m).card * ((m + 2) * (m + 4)) ^ t < ((m + 2) * (m + 4) + 1) ^ t :=
    mul_pow_lt_pow hQ ht
  have hsq : (m + 2) * (m + 4) + 1 = (m + 3) ^ 2 := by ring
  rw [hsq] at hbern
  -- rewrite both powers of `t` against `((m+3)^2)^t`
  have hsplit : ((m + 3) ^ 2 * ((m + 2) * (m + 4))) ^ t
      = ((m + 3) ^ 2) ^ t * ((m + 2) * (m + 4)) ^ t := mul_pow _ _ t
  have h4t : (m + 3) ^ (4 * t) = ((m + 3) ^ 2) ^ t * ((m + 3) ^ 2) ^ t := by
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  -- the error term is strictly smaller than one full block
  have herr : (Sbad m).card * ((m + 3) ^ 2 * ((m + 2) * (m + 4))) ^ t < (m + 3) ^ (4 * t) := by
    rw [hsplit, h4t]
    calc (Sbad m).card * (((m + 3) ^ 2) ^ t * ((m + 2) * (m + 4)) ^ t)
        = ((Sbad m).card * ((m + 2) * (m + 4)) ^ t) * ((m + 3) ^ 2) ^ t := by ring
      _ < ((m + 3) ^ 2) ^ t * ((m + 3) ^ 2) ^ t :=
          mul_lt_mul_of_pos_right hbern (pow_pos (by positivity) t)
  -- and one full block is what the strict inclusion buys
  have hcard : (SbadA m).card + 1 ≤ (TconstA m).card := card_SbadA_lt m
  calc (zd m t).col (Lbad m t)
      ≤ (SbadA m).card * (m + 3) ^ (4 * t)
        + (Sbad m).card * ((m + 3) ^ 2 * ((m + 2) * (m + 4))) ^ t := col_zd_le m t
    _ < (SbadA m).card * (m + 3) ^ (4 * t) + (m + 3) ^ (4 * t) := by omega
    _ = ((SbadA m).card + 1) * (m + 3) ^ (4 * t) := by ring
    _ ≤ (TconstA m).card * (m + 3) ^ (4 * t) := Nat.mul_le_mul_right _ hcard
    _ ≤ (zd m t).colConst (m + 4) := le_colConst_zd m t

/-- **Zhang–Dong, Theorem 6, for one graph.** -/
theorem not_ECCAt_succ (m t : ℕ) (ht : t₀ m ≤ t) : ¬ (zd m t).ECCAt (m + 4) := by
  intro hcon
  exact absurd (hcon (Lbad m t) (isNListAssignment_Lbad m t)) (Nat.not_le.mpr
    (col_lt_colConst m t ht))

end ZhangDong
