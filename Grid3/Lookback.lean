/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Grid3.Main

/-!
# Lookback: pointwise conditions that imply the seam inequalities

`(H1)` and `(C1_r)` are linear in the state vector, and the chain vector at column `j + d` is a
nonnegative combination, over the states `s₀` of column `j`, of the *path vectors* — the numbers
of `d`-step continuations of `s₀` ending in each state. So it suffices to check the two
inequalities pointwise: for every state `s₀` and every `d + 2` consecutive columns of lists, on
the path vector of `s₀` (`DepthOK`), together with the first `d` seams of every chain
(`ShortOK`). At `k ≥ 5` the note's data say depth `1` suffices; at `k = 4`, depth `2`.

This file proves the reduction; the pointwise conditions are the open local lemmas.
-/

open Finset

namespace Grid3

/-! ### Linearity of the seam inequalities -/

theorem total_sum {ι : Type*} (I : Finset ι) (S : Finset State) (Ns : ι → State → ℕ) :
    total S (fun s => ∑ i ∈ I, Ns i s) = ∑ i ∈ I, total S (Ns i) := by
  unfold total; exact Finset.sum_comm

theorem eqMass_sum {ι : Type*} (I : Finset ι) (S : Finset State) (Ns : ι → State → ℕ) :
    eqMass S (fun s => ∑ i ∈ I, Ns i s) = ∑ i ∈ I, eqMass S (Ns i) := by
  unfold eqMass; exact Finset.sum_comm

theorem step_sum {ι : Type*} (I : Finset ι) (S : Finset State) (Ns : ι → State → ℕ) :
    step S (fun s => ∑ i ∈ I, Ns i s) = fun t => ∑ i ∈ I, step S (Ns i) t := by
  funext t; unfold step; exact Finset.sum_comm

theorem total_smul (c : ℕ) (S : Finset State) (N : State → ℕ) :
    total S (fun s => c * N s) = c * total S N := by
  unfold total; rw [Finset.mul_sum]

theorem eqMass_smul (c : ℕ) (S : Finset State) (N : State → ℕ) :
    eqMass S (fun s => c * N s) = c * eqMass S N := by
  unfold eqMass; rw [Finset.mul_sum]

theorem step_smul (c : ℕ) (S : Finset State) (N : State → ℕ) :
    step S (fun s => c * N s) = fun t => c * step S N t := by
  funext t; unfold step; rw [Finset.mul_sum]

theorem eqMass_congr {S : Finset State} {N N' : State → ℕ} (h : ∀ s ∈ S, N s = N' s) :
    eqMass S N = eqMass S N' :=
  Finset.sum_congr rfl fun s hs => h s (Finset.mem_filter.mp hs).1

/-- `(H1)` and `(C1_r)` read the vector only on the states of the column. -/
theorem H1_congr {S : Finset State} {N N' : State → ℕ} (h : ∀ s ∈ S, N s = N' s)
    {T M B : Finset ℕ} {k : ℕ} (hN : H1 S N T M B k) : H1 S N' T M B k := by
  unfold H1 at hN ⊢
  rwa [total_congr h, step_congr h, eqMass_congr h] at hN

theorem C1r_congr {S : Finset State} {N N' : State → ℕ} (h : ∀ s ∈ S, N s = N' s)
    {T M B : Finset ℕ} {k : ℕ} (hN : C1r S N T M B k) : C1r S N' T M B k := by
  unfold C1r at hN ⊢
  rwa [total_congr h, step_congr h, eqMass_congr h] at hN

/-- `(H1)` is closed under nonnegative combinations. -/
theorem H1_sum {ι : Type*} (I : Finset ι) (c : ι → ℕ) (Ns : ι → State → ℕ) {S : Finset State}
    {T M B : Finset ℕ} {k : ℕ} (h : ∀ i ∈ I, H1 S (Ns i) T M B k) :
    H1 S (fun s => ∑ i ∈ I, c i * Ns i s) T M B k := by
  unfold H1 at h ⊢
  rw [total_sum, eqMass_sum, step_sum, total_sum]
  simp only [total_smul, eqMass_smul, step_smul]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i hi => ?_
  have := h i hi
  nlinarith [Nat.mul_le_mul_left (c i) this]

/-- `(C1_r)` is closed under nonnegative combinations. -/
theorem C1r_sum {ι : Type*} (I : Finset ι) (c : ι → ℕ) (Ns : ι → State → ℕ) {S : Finset State}
    {T M B : Finset ℕ} {k : ℕ} (h : ∀ i ∈ I, C1r S (Ns i) T M B k) :
    C1r S (fun s => ∑ i ∈ I, c i * Ns i s) T M B k := by
  unfold C1r at h ⊢
  rw [total_sum, eqMass_sum, step_sum, total_sum, eqMass_sum]
  simp only [total_smul, eqMass_smul, step_smul]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i hi => ?_
  have := h i hi
  nlinarith [Nat.mul_le_mul_left (c i) this]

/-! ### Path vectors -/

/-- The `d`-step continuations of the state `s₀` of column `j`, by end state. -/
def pathVec (L : Cols) (j : ℕ) (s₀ : State) : ℕ → (State → ℕ)
  | 0 => fun s => if s = s₀ then 1 else 0
  | d + 1 => step (cols L (j + d)) (pathVec L j s₀ d)

@[simp] theorem pathVec_zero (L : Cols) (j : ℕ) (s₀ : State) :
    pathVec L j s₀ 0 = fun s => if s = s₀ then 1 else 0 := rfl
@[simp] theorem pathVec_succ (L : Cols) (j : ℕ) (s₀ : State) (d : ℕ) :
    pathVec L j s₀ (d + 1) = step (cols L (j + d)) (pathVec L j s₀ d) := rfl

/-- The chain vector at column `j + d` is the combination of the path vectors from column `j`,
weighted by the chain vector there. -/
theorem vec_eq_sum_pathVec (L : Cols) (j : ℕ) :
    ∀ d, ∀ s ∈ cols L (j + d), vec L (j + d) s = ∑ s₀ ∈ cols L j, vec L j s₀ * pathVec L j s₀ d s := by
  intro d
  induction d with
  | zero =>
      intro s hs
      simp only [Nat.add_zero, pathVec_zero]
      rw [Finset.sum_eq_single s]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · intro h; exact absurd hs h
  | succ d ih =>
      intro s _
      rw [show j + (d + 1) = (j + d) + 1 from rfl, vec_succ]
      simp only [pathVec_succ]
      unfold step
      rw [Finset.sum_congr rfl (fun s' hs' => ih s' (Finset.mem_filter.mp hs').1)]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s₀ _ => ?_
      rw [Finset.mul_sum]

/-- **The depth-`d` pointwise condition.** For every chain of `k`-list columns, every column
`j` and every state `s₀` there, the path vector of `s₀` satisfies both seam inequalities at the
seam `d` columns later. -/
def DepthOK (k d : ℕ) : Prop :=
  ∀ L : Cols, IsKCols k L → ∀ j, ∀ s₀ ∈ cols L j,
    H1 (cols L (j + d)) (pathVec L j s₀ d) (L (j + d + 1)).1 (L (j + d + 1)).2.1
        (L (j + d + 1)).2.2 k
      ∧ C1r (cols L (j + d)) (pathVec L j s₀ d) (L (j + d + 1)).1 (L (j + d + 1)).2.1
        (L (j + d + 1)).2.2 k

/-- **The short-chain condition.** The first `d` seams of every chain. -/
def ShortOK (k d : ℕ) : Prop := ∀ L : Cols, IsKCols k L → ∀ j, j < d → SeamOK k L j

/-- **Lookback suffices.** -/
theorem allSeamsOK_of_lookback {k d : ℕ} (hd : DepthOK k d) (hs : ShortOK k d) :
    AllSeamsOK k := by
  intro L hL j
  by_cases hj : j < d
  · exact hs L hL j hj
  · obtain ⟨j', rfl⟩ : ∃ j', j = j' + d := ⟨j - d, by omega⟩
    have hdec := vec_eq_sum_pathVec L j' d
    have hcong : ∀ s ∈ cols L (j' + d),
        (fun s => ∑ s₀ ∈ cols L j', vec L j' s₀ * pathVec L j' s₀ d s) s = vec L (j' + d) s :=
      fun s hs' => (hdec s hs').symm
    refine ⟨H1_congr hcong ?_, C1r_congr hcong ?_⟩
    · exact H1_sum (cols L j') (vec L j') (fun s₀ => pathVec L j' s₀ d)
        fun s₀ hs₀ => (hd L hL j' s₀ hs₀).1
    · exact C1r_sum (cols L j') (vec L j') (fun s₀ => pathVec L j' s₀ d)
        fun s₀ hs₀ => (hd L hL j' s₀ hs₀).2

/-- **The theorem, from lookback.** -/
theorem ecc_of_lookback {k d : ℕ} (hk : 3 ≤ k) (hd : DepthOK k d) (hs : ShortOK k d) (n : ℕ) :
    (ListColoring.pathG 2 □ ListColoring.pathG n).ECCAt k :=
  ecc_of_allSeamsOK hk (allSeamsOK_of_lookback hd hs) n

end Grid3
