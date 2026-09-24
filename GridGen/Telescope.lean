/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Column

/-!
# The telescoping bound and the lookback reduction, for any reference

A *reference* `Φ i s` assigns to every state `s` a weight at every horizon `i`, with `Φ 0 = 1`.
The **seam inequality** at horizon `i` says that the `Φ`-weighted mass does not decrease across
a seam:

  `∑_s N s · Φ (i+1) s ≤ ∑_t (step N) t · Φ i t`.

If it holds at every seam of a chain of `n` seams, the total after the chain is at least the
first column's states weighted by `Φ n` (`total_vec_ge_fw`). The seam inequality is linear in
`N`, and the chain vector `d` columns on is a nonnegative combination of *path vectors*, so it
suffices to check it on path vectors (`allSeams_of_lookback`): at depth `1` this is exactly the
two-step inequality of `ai_research_notes/GRID_REVIEW_2026-09-02.md` §5.6.

This is `Grid3.Transfer` and `Grid3.Lookback` with the height-three integer data replaced by an
arbitrary `Φ`; the specific reference — the uniform futures by equality pattern — is in
`GridGen.Uniform`.
-/

open Finset SimpleGraph

namespace GridGen

variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
variable (Φ : ℕ → State V → ℕ)

/-- **The seam inequality** at horizon `i`. -/
def Seam (S : Finset (State V)) (N : State V → ℕ) (T : Lists V) (i : ℕ) : Prop :=
  ∑ s ∈ S, N s * Φ (i + 1) s ≤ ∑ t ∈ states H T, step S N t * Φ i t

/-- The future-weighted mass at column `j` of a chain of `n + 1` columns. -/
def fw (L : Cols V) (n j : ℕ) : ℕ := ∑ s ∈ cols H L j, vec H L j s * Φ (n - j) s

theorem fw_succ_ge (L : Cols V) (n j : ℕ) (hj : j < n)
    (h : Seam H Φ (cols H L j) (vec H L j) (L (j + 1)) (n - (j + 1))) :
    fw H Φ L n j ≤ fw H Φ L n (j + 1) := by
  unfold fw
  have hi : n - j = (n - (j + 1)) + 1 := by omega
  rw [hi, vec_succ]
  exact h

/-- **The telescoping bound.** If every seam satisfies the seam inequality at its horizon, the
total after `n` seams is at least the first column's states weighted by `Φ n`. -/
theorem total_vec_ge_fw (L : Cols V) (n : ℕ) (hΦ : ∀ s, Φ 0 s = 1)
    (h : ∀ j, j < n → Seam H Φ (cols H L j) (vec H L j) (L (j + 1)) (n - (j + 1))) :
    ∑ s ∈ cols H L 0, Φ n s ≤ total (cols H L n) (vec H L n) := by
  have hmono : ∀ j, j ≤ n → fw H Φ L n 0 ≤ fw H Φ L n j := by
    intro j
    induction j with
    | zero => intro _; exact le_rfl
    | succ j ih =>
        intro hj
        exact le_trans (ih (by omega)) (fw_succ_ge H Φ L n j (by omega) (h j (by omega)))
  have h0 : fw H Φ L n 0 = ∑ s ∈ cols H L 0, Φ n s := by
    simp [fw]
  have hn : fw H Φ L n n = total (cols H L n) (vec H L n) := by
    simp [fw, total, hΦ]
  rw [← h0, ← hn]
  exact hmono n le_rfl

/-! ### Linearity -/

theorem Seam_congr {S : Finset (State V)} {N N' : State V → ℕ} (h : ∀ s ∈ S, N s = N' s)
    {T : Lists V} {i : ℕ} (hN : Seam H Φ S N T i) : Seam H Φ S N' T i := by
  unfold Seam at hN ⊢
  have hl : ∑ s ∈ S, N s * Φ (i + 1) s = ∑ s ∈ S, N' s * Φ (i + 1) s :=
    Finset.sum_congr rfl fun s hs => by rw [h s hs]
  rw [hl, step_congr h] at hN
  exact hN

/-- The seam inequality is closed under nonnegative combinations. -/
theorem Seam_sum {ι : Type*} (I : Finset ι) (c : ι → ℕ) (Ns : ι → State V → ℕ)
    {S : Finset (State V)} {T : Lists V} {i : ℕ} (h : ∀ a ∈ I, Seam H Φ S (Ns a) T i) :
    Seam H Φ S (fun s => ∑ a ∈ I, c a * Ns a s) T i := by
  unfold Seam at h ⊢
  rw [step_sum_smul]
  have hl : ∑ s ∈ S, (∑ a ∈ I, c a * Ns a s) * Φ (i + 1) s
      = ∑ a ∈ I, c a * ∑ s ∈ S, Ns a s * Φ (i + 1) s := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_assoc]
  have hr : ∑ t ∈ states H T, (∑ a ∈ I, c a * step S (Ns a) t) * Φ i t
      = ∑ a ∈ I, c a * ∑ t ∈ states H T, step S (Ns a) t * Φ i t := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_assoc]
  rw [hl, hr]
  exact Finset.sum_le_sum fun a ha => Nat.mul_le_mul_left _ (h a ha)

/-! ### Path vectors and lookback -/

/-- The `d`-step continuations of the state `s₀` of column `j`, by end state. -/
def pathVec (L : Cols V) (j : ℕ) (s₀ : State V) : ℕ → (State V → ℕ)
  | 0 => fun s => if s = s₀ then 1 else 0
  | d + 1 => step (cols H L (j + d)) (pathVec L j s₀ d)

@[simp] theorem pathVec_zero (L : Cols V) (j : ℕ) (s₀ : State V) :
    pathVec H L j s₀ 0 = fun s => if s = s₀ then 1 else 0 := rfl
@[simp] theorem pathVec_succ (L : Cols V) (j : ℕ) (s₀ : State V) (d : ℕ) :
    pathVec H L j s₀ (d + 1) = step (cols H L (j + d)) (pathVec H L j s₀ d) := rfl

/-- The chain vector at column `j + d` is the combination of the path vectors from column `j`,
weighted by the chain vector there. -/
theorem vec_eq_sum_pathVec (L : Cols V) (j : ℕ) :
    ∀ d, ∀ s ∈ cols H L (j + d),
      vec H L (j + d) s = ∑ s₀ ∈ cols H L j, vec H L j s₀ * pathVec H L j s₀ d s := by
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
`j`, every state `s₀` there and every horizon, the path vector of `s₀` satisfies the seam
inequality at the seam `d` columns later. At `d = 1` this is the two-step inequality. -/
def DepthOK (k d : ℕ) : Prop :=
  ∀ L : Cols V, IsKCols k L → ∀ j, ∀ s₀ ∈ cols H L j, ∀ i,
    Seam H Φ (cols H L (j + d)) (pathVec H L j s₀ d) (L (j + d + 1)) i

/-- **The short-chain condition.** The first `d` seams of every chain, at every horizon. -/
def ShortOK (k d : ℕ) : Prop :=
  ∀ L : Cols V, IsKCols k L → ∀ j, j < d → ∀ i, Seam H Φ (cols H L j) (vec H L j) (L (j + 1)) i

/-- **Lookback suffices.** -/
theorem allSeams_of_lookback {k d : ℕ} (hd : DepthOK H Φ k d) (hs : ShortOK H Φ k d) :
    ∀ L : Cols V, IsKCols k L → ∀ j i, Seam H Φ (cols H L j) (vec H L j) (L (j + 1)) i := by
  intro L hL j i
  by_cases hj : j < d
  · exact hs L hL j hj i
  · obtain ⟨j', rfl⟩ : ∃ j', j = j' + d := ⟨j - d, by omega⟩
    have hdec := vec_eq_sum_pathVec H L j' d
    have hcong : ∀ s ∈ cols H L (j' + d),
        (fun s => ∑ s₀ ∈ cols H L j', vec H L j' s₀ * pathVec H L j' s₀ d s) s
          = vec H L (j' + d) s :=
      fun s hs' => (hdec s hs').symm
    refine Seam_congr H Φ hcong ?_
    exact Seam_sum H Φ (cols H L j') (vec H L j') (fun s₀ => pathVec H L j' s₀ d)
      fun s₀ hs₀ => hd L hL j' s₀ hs₀ i

end GridGen
