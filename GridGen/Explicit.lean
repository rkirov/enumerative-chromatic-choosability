/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Main

/-!
# The two-step hypothesis in explicit form

`TwoStep H k` is phrased through path vectors. Unfolded at depth one it is the two-step
inequality of the note, `(2S)_i`: for every state `s₀` of column `j` and every horizon `i`,

  `∑_{s ⊥ s₀} Φ (i+1) s ≤ ∑_{s ⊥ s₀} ∑_{t ⊥ s} Φ i t`,

where `s` ranges over the states of column `j+1` and `t` over those of column `j+2`; and at the
first seam the same with no `s₀`. These are the statements checked numerically in
`ai_research_notes/cx/k3rev/h4/` (`slack.c`, `pairlab.c`, `slacknu.c`), and the ones a proof of
`GeneralHeightConjecture` has to establish.
-/

namespace GridGen

open Finset SimpleGraph ListColoring
open scoped SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- One column on from `s₀`, the path vector is the indicator of compatibility with `s₀`. -/
theorem pathVec_one (L : Cols V) (j : ℕ) {s₀ : State V} (hs₀ : s₀ ∈ cols H L j) :
    pathVec H L j s₀ 1 = fun s => if Compat s₀ s then 1 else 0 := by
  funext s
  simp only [pathVec_succ, pathVec_zero, Nat.add_zero, step]
  simp [Finset.sum_ite_eq', Finset.mem_filter, hs₀]

omit [DecidableEq V] in
/-- Restricting a sum to the states compatible with `s₀`, as an indicator weight. -/
theorem sum_ind_compat (S : Finset (State V)) (s₀ : State V) (f : State V → ℕ) :
    ∑ s ∈ S, (if Compat s₀ s then 1 else 0) * f s = ∑ s ∈ S.filter (Compat s₀), f s := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs <;> simp

/-- **The two-step inequality `(2S)_i`, explicitly.** -/
def TwoStepExplicit (k : ℕ) : Prop :=
  ∀ L : Cols V, IsKCols k L → ∀ j, ∀ s₀ ∈ cols H L j, ∀ i,
    ∑ s ∈ (cols H L (j + 1)).filter (Compat s₀), Φ H k (i + 1) s
      ≤ ∑ s ∈ (cols H L (j + 1)).filter (Compat s₀),
          ∑ t ∈ (cols H L (j + 1 + 1)).filter (Compat s), Φ H k i t

/-- **The first seam, explicitly**: the two-step inequality with no previous state. -/
def FirstSeamExplicit (k : ℕ) : Prop :=
  ∀ L : Cols V, IsKCols k L → ∀ i,
    ∑ s ∈ cols H L 0, Φ H k (i + 1) s
      ≤ ∑ s ∈ cols H L 0, ∑ t ∈ (cols H L 1).filter (Compat s), Φ H k i t

theorem depthOK_one_of_explicit {k : ℕ} (h : TwoStepExplicit H k) : DepthOK H (Φ H k) k 1 := by
  intro L hL j s₀ hs₀ i
  unfold Seam
  rw [pathVec_one H L j hs₀, sum_step_mul, sum_ind_compat, sum_ind_compat]
  exact h L hL j s₀ hs₀ i

theorem shortOK_one_of_explicit {k : ℕ} (h : FirstSeamExplicit H k) : ShortOK H (Φ H k) k 1 := by
  intro L hL j hj i
  obtain rfl : j = 0 := by omega
  unfold Seam
  rw [vec_zero, sum_step_mul]
  simp only [one_mul]
  exact h L hL i

/-- **The two-step hypothesis, from its explicit form.** -/
theorem twoStep_of_explicit {k : ℕ} (h2 : TwoStepExplicit H k) (h1 : FirstSeamExplicit H k) :
    TwoStep H k :=
  ⟨depthOK_one_of_explicit H h2, shortOK_one_of_explicit H h1⟩

/-- **`H □ P_{n+1}` is `k`-ECC from the explicit two-step and initial inequalities.** -/
theorem ecc_of_explicit {k : ℕ} (h2 : TwoStepExplicit H k) (h1 : FirstSeamExplicit H k)
    (hi : Init H k) (n : ℕ) : (H □ pathG n).ECCAt k :=
  ecc_of_twoStep H (twoStep_of_explicit H h2 h1) hi n

end GridGen
