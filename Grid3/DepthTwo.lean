/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Grid3.Column

/-!
# The depth-two interface for the palette-four case

The `k ≥ 5` proof closes the seam inequalities one column back. That condition is genuinely
false at `k = 4`: the exhaustive exact-integer checker in `ai_research_notes/cx/eig/depth_r.c`
finds a `(C1_r)` value of `-1` at depth one. At depth two it finds no negative value (exhaustively
over palette five, with further samples on larger palettes).

This file states that surviving target without any infinite chain or graph bookkeeping.

* `InitialTwoSeamsOK k` is a condition on three columns. It checks the first seam from the
  all-ones vector and the second seam after one transfer.
* `DepthTwoLocalOK k` is a condition on four columns and one state of the first column. It checks
  the last seam after propagating that state across the next two columns.

Together they imply `ECCAt k` for every height-three grid. In particular,
`ecc_grid3_four_of_depthTwo` isolates the two finite set inequalities still needed at `k = 4`.
Neither local predicate is asserted here.
-/

namespace Grid3

open Finset

/-- Both seam inequalities for a vector on one column against the next column. -/
def LocalSeamOK (k : ℕ) (C : ColumnLists) (N : State → ℕ) (D : ColumnLists) : Prop :=
  H1 (columnStates C) N D.1 D.2.1 D.2.2 k ∧
    C1r (columnStates C) N D.1 D.2.1 D.2.2 k

/-- The vector obtained from one starting state after crossing the next two columns. -/
def twoStepVec (C : ColumnLists) (s₀ : State) : State → ℕ :=
  step (columnStates C) (fun s => if Compat s₀ s then 1 else 0)

/-- The first two seams, expressed using only three columns of lists. -/
def InitialTwoSeamsOK (k : ℕ) : Prop :=
  ∀ C₀ C₁ C₂ : ColumnLists,
    IsKColumn k C₀ → IsKColumn k C₁ → IsKColumn k C₂ →
      LocalSeamOK k C₀ (fun _ => 1) C₁ ∧
        LocalSeamOK k C₁ (step (columnStates C₀) (fun _ => 1)) C₂

/-- The depth-two pointwise condition, expressed using only four columns of lists. -/
def DepthTwoLocalOK (k : ℕ) : Prop :=
  ∀ C₀ C₁ C₂ C₃ : ColumnLists,
    IsKColumn k C₀ → IsKColumn k C₁ → IsKColumn k C₂ → IsKColumn k C₃ →
      ∀ s₀ ∈ columnStates C₀, LocalSeamOK k C₂ (twoStepVec C₁ s₀) C₃

/-- The abstract path vector at depth two is exactly the local two-step vector. -/
theorem pathVec_two (L : Cols) (j : ℕ) {s₀ : State} (hs₀ : s₀ ∈ cols L j) :
    pathVec L j s₀ 2 = twoStepVec (L (j + 1)) s₀ := by
  rw [show 2 = 1 + 1 by omega, pathVec_succ]
  unfold twoStepVec cols
  exact step_congr (pathVec_one_compat L j hs₀)

/-- The four-column local condition gives `DepthOK k 2`. -/
theorem depthOK_two_of_local {k : ℕ} (h : DepthTwoLocalOK k) : DepthOK k 2 := by
  intro L hL j s₀ hs₀
  have hlocal := h (L j) (L (j + 1)) (L (j + 2)) (L (j + 3))
    (hL j) (hL (j + 1)) (hL (j + 2)) (hL (j + 3)) s₀
    (by simpa [cols] using hs₀)
  rw [pathVec_two L j hs₀]
  simpa [LocalSeamOK, cols, Nat.add_assoc] using hlocal

/-- The three-column initial condition gives `ShortOK k 2`. -/
theorem shortOK_two_of_initial {k : ℕ} (h : InitialTwoSeamsOK k) : ShortOK k 2 := by
  intro L hL j hj
  obtain ⟨h₀, h₁⟩ := h (L 0) (L 1) (L 2) (hL 0) (hL 1) (hL 2)
  have hj' : j = 0 ∨ j = 1 := by omega
  rcases hj' with rfl | rfl
  · simpa [SeamOK, LocalSeamOK, cols] using h₀
  · simpa [SeamOK, LocalSeamOK, cols] using h₁

/-- The height-three theorem from the exact depth-two local obligations. -/
theorem ecc_of_depthTwoLocalOK {k : ℕ} (hk : 3 ≤ k) (hi : InitialTwoSeamsOK k)
    (hd : DepthTwoLocalOK k) (n : ℕ) :
    (ListColoring.pathG 2 □ ListColoring.pathG n).ECCAt k :=
  ecc_of_lookback hk (depthOK_two_of_local hd) (shortOK_two_of_initial hi) n

/-- **The remaining `k = 4` reduction.** The two explicit local predicates imply every
height-three grid is `ECCAt 4`. -/
theorem ecc_grid3_four_of_depthTwo (hi : InitialTwoSeamsOK 4) (hd : DepthTwoLocalOK 4) (n : ℕ) :
    (ListColoring.pathG 2 □ ListColoring.pathG n).ECCAt 4 :=
  ecc_of_depthTwoLocalOK (by omega) hi hd n

end Grid3

#print axioms Grid3.ecc_grid3_four_of_depthTwo
