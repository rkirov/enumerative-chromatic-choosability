/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Cacti.Tensor
import Cacti.Induction

/-! Pinning of the arithmetic + residual layer of UM-104, handoff §5.2–§5.3. -/

open Matrix Finset

namespace ListColoring

/-! ### (a) The γ addition law -/

/-- **(a)** `γ_{a+b} = 3 γ_a γ_b + γ_a + γ_b`: the multiplicativity of `3γ_s + 1 = 4^s`,
i.e. the law that lets a cycle transfer product be split into two arcs. -/
theorem gammaPlus_add (a b : ℕ) :
    gammaPlus (a + b) = 3 * gammaPlus a * gammaPlus b + gammaPlus a + gammaPlus b := by
  have ha := three_mul_gammaPlus_add_one a
  have hb := three_mul_gammaPlus_add_one b
  have hab := three_mul_gammaPlus_add_one (a + b)
  rw [pow_add, ← ha, ← hb] at hab
  have h : 3 * gammaPlus (a + b) + 1
      = 3 * (3 * gammaPlus a * gammaPlus b + gammaPlus a + gammaPlus b) + 1 := by
    rw [hab]; ring
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) (Nat.add_right_cancel h)

/-! ### (b) The perturbed transfer matrix `J + P_σ` -/

/-- `J + P_σ` on three colours: weight `2` on the σ-graph, `1` off it.  For `σ = 1` this is
`onesPlus = J + I`. -/
def onesPerm (σ : Equiv.Perm (Fin 3)) : Matrix (Fin 3) (Fin 3) ℕ :=
  Matrix.of fun i j => if j = σ i then 2 else 1

theorem onesPerm_apply (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    onesPerm σ i j = if j = σ i then 2 else 1 := rfl

/-! ### (c) The residual table of §5.3 -/

/-- Residual of an ordinary terminal pair against base `(M, S) = (2T, T)`:
`D = I + P_{σ⁻¹}`, i.e. `D i j = [i = j] + [i = σ j]`. -/
def resOrd (σ : Equiv.Perm (Fin 3)) : Matrix (Fin 3) (Fin 3) ℕ :=
  Matrix.of fun i j => (if i = j then 1 else 0) + (if i = σ j then 1 else 0)

/-- Residual of the closing terminal pair, in aligned coordinates, against the naive base
`(2T, T)`: `D = 2 P_{σ⁻¹}`. -/
def resClose (σ : Equiv.Perm (Fin 3)) : Matrix (Fin 3) (Fin 3) ℕ :=
  Matrix.of fun i j => 2 * (if i = σ j then 1 else 0)

/-- Residual of the closing terminal pair against the **repaired** base `(2T - 2, T)`:
`D = 2 P_{σ⁻¹} + 2 I`. -/
def resCloseRepaired (σ : Equiv.Perm (Fin 3)) : Matrix (Fin 3) (Fin 3) ℕ :=
  Matrix.of fun i j => 2 * (if i = σ j then 1 else 0) + 2 * (if i = j then 1 else 0)

/-- **(c) base/residual split, ordinary edge.**  The exact pair marginal of `U` at an ordinary
terminal pair is `(J + I)(i,j) * (T·J + P_σ)(j,i)` plus the constant-word correction of (5.3);
it splits as base `M = 2T` on the selected matching, `S = T` off it, plus residual `resOrd σ`. -/
theorem pairOrdinary_decomp (T : ℕ) (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    (if i = j then 2 else 1) * (T + (if i = σ j then 1 else 0))
        + (if i = j ∧ σ i ≠ i then 1 else 0)
      = (if i = j then 2 * T else T) + resOrd σ i j := by
  simp only [resOrd, Matrix.of_apply]
  rcases eq_or_ne i j with rfl | h
  · rcases eq_or_ne (σ i) i with hf | hf
    · simp [hf]; omega
    · simp [hf, Ne.symm hf]
  · simp [h]

/-- **(c) base/residual split, closing edge, naive base `(2T, T)`.**  In aligned coordinates the
closing pair marginal is `(if i = j then 2 else 1) * (T + [i = σ j])` plus the correction, now
sitting at `i = σ j`; the residual is `resClose σ = 2 P_{σ⁻¹}`. -/
theorem pairClosing_decomp (T : ℕ) (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    (if i = j then 2 else 1) * (T + (if i = σ j then 1 else 0))
        + (if i = σ j ∧ σ i ≠ i then 1 else 0)
      = (if i = j then 2 * T else T) + resClose σ i j := by
  simp only [resClose, Matrix.of_apply]
  rcases eq_or_ne i j with rfl | h
  · rcases eq_or_ne (σ i) i with hf | hf
    · simp [hf]; omega
    · simp [hf, Ne.symm hf]
  · rcases eq_or_ne i (σ j) with hs | hs
    · have hjj : σ j ≠ j := fun hh => h (hs.trans hh)
      simp [hs, hjj]
    · simp [h, hs]

/-- **Closing pair marginal, aligned coordinates, naive base `(2T, T)`** with `T = γ_s`.
Alignment is the substitution `j ↦ σ j` on the second index, which is why the own-edge factor
`(J + P_σ)(i, σ j)` collapses to `[i = j] ↦ 2` and the correction moves to `i = σ j`. -/
theorem pairClosing_of_transfer (s : ℕ) (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    onesPerm σ i (σ j) * (onesPlus ^ s) (σ j) i + (if i = σ j ∧ σ i ≠ i then 1 else 0)
      = (if i = j then 2 * gammaPlus s else gammaPlus s) + resClose σ i j := by
  have hown : onesPerm σ i (σ j) = if i = j then 2 else 1 := by
    rw [onesPerm_apply]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  have hrest : (onesPlus ^ s) (σ j) i = gammaPlus s + (if i = σ j then 1 else 0) := by
    rw [onesPlus_pow_apply]
    by_cases h : i = σ j
    · simp [h]
    · simp [h, Ne.symm h]
  rw [hown, hrest]
  exact pairClosing_decomp (gammaPlus s) σ i j

end ListColoring
