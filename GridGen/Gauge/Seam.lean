/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Labelling

/-!
# The slab inequality at a seam

Moving from the gauge of column `j` to the gauge of column `j + 1` changes the seam keys of the
slab in two phases:

* **Stars.** One unpairing per colour that leaves its row. Each multiplies the count by at least
  `1/(1-γ_k)`: the box bound, `γ_k = (k-4)²(k-5)²/(k²(k-3)⁴)`.
* **Moves.** At most `2H` lower-part transpositions. Each costs at most a factor `1 - ε_k`:
  the Kempe wall lemma with the path bound, `ε_k` explicit (`epsK`).

Since `2ε_k ≤ γ_k` for every `k ≥ 10` (`two_epsK_le_gammaK`), the slab count does not decrease
(`slab_core`).
-/

open Finset
open scoped Classical

set_option linter.unusedSectionVars false

namespace GridGen.Gauge

variable {c m k : ℕ}

/-! ### The constants -/

/-- The star gain `γ_k`. -/
noncomputable def gammaK (k : ℕ) : ℚ := ((k : ℚ) - 4) ^ 2 * ((k : ℚ) - 5) ^ 2 / ((k : ℚ) ^ 2 * ((k : ℚ) - 3) ^ 4)

/-- The weight of a crossing path with `L` cells. -/
noncomputable def pathW (k L : ℕ) : ℚ := 2 / (((k : ℚ) - 3) ^ (L + 1) * ((k : ℚ) - 4))

/-- The move loss `ε_k`: exact shape counts below `8` cells, the `(L-1)3^(L-1)` tail above. -/
noncomputable def epsK (k : ℕ) : ℚ :=
  ∑ L ∈ range 8, (shapeCount L : ℚ) * pathW k L +
    2 / (((k : ℚ) - 4) * ((k : ℚ) - 3) ^ 2) *
      ((3 / ((k : ℚ) - 3)) ^ 7 * (7 - 6 * (3 / ((k : ℚ) - 3))) / (1 - 3 / ((k : ℚ) - 3)) ^ 2)

theorem pathW_nonneg (hk : 5 ≤ k) (L : ℕ) : 0 ≤ pathW k L := by
  unfold pathW
  have : (5 : ℚ) ≤ k := by exact_mod_cast hk
  have h3 : 0 < (k : ℚ) - 3 := by linarith
  have h4 : 0 < (k : ℚ) - 4 := by linarith
  positivity

/-- **The path sum is at most `ε_k`.** -/
theorem sum_le_epsK (hk : 10 ≤ k) (N : ℕ) :
    ∑ L ∈ range (N + 1), (shapeCount L : ℚ) * pathW k L ≤ epsK k := by
  have hk' : (10 : ℚ) ≤ k := by exact_mod_cast hk
  have h3 : 0 < (k : ℚ) - 3 := by linarith
  have h4 : 0 < (k : ℚ) - 4 := by linarith
  set x : ℚ := 3 / ((k : ℚ) - 3) with hxdef
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x < 1 := by rw [hxdef, div_lt_one h3]; linarith
  have hnn : ∀ L, 0 ≤ (shapeCount L : ℚ) * pathW k L := fun L =>
    mul_nonneg (by positivity) (pathW_nonneg (by omega) L)
  -- extend the range, then split at `8`
  calc ∑ L ∈ range (N + 1), (shapeCount L : ℚ) * pathW k L
      ≤ ∑ L ∈ range (N + 9), (shapeCount L : ℚ) * pathW k L :=
        sum_le_sum_of_subset_of_nonneg (f := fun L => (shapeCount L : ℚ) * pathW k L)
          (range_subset_range.mpr (by omega)) fun L _ _ => hnn L
    _ = ∑ L ∈ range 8, (shapeCount L : ℚ) * pathW k L +
          ∑ L ∈ Ico 8 (N + 9), (shapeCount L : ℚ) * pathW k L := by
        rw [sum_range_add_sum_Ico _ (by omega)]
    _ ≤ ∑ L ∈ range 8, (shapeCount L : ℚ) * pathW k L +
          2 / (((k : ℚ) - 4) * ((k : ℚ) - 3) ^ 2) * ∑ n ∈ Ico 7 (N + 8), (n : ℚ) * x ^ n := by
        rw [add_le_add_iff_left, mul_sum]
        have e : ∑ n ∈ Ico 7 (N + 8), 2 / (((k : ℚ) - 4) * ((k : ℚ) - 3) ^ 2) * ((n : ℚ) * x ^ n)
            = ∑ L ∈ Ico 8 (N + 9), 2 / (((k : ℚ) - 4) * ((k : ℚ) - 3) ^ 2) *
                (((L - 1 : ℕ) : ℚ) * x ^ (L - 1)) := by
          rw [← map_add_right_Ico 7 (N + 8) 1, sum_map]
          refine sum_congr rfl fun n _ => ?_
          simp
        rw [e]
        refine sum_le_sum fun L hL => ?_
        rw [mem_Ico] at hL
        have hs := shapeCount_le L
        have hcast : (shapeCount L : ℚ) ≤ ((L - 1 : ℕ) : ℚ) * 3 ^ (L - 1) := by exact_mod_cast hs
        have hw : pathW k L = 2 / (((k : ℚ) - 4) * ((k : ℚ) - 3) ^ 2) *
            (1 / ((k : ℚ) - 3) ^ (L - 1)) := by
          unfold pathW
          rw [show L + 1 = (L - 1) + 2 by omega, pow_add]
          field_simp
        calc (shapeCount L : ℚ) * pathW k L
            ≤ (((L - 1 : ℕ) : ℚ) * 3 ^ (L - 1)) * pathW k L :=
              mul_le_mul_of_nonneg_right hcast (pathW_nonneg (by omega) L)
          _ = _ := by
              rw [hw, hxdef, div_pow]
              field_simp
    _ ≤ epsK k := by
        unfold epsK
        rw [add_le_add_iff_left]
        refine mul_le_mul_of_nonneg_left (le_of_le_of_eq (geom_sum_le hx0 hx1 7 (N + 8)
          (by omega)) ?_) (by positivity)
        rw [hxdef]; push_cast; ring

/-- **The threshold.** For `k ≥ 10` two moves cost less than one star gains. -/
theorem two_epsK_le_gammaK (hk : 10 ≤ k) : 2 * epsK k ≤ gammaK k := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := shapeCount_small
  unfold epsK gammaK pathW
  simp only [sum_range_succ, sum_range_zero, h0, h1, h2, h3, h4, h5, h6, h7]
  have hk' : (10 : ℚ) ≤ k := by exact_mod_cast hk
  obtain ⟨u, hu, hku⟩ : ∃ u : ℚ, 0 ≤ u ∧ (k : ℚ) = u + 10 := ⟨k - 10, by linarith, by ring⟩
  rw [hku]
  rw [← sub_nonneg]
  have hu6 : (0 : ℚ) < u + 6 := by linarith
  have hu4 : (0 : ℚ) < u + 4 := by linarith
  have e : (u + 10 - 4) ^ 2 * (u + 10 - 5) ^ 2 / ((u + 10) ^ 2 * (u + 10 - 3) ^ 4) -
      2 * (0 + ((0 : ℕ) : ℚ) * (2 / ((u + 10 - 3) ^ (0 + 1) * (u + 10 - 4))) +
        ((0 : ℕ) : ℚ) * (2 / ((u + 10 - 3) ^ (1 + 1) * (u + 10 - 4))) +
        ((1 : ℕ) : ℚ) * (2 / ((u + 10 - 3) ^ (2 + 1) * (u + 10 - 4))) +
        ((2 : ℕ) : ℚ) * (2 / ((u + 10 - 3) ^ (3 + 1) * (u + 10 - 4))) +
        ((4 : ℕ) : ℚ) * (2 / ((u + 10 - 3) ^ (4 + 1) * (u + 10 - 4))) +
        ((10 : ℕ) : ℚ) * (2 / ((u + 10 - 3) ^ (5 + 1) * (u + 10 - 4))) +
        ((31 : ℕ) : ℚ) * (2 / ((u + 10 - 3) ^ (6 + 1) * (u + 10 - 4))) +
        ((76 : ℕ) : ℚ) * (2 / ((u + 10 - 3) ^ (7 + 1) * (u + 10 - 4))) +
        2 / ((u + 10 - 4) * (u + 10 - 3) ^ 2) *
          ((3 / (u + 10 - 3)) ^ 7 * (7 - 6 * (3 / (u + 10 - 3))) / (1 - 3 / (u + 10 - 3)) ^ 2))
      = (u ^ 11 + 64 * u ^ 10 + 1851 * u ^ 9 + 31878 * u ^ 8 + 362307 * u ^ 7 +
          2842612 * u ^ 6 + 15622265 * u ^ 5 + 59615274 * u ^ 4 + 152506632 * u ^ 3 +
          241225332 * u ^ 2 + 191704480 * u + 28238000) /
        ((u + 10) ^ 2 * (u + 7) ^ 8 * (u + 6) * (u + 4) ^ 2) := by
    have h7 : (u + 10 - 3) = u + 7 := by ring
    have h6 : (u + 10 - 4) = u + 6 := by ring
    have h5 : (u + 10 - 5) = u + 5 := by ring
    have hu7 : (0 : ℚ) < u + 7 := by linarith
    have hu10 : (0 : ℚ) < u + 10 := by linarith
    have h1 : (1 : ℚ) - 3 / (u + 7) = (u + 4) / (u + 7) := by field_simp; ring
    rw [h7, h6, h5, h1]
    have := hu6.ne'; have := hu4.ne'; have := hu7.ne'; have := hu10.ne'
    field_simp
    ring
  rw [e]
  positivity

end GridGen.Gauge
