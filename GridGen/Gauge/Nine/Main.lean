/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Nine.Bad9
import GridGen.Gauge.Grid

/-!
# Every grid is `9`-ECC

The seam bounds at `k = 9`:
* **star gain** `γ₉ = 2450/449334`, from the refined box bound (`box_bound_nine`);
* **move loss** `ε₉`, from the bad-event bound with 4-cycle weights (`card_bad_le_w`, `W9`).
  The exact shape counts go up to twelve cells, with the `(L-1)3^{L-1}` tail beyond.

They satisfy `(1 - ε₉)² ≥ 1 - γ₉` with a margin of about three percent (`hγε_nine`). The gauge
telescope then gives `rowG m □ P_{n+1}` at `k = 9`, and every rectangle follows.
-/

open Finset SimpleGraph ListColoring
open scoped Classical SimpleGraph

set_option linter.unusedSectionVars false

namespace GridGen.Gauge

variable {c m : ℕ} {P A : Fin m → Finset ℕ}

/-- The move loss at `k = 9`. -/
noncomputable def epsNine : ℚ :=
  ∑ L ∈ range 13, (shapeCount L : ℚ) * (2 / W9 L) +
    2 / (5 * 36) * ((1 / 2 : ℚ) ^ 12 * (12 - 11 * (1 / 2)) / (1 - 1 / 2) ^ 2)

theorem W9_pos (L : ℕ) : 0 < W9 L := by unfold W9; split_ifs <;> positivity

/-- **The path sum at `k = 9`.** -/
theorem sum_le_epsNine (N : ℕ) :
    ∑ L ∈ range (N + 1), (shapeCount L : ℚ) * (2 / W9 L) ≤ epsNine := by
  have hnn : ∀ L, 0 ≤ (shapeCount L : ℚ) * (2 / W9 L) := fun L =>
    mul_nonneg (by positivity) (div_nonneg (by norm_num) (W9_pos L).le)
  calc ∑ L ∈ range (N + 1), (shapeCount L : ℚ) * (2 / W9 L)
      ≤ ∑ L ∈ range (N + 14), (shapeCount L : ℚ) * (2 / W9 L) :=
        sum_le_sum_of_subset_of_nonneg (f := fun L => (shapeCount L : ℚ) * (2 / W9 L))
          (range_subset_range.mpr (by omega)) fun L _ _ => hnn L
    _ = ∑ L ∈ range 13, (shapeCount L : ℚ) * (2 / W9 L) +
          ∑ L ∈ Ico 13 (N + 14), (shapeCount L : ℚ) * (2 / W9 L) := by
        rw [sum_range_add_sum_Ico _ (by omega)]
    _ ≤ ∑ L ∈ range 13, (shapeCount L : ℚ) * (2 / W9 L) +
          2 / (5 * 36) * ∑ n ∈ Ico 12 (N + 13), (n : ℚ) * (1 / 2) ^ n := by
        rw [add_le_add_iff_left, mul_sum]
        have e : ∑ n ∈ Ico 12 (N + 13), 2 / (5 * 36) * ((n : ℚ) * (1 / 2) ^ n)
            = ∑ L ∈ Ico 13 (N + 14), 2 / (5 * 36) * (((L - 1 : ℕ) : ℚ) * (1 / 2) ^ (L - 1)) := by
          rw [← map_add_right_Ico 12 (N + 13) 1, sum_map]
          refine sum_congr rfl fun n _ => ?_
          simp
        rw [e]
        refine sum_le_sum fun L hL => ?_
        rw [mem_Ico] at hL
        have hs := shapeCount_le L
        have hcast : (shapeCount L : ℚ) ≤ ((L - 1 : ℕ) : ℚ) * 3 ^ (L - 1) := by exact_mod_cast hs
        have hw : 2 / W9 L = 2 / (5 * 36) * (1 / 2) ^ (L - 1) / 3 ^ (L - 1) := by
          unfold W9
          rw [if_neg (by omega), show L + 1 = (L - 1) + 2 by omega, pow_add]
          field_simp
          rw [show (6 : ℚ) = 3 * 2 by norm_num, mul_pow]
          have h2 : (1 / 2 : ℚ) ^ (L - 1) * 2 ^ (L - 1) = 1 := by rw [← mul_pow]; norm_num
          linear_combination (-(3 : ℚ) ^ (L - 1) * 36) * h2
        rw [hw]
        calc (shapeCount L : ℚ) * (2 / (5 * 36) * (1 / 2) ^ (L - 1) / 3 ^ (L - 1))
            ≤ (((L - 1 : ℕ) : ℚ) * 3 ^ (L - 1)) * (2 / (5 * 36) * (1 / 2) ^ (L - 1) / 3 ^ (L - 1)) :=
              mul_le_mul_of_nonneg_right hcast (by positivity)
          _ = _ := by field_simp
    _ ≤ epsNine := by
        unfold epsNine
        rw [add_le_add_iff_left]
        refine mul_le_mul_of_nonneg_left (le_of_le_of_eq (geom_sum_le (by norm_num) (by norm_num)
          12 (N + 13) (by omega)) ?_) (by positivity)
        push_cast; ring

/-- `ε₉` in closed form. -/
theorem epsNine_eq : epsNine = 2 / 1260 + 2 * 2 / (5 * 6 ^ 4) + 2 * 4 / (5 * 6 ^ 5) +
    2 * 10 / (5 * 6 ^ 6) + 2 * 31 / (5 * 6 ^ 7) + 2 * 76 / (5 * 6 ^ 8) + 2 * 212 / (5 * 6 ^ 9) +
    2 * 552 / (5 * 6 ^ 10) + 2 * 1607 / (5 * 6 ^ 11) + 2 * 4250 / (5 * 6 ^ 12) +
    2 * 12296 / (5 * 6 ^ 13) + 2 / (5 * 36) * ((1 / 2 : ℚ) ^ 12 * (12 - 11 * (1 / 2)) /
      (1 - 1 / 2) ^ 2) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := shapeCount_small
  unfold epsNine W9
  simp only [sum_range_succ, sum_range_zero, h0, h1, h2, h3, h4, h5, h6, h7,
    shapeCount_eq_cnt 8, shapeCount_eq_cnt 9, shapeCount_eq_cnt 10, shapeCount_eq_cnt 11,
    shapeCount_eq_cnt 12, shapeCnt_8, shapeCnt_9, shapeCnt_10, shapeCnt_11, shapeCnt_12]
  norm_num

/-- The star gain at `k = 9`. -/
def gammaNine : ℚ := 2450 / 449334

theorem hγε_nine : 1 - gammaNine ≤ (1 - epsNine) ^ 2 := by
  rw [epsNine_eq]; unfold gammaNine; norm_num

theorem epsNine_le : epsNine ≤ 1 := by rw [epsNine_eq]; norm_num

theorem epsNine_nonneg : 0 ≤ epsNine := by rw [epsNine_eq]; norm_num

/-! ### The two steps at `k = 9` -/

theorem star_step_nine (hc : 1 ≤ c) (hA : ∀ v, (A v).card = 9) {N : Fin m → ℕ → ℕ}
    (hK : KeyInj 9 A N) (v : Fin m) {a₀ : ℕ} (ha : a₀ ∈ A v) (hx : N v a₀ < 9)
    (hPv : 9 - 1 ≤ (P v).card ∨ a₀ ∉ P v) :
    (Z c m 9 P A N : ℚ) ≤ (1 - gammaNine) * Z c m 9 P A (unpair 9 N v a₀) := by
  have hsplit := card_unpair (k := 9) (P := P) (A := A) N hc v a₀ (N v a₀) rfl
  have hbox := box_bound_nine (P := P) (keyInj_unpair hK v a₀) hA hc v ha hx
    (by simp [unpair]) (by simpa using hPv)
  unfold Z
  have hq := (Nat.cast_le (α := ℚ)).mpr hbox
  push_cast at hq
  have hsplit' : ((slab c m 9 P A (unpair 9 N v a₀)).Ω.card : ℚ) = (slab c m 9 P A N).Ω.card +
      ((slab c m 9 P A (unpair 9 N v a₀)).Ω.filter (Hit hc v a₀ (N v a₀))).card := by
    exact_mod_cast hsplit
  unfold gammaNine
  linarith

theorem move_step_nine (hc : 1 ≤ c) (hA : ∀ v, (A v).card = 9) {M : Fin m → ℕ → ℕ}
    (hK : KeyInj 9 A M) (w : ℕ) {x y : ℕ} (hx : x < 9) (hy : y < 9) :
    (1 - epsNine) * Z c m 9 P A M ≤ Z c m 9 P A (moveKey M w x y) := by
  have hε := epsNine_nonneg
  by_cases hxy : x = y
  · subst hxy
    have : moveKey M w x x = M := by funext v a; simp [moveKey]
    rw [this]
    have : (0 : ℚ) ≤ Z c m 9 P A M := by positivity
    nlinarith
  have hbad := card_bad_le_w (P := P) (hc := hc) (w := w) hK hA hxy hx hy W9 (W9_le hA)
  have hmove := card_le_move_add_bad (P := P) (A := A) (M := M) (hc := hc) (w := w) hx hy
  have hsum := sum_crossPaths_le (m := m) hc w (fun L => 2 / W9 L)
    (fun L => div_nonneg (by norm_num) (W9_pos L).le)
  have hle := sum_le_epsNine (Fintype.card (Cell c m))
  unfold Z
  have hZ : (0 : ℚ) ≤ (slab c m 9 P A M).Ω.card := by positivity
  have hb' : (((slab c m 9 P A M).Ω.filter (Bad hc M w x y)).card : ℚ) ≤
      (slab c m 9 P A M).Ω.card * epsNine :=
    le_trans hbad (mul_le_mul_of_nonneg_left (le_trans hsum hle) hZ)
  have hm' : ((slab c m 9 P A M).Ω.card : ℚ) ≤ (slab c m 9 P A (moveKey M w x y)).Ω.card +
      ((slab c m 9 P A M).Ω.filter (Bad hc M w x y)).card := by exact_mod_cast hmove
  nlinarith

/-- The seam bounds at `k = 9`. -/
noncomputable def slabBounds_nine (hc : 1 ≤ c) (hA : ∀ v, (A v).card = 9) :
    SlabBounds c m 9 P A where
  γ := gammaNine
  ε := epsNine
  hε0 := by linarith [epsNine_le]
  hε1 := by linarith [epsNine_nonneg]
  hγ0 := by unfold gammaNine; norm_num
  hγε := hγε_nine
  star := fun _ hK v _ ha hx hPv => star_step_nine hc hA hK v ha hx hPv
  move := fun _ hK w _ _ hx hy => move_step_nine hc hA hK w hx hy

theorem gaugeBounds_nine : GaugeBounds 9 :=
  fun _ _ _ _ hc hA => ⟨slabBounds_nine hc hA⟩

/-- **`rowG m □ P_{n+1}` is `9`-ECC.** -/
theorem ecc_rowG_boxProd_nine (m n : ℕ) : (rowG m □ pathG n).ECCAt 9 :=
  ecc_rowG_boxProd_of gaugeBounds_nine m n

end GridGen.Gauge

namespace ListColoring

open GridGen.Gauge

/-- **Every rectangular grid is ECC at every list size at least 9.** Both dimensions are
unrestricted; `pathG n` has `n + 1` vertices. For `k ≥ 10` this is the gauge telescope with the
constants of `Seam.lean` (`ecc_rowG_boxProd`); `k = 9` uses the sharper ones above. -/
theorem ecc_boxProd_pathG_of_nine {k : ℕ} (hk : 9 ≤ k) (r n : ℕ) :
    (pathG r □ pathG n).ECCAt k := by
  classical
  rw [SimpleGraph.ecc_iso (boxProdIsoLeft (pathG n) (pathIso r)) k]
  rcases Nat.eq_or_lt_of_le hk with rfl | hk'
  · convert! ecc_rowG_boxProd_nine (r + 1) n
  · convert! ecc_rowG_boxProd hk' (r + 1) n

end ListColoring
