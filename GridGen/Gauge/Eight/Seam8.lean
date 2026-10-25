/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Seam
import GridGen.Gauge.Eight.Holes
import GridGen.Gauge.Eight.Bad8
import GridGen.Gauge.Eight.Box8
import GridGen.Gauge.Eight.Counts8
import GridGen.Gauge.Eight.BoxV

/-!
# The seam steps for `k ≥ 8`

The slab inequality of `Core8.lean` needs three steps, collected in `Bounds8 k`:

* **star gain** `γ`: `γ₈ = 5184/960375` at `k = 8` (`box_bound_eight`), the uniform box bound
  `γ_k` (`box_bound`) for `k ≥ 9`;
* **move loss** `ε_k`, for moves through a hole (`card_bad_le_hole`): chain weights
  `(k-2)(k-3)²(k-4)` for two cells, `(k-4)(k-3)^{L+1}` otherwise, two-cell paths counted once.
  The path-shape counts do not depend on `k`, and each weight is at most `(5/(k-3))³` times its
  value at `k = 8` (`wk_le`). So `ε_k = (5/(k-3))³ ε₈` (`epsG`), where `ε₈` uses the exact shape
  counts to eighteen cells (`Eight/Counts8.lean`) and the `(L-1)3^{L-1}` tail beyond;
* **relaxation gain** `γ_V`: `152/27675` at `k = 8` (`boxV_bound`), the uniform vertical box
  bound (`boxV_bound_gen`) for `k ≥ 9`.

`ε ≤ γ` and `ε ≤ γ_V`: at `k = 8` with margins of about `14%` and `16%` (`epsEight_le`), for
`k ≥ 9` by polynomial inequalities in `k - 9` with positive coefficients (`epsG_le_gammaK`,
`epsG_le_gammaVK`); the margins are `39%` and `49%` at `k = 9` and grow like `k`.
-/

open Finset
open scoped Classical

set_option linter.unusedSectionVars false

namespace GridGen.Gauge

variable {c m k : ℕ} {P A : Fin m → Finset ℕ}

/-! ### The move loss at `k = 8` -/

/-- The chain weights at `k = 8`: `600` for two cells, `4 · 5^{L+1}` otherwise. -/
def W8 (L : ℕ) : ℚ := if L = 2 then 600 else 4 * 5 ^ (L + 1)

theorem W8_pos (L : ℕ) : 0 < W8 L := by unfold W8; split_ifs <;> positivity

/-- The per-length weight of the move loss. -/
noncomputable def w8 (L : ℕ) : ℚ := (if L = 2 then 1 else 2) / W8 L

theorem w8_nonneg (L : ℕ) : 0 ≤ w8 L := by
  unfold w8; exact div_nonneg (by split_ifs <;> norm_num) (W8_pos L).le

/-- The move loss at `k = 8`. -/
noncomputable def epsEight : ℚ :=
  ∑ L ∈ range 19, (shapeCount L : ℚ) * w8 L +
    2 / (4 * 25) * ((3 / 5 : ℚ) ^ 18 * (18 - 17 * (3 / 5)) / (1 - 3 / 5) ^ 2)

/-- **The path sum at `k = 8`.** -/
theorem sum_le_epsEight (N : ℕ) :
    ∑ L ∈ range (N + 1), (shapeCount L : ℚ) * w8 L ≤ epsEight := by
  have hnn : ∀ L, 0 ≤ (shapeCount L : ℚ) * w8 L := fun L =>
    mul_nonneg (by positivity) (w8_nonneg L)
  calc ∑ L ∈ range (N + 1), (shapeCount L : ℚ) * w8 L
      ≤ ∑ L ∈ range (N + 20), (shapeCount L : ℚ) * w8 L :=
        sum_le_sum_of_subset_of_nonneg (f := fun L => (shapeCount L : ℚ) * w8 L)
          (range_subset_range.mpr (by omega)) fun L _ _ => hnn L
    _ = ∑ L ∈ range 19, (shapeCount L : ℚ) * w8 L +
          ∑ L ∈ Ico 19 (N + 20), (shapeCount L : ℚ) * w8 L := by
        rw [sum_range_add_sum_Ico _ (by omega)]
    _ ≤ ∑ L ∈ range 19, (shapeCount L : ℚ) * w8 L +
          2 / (4 * 25) * ∑ n ∈ Ico 18 (N + 19), (n : ℚ) * (3 / 5) ^ n := by
        rw [add_le_add_iff_left, mul_sum]
        have e : ∑ n ∈ Ico 18 (N + 19), 2 / (4 * 25) * ((n : ℚ) * (3 / 5) ^ n)
            = ∑ L ∈ Ico 19 (N + 20), 2 / (4 * 25) * (((L - 1 : ℕ) : ℚ) * (3 / 5) ^ (L - 1)) := by
          rw [← map_add_right_Ico 18 (N + 19) 1, sum_map]
          refine sum_congr rfl fun n _ => ?_
          simp
        rw [e]
        refine sum_le_sum fun L hL => ?_
        rw [mem_Ico] at hL
        have hs := shapeCount_le L
        have hcast : (shapeCount L : ℚ) ≤ ((L - 1 : ℕ) : ℚ) * 3 ^ (L - 1) := by exact_mod_cast hs
        have hw : w8 L = 2 / (4 * 25) * (3 / 5) ^ (L - 1) / 3 ^ (L - 1) := by
          unfold w8 W8
          rw [ite_eq_right (by omega), ite_eq_right (by omega), show L + 1 = (L - 1) + 2 by omega, pow_add]
          rw [div_pow]
          field_simp
          ring
        rw [hw]
        calc (shapeCount L : ℚ) * (2 / (4 * 25) * (3 / 5) ^ (L - 1) / 3 ^ (L - 1))
            ≤ (((L - 1 : ℕ) : ℚ) * 3 ^ (L - 1)) * (2 / (4 * 25) * (3 / 5) ^ (L - 1) / 3 ^ (L - 1)) :=
              mul_le_mul_of_nonneg_right hcast (by positivity)
          _ = _ := by field_simp
    _ ≤ epsEight := by
        unfold epsEight
        rw [add_le_add_iff_left]
        refine mul_le_mul_of_nonneg_left (le_of_le_of_eq (geom_sum_le (by norm_num) (by norm_num)
          18 (N + 19) (by omega)) ?_) (by positivity)
        push_cast; ring

/-- `ε₈` in closed form. -/
theorem epsEight_eq : epsEight = 1 / 600 + 2 * 2 / (4 * 5 ^ 4) + 2 * 4 / (4 * 5 ^ 5) +
    2 * 10 / (4 * 5 ^ 6) + 2 * 31 / (4 * 5 ^ 7) + 2 * 76 / (4 * 5 ^ 8) + 2 * 212 / (4 * 5 ^ 9) +
    2 * 552 / (4 * 5 ^ 10) + 2 * 1607 / (4 * 5 ^ 11) + 2 * 4250 / (4 * 5 ^ 12) +
    2 * 12296 / (4 * 5 ^ 13) + 2 * 33190 / (4 * 5 ^ 14) + 2 * 96757 / (4 * 5 ^ 15) +
    2 * 264376 / (4 * 5 ^ 16) + 2 * 772192 / (4 * 5 ^ 17) + 2 * 2132440 / (4 * 5 ^ 18) +
    2 * 6246601 / (4 * 5 ^ 19) +
    2 / (4 * 25) * ((3 / 5 : ℚ) ^ 18 * (18 - 17 * (3 / 5)) / (1 - 3 / 5) ^ 2) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := shapeCount_small
  obtain ⟨h8, h9, h10, h11, h12⟩ := shapeCnt_8_12
  obtain ⟨h13, h14, h15, h16, h17, h18⟩ := shapeCnt_13_18
  unfold epsEight w8 W8
  simp only [sum_range_succ, sum_range_zero, h0, h1, h2, h3, h4, h5, h6, h7,
    shapeCount_eq_cnt 8, shapeCount_eq_cnt 9, shapeCount_eq_cnt 10, shapeCount_eq_cnt 11,
    shapeCount_eq_cnt 12, shapeCount_eq_cnt 13, shapeCount_eq_cnt 14, shapeCount_eq_cnt 15,
    shapeCount_eq_cnt 16, shapeCount_eq_cnt 17, shapeCount_eq_cnt 18, h8, h9,
    h10, h11, h12, h13, h14, h15, h16, h17, h18]
  norm_num

/-- The star gain at `k = 8`. -/
def gammaEight : ℚ := 5184 / 960375

/-- The relaxation gain at `k = 8`. -/
def gammaV : ℚ := 152 / 27675

theorem epsEight_le : epsEight ≤ gammaEight ∧ epsEight ≤ gammaV := by
  rw [epsEight_eq]; unfold gammaEight gammaV; constructor <;> norm_num

theorem epsEight_nonneg : 0 ≤ epsEight := by rw [epsEight_eq]; norm_num

/-! ### The steps at `k = 8` -/

/-- **A star step at `k = 8`.** -/
theorem star_step8 (hc : 1 ≤ c) (hA : ∀ v, (A v).card = 8) {N : Fin m → ℕ → ℕ}
    (hK : KeyInj 8 A N) (v : Fin m) {a₀ : ℕ} (ha : a₀ ∈ A v) (hx : N v a₀ < 8)
    (hPv : 8 - 1 ≤ (P v).card ∨ a₀ ∉ P v) :
    (Z c m 8 P A N : ℚ) ≤ (1 - gammaEight) * Z c m 8 P A (unpair 8 N v a₀) := by
  have hsplit := card_unpair (k := 8) (P := P) (A := A) N hc v a₀ (N v a₀) rfl
  have hbox := box_bound_eight (P := P) (keyInj_unpair hK v a₀) hA hc v ha hx
    (by simp [unpair]) (by simpa using hPv)
  unfold Z
  have hq := (Nat.cast_le (α := ℚ)).mpr hbox
  push_cast at hq
  have hsplit' : ((slab c m 8 P A (unpair 8 N v a₀)).Ω.card : ℚ) = (slab c m 8 P A N).Ω.card +
      ((slab c m 8 P A (unpair 8 N v a₀)).Ω.filter (Hit hc v a₀ (N v a₀))).card := by
    exact_mod_cast hsplit
  unfold gammaEight
  linarith

/-- **A relaxation step at `k = 8`.** -/
theorem relax_step8 (hc : 1 ≤ c) (hA : ∀ v, (A v).card = 8) {M : Fin m → ℕ → ℕ}
    (hK : KeyInj 8 A M) {R : Fin m → Finset ℕ} {v : Fin m} (hv : v.val + 1 < m) {ℓ : ℕ}
    (hℓ : ℓ < 8) (hn : ℓ ∉ R v) :
    ((slabR c m 8 P A M R).Ω.card : ℚ) ≤ (1 - gammaV) * (slabR c m 8 P A M (Radd R v ℓ)).Ω.card := by
  have hsplit := card_relax (k := 8) (P := P) (A := A) (M := M) hc hv hn
  have hmem : ℓ ∈ Radd R v ℓ v := by simp [Radd]
  have hbox := boxV_bound (P := P) hK hc hv hA hℓ hmem
  have hq := (Nat.cast_le (α := ℚ)).mpr hbox
  push_cast at hq
  have hsplit' : ((slabR c m 8 P A M (Radd R v ℓ)).Ω.card : ℚ) = (slabR c m 8 P A M R).Ω.card +
      ((slabR c m 8 P A M (Radd R v ℓ)).Ω.filter (HitV hc hv ℓ)).card := by exact_mod_cast hsplit
  unfold gammaV
  linarith

/-- The relaxation sets of a set of (row, label) pairs. -/
def RT (T : Finset (Fin m × ℕ)) : Fin m → Finset ℕ := fun v => (T.filter (·.1 = v)).image Prod.snd

theorem mem_RT {T : Finset (Fin m × ℕ)} {v : Fin m} {ℓ : ℕ} : ℓ ∈ RT T v ↔ (v, ℓ) ∈ T := by
  simp only [RT, mem_image, mem_filter]
  constructor
  · rintro ⟨q, ⟨hq, rfl⟩, rfl⟩; exact hq
  · intro h; exact ⟨(v, ℓ), ⟨h, rfl⟩, rfl⟩

/-! ### The move loss at every `k ≥ 8` -/

/-- The chain weights: `(k-2)(k-3)²(k-4)` for two cells, `(k-3)^{L+1}(k-4)` otherwise. -/
noncomputable def Wk (k L : ℕ) : ℚ :=
  if L = 2 then ((k : ℚ) - 2) * (((k : ℚ) - 3) ^ 2 * ((k : ℚ) - 4))
  else ((k : ℚ) - 3) ^ (L + 1) * ((k : ℚ) - 4)

theorem Wk_pos (hk : 5 ≤ k) (L : ℕ) : 0 < Wk k L := by
  have hk' : (5 : ℚ) ≤ k := by exact_mod_cast hk
  have h2 : 0 < (k : ℚ) - 2 := by linarith
  have h3 : 0 < (k : ℚ) - 3 := by linarith
  have h4 : 0 < (k : ℚ) - 4 := by linarith
  unfold Wk; split_ifs <;> positivity

theorem Wk_le {M : Fin m → ℕ → ℕ} {hc : 1 ≤ c} {w : ℕ} (hk : 5 ≤ k)
    (hA : ∀ v, (A v).card = k) :
    ∀ l ∈ crossPaths (m := m) hc w,
      0 < Wk k l.length ∧ Wk k l.length ≤ (slab c m k P A M).chainProd (chainOf l) := by
  intro l hl
  have hl' : CrossPath hc w l := (mem_filter.mp hl).2
  refine ⟨Wk_pos hk _, ?_⟩
  unfold Wk
  split_ifs with h2
  · have := chainProd_two (P := P) (M := M) (by omega) hA hl' h2
    have hq := (Nat.cast_le (α := ℚ)).mpr this
    push_cast [Nat.cast_sub (show 2 ≤ k by omega), Nat.cast_sub (show 3 ≤ k by omega),
      Nat.cast_sub (show 4 ≤ k by omega)] at hq
    exact hq
  · obtain ⟨hne, hnd, hch, hlen, hcol⟩ := chainOf_props hl'
    have hD : ∀ z ∈ chainOf l, ((slab c m k P A M).D z).card = k := by
      intro z hz
      by_cases h1 : z.1.val = 1
      · rw [slab_D_one h1, hA]
      · rw [slab_D_fut (by have := hcol z hz; omega), card_range]
    have hge := chainProd_ge (P := P) (A := A) (M := M) (by omega) (chainOf l) hne hnd hch hD
    rw [hlen, show l.length + 2 - 1 = l.length + 1 by omega] at hge
    have hq := (Nat.cast_le (α := ℚ)).mpr hge
    push_cast [Nat.cast_sub (show 3 ≤ k by omega), Nat.cast_sub (show 4 ≤ k by omega)] at hq
    exact hq

/-- The per-length weight of the move loss. -/
noncomputable def wk (k L : ℕ) : ℚ := (if L = 2 then 1 else 2) / Wk k L

theorem wk_nonneg (hk : 5 ≤ k) (L : ℕ) : 0 ≤ wk k L := by
  unfold wk; exact div_nonneg (by split_ifs <;> norm_num) (Wk_pos hk L).le

/-- **The weights scale with `k`.** Each per-length weight at `k ≥ 8` is at most `(5/(k-3))³`
times its value at `k = 8`. -/
theorem wk_le (hk : 8 ≤ k) {L : ℕ} (hL : 2 ≤ L) :
    wk k L ≤ (5 / ((k : ℚ) - 3)) ^ 3 * w8 L := by
  have hk' : (8 : ℚ) ≤ k := by exact_mod_cast hk
  set y : ℚ := (k : ℚ) - 3 with hy
  have hy5 : 5 ≤ y := by rw [hy]; linarith
  have hy0 : 0 < y := by linarith
  have e2 : (k : ℚ) - 2 = y + 1 := by rw [hy]; ring
  have e4 : (k : ℚ) - 4 = y - 1 := by rw [hy]; ring
  unfold wk Wk w8 W8
  by_cases h2 : L = 2
  · subst h2
    simp only [ite_true]
    rw [e2, e4]
    have hrhs : (5 / y) ^ 3 * (1 / 600) = 5 / (24 * y ^ 3) := by field_simp; ring
    have hy1 : 0 < y - 1 := by linarith
    rw [hrhs, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 ≤ y ^ 2 * (5 * y + 1) * (y - 5) :=
      mul_nonneg (mul_nonneg (sq_nonneg y) (by linarith)) (by linarith)
    nlinarith
  · rw [ite_eq_right h2, ite_eq_right h2, ite_eq_right h2]
    obtain ⟨n, rfl⟩ : ∃ n, L = n + 3 := ⟨L - 3, by omega⟩
    rw [e4]
    have hrhs : (5 / y) ^ 3 * (2 / (4 * 5 ^ (n + 3 + 1))) = 2 / (4 * 5 ^ (n + 1) * y ^ 3) := by
      field_simp; ring
    rw [hrhs, div_le_div_iff₀ (mul_pos (pow_pos hy0 _) (by linarith)) (by positivity)]
    have h5 : (5 : ℚ) ^ (n + 1) ≤ y ^ (n + 1) := pow_le_pow_left₀ (by norm_num) hy5 _
    have e : y ^ (n + 3 + 1) * (y - 1) = y ^ (n + 1) * (y - 1) * y ^ 3 := by ring
    rw [e]
    have h4 : 4 * (5 : ℚ) ^ (n + 1) ≤ y ^ (n + 1) * (y - 1) := by
      have := mul_le_mul h5 (show (4 : ℚ) ≤ y - 1 by linarith) (by norm_num) (by positivity)
      linarith
    have := mul_le_mul_of_nonneg_right h4 (pow_nonneg hy0.le 3)
    nlinarith

/-- The move loss at `k ≥ 8`. -/
noncomputable def epsG (k : ℕ) : ℚ := (5 / ((k : ℚ) - 3)) ^ 3 * epsEight

theorem epsG_eight : epsG 8 = epsEight := by unfold epsG; norm_num

theorem epsG_nonneg (hk : 4 ≤ k) : 0 ≤ epsG k := by
  have hk' : (4 : ℚ) ≤ k := by exact_mod_cast hk
  have h3 : 0 < (k : ℚ) - 3 := by linarith
  unfold epsG; exact mul_nonneg (by positivity) epsEight_nonneg

/-- **The path sum at `k ≥ 8`.** -/
theorem sum_le_epsG (hk : 8 ≤ k) (N : ℕ) :
    ∑ L ∈ range (N + 1), (shapeCount L : ℚ) * wk k L ≤ epsG k := by
  have hk' : (8 : ℚ) ≤ k := by exact_mod_cast hk
  have h3 : 0 < (k : ℚ) - 3 := by linarith
  have hc0 : 0 ≤ (5 / ((k : ℚ) - 3)) ^ 3 := by positivity
  obtain ⟨h0, h1, -⟩ := shapeCount_small
  calc ∑ L ∈ range (N + 1), (shapeCount L : ℚ) * wk k L
      ≤ ∑ L ∈ range (N + 1), (5 / ((k : ℚ) - 3)) ^ 3 * ((shapeCount L : ℚ) * w8 L) := by
        refine sum_le_sum fun L _ => ?_
        by_cases hL : 2 ≤ L
        · rw [mul_left_comm]
          exact mul_le_mul_of_nonneg_left (wk_le hk hL) (Nat.cast_nonneg _)
        · interval_cases L <;> simp [h0, h1]
    _ = (5 / ((k : ℚ) - 3)) ^ 3 * ∑ L ∈ range (N + 1), (shapeCount L : ℚ) * w8 L := by
        rw [mul_sum]
    _ ≤ epsG k := mul_le_mul_of_nonneg_left (sum_le_epsEight N) hc0

/-- **A move step through a hole at `k ≥ 8`.** -/
theorem move_stepG (hk : 8 ≤ k) (hc : 1 ≤ c) (hA : ∀ v, (A v).card = k) {M : Fin m → ℕ → ℕ}
    (hK : KeyInj k A M) (w : ℕ) {x y : ℕ} (hx : x < k) (hy : y < k) (hh : HoleAt A M w x y) :
    (1 - epsG k) * Z c m k P A M ≤ Z c m k P A (moveKey M w x y) := by
  have hε := epsG_nonneg (show 4 ≤ k by omega)
  by_cases hxy : x = y
  · subst hxy
    have : moveKey M w x x = M := by funext v a; simp [moveKey]
    rw [this]
    have : (0 : ℚ) ≤ Z c m k P A M := by positivity
    nlinarith
  have hbad := card_bad_le_hole (P := P) (hc := hc) (w := w) hK hxy hx hy hh (Wk k)
    (Wk_le (by omega) hA)
  have hmove := card_le_move_add_bad (P := P) (A := A) (M := M) (hc := hc) (w := w) hx hy
  have hsum := sum_crossPaths_le (m := m) hc w (wk k) (wk_nonneg (by omega))
  have hle := sum_le_epsG hk (Fintype.card (Cell c m))
  unfold Z
  have hZ : (0 : ℚ) ≤ (slab c m k P A M).Ω.card := by positivity
  have hb' : (((slab c m k P A M).Ω.filter (Bad hc M w x y)).card : ℚ) ≤
      (slab c m k P A M).Ω.card * epsG k :=
    le_trans hbad (mul_le_mul_of_nonneg_left (le_trans hsum hle) hZ)
  have hm' : ((slab c m k P A M).Ω.card : ℚ) ≤ (slab c m k P A (moveKey M w x y)).Ω.card +
      ((slab c m k P A M).Ω.filter (Bad hc M w x y)).card := by exact_mod_cast hmove
  nlinarith

/-! ### The relaxation gain at every `k ≥ 9` -/

/-- The relaxation gain of the uniform vertical box. -/
noncomputable def gammaVK (k : ℕ) : ℚ :=
  ((k : ℚ) - 4) ^ 2 * (((k : ℚ) - 3) ^ 2 - ((k : ℚ) - 2)) ^ 2 /
    ((k : ℚ) ^ 2 * ((k : ℚ) - 3) ^ 2 * (((k : ℚ) - 2) * ((k : ℚ) - 3)) ^ 2)

/-- **A relaxation step at `k ≥ 9`.** -/
theorem relax_stepK (hk : 9 ≤ k) (hc : 1 ≤ c) (hA : ∀ v, (A v).card = k) {M : Fin m → ℕ → ℕ}
    (hK : KeyInj k A M) {R : Fin m → Finset ℕ} {v : Fin m} (hv : v.val + 1 < m) {ℓ : ℕ}
    (hℓ : ℓ < k) (hn : ℓ ∉ R v) :
    ((slabR c m k P A M R).Ω.card : ℚ) ≤ (1 - gammaVK k) * (slabR c m k P A M (Radd R v ℓ)).Ω.card := by
  have hsplit := card_relax (k := k) (P := P) (A := A) (M := M) hc hv hn
  have hmem : ℓ ∈ Radd R v ℓ v := by simp [Radd]
  have hbox := boxV_bound_gen (P := P) hK hc hv (by omega) hA hℓ hmem
  have hsq : k - 2 ≤ (k - 3) ^ 2 := by
    obtain ⟨t, rfl⟩ : ∃ t, k = 9 + t := ⟨k - 9, by omega⟩
    rw [show 9 + t - 2 = 7 + t by omega, show 9 + t - 3 = 6 + t by omega]; nlinarith
  have hq := (Nat.cast_le (α := ℚ)).mpr hbox
  push_cast [Nat.cast_sub hsq, Nat.cast_sub (show 2 ≤ k by omega), Nat.cast_sub (show 3 ≤ k by omega),
    Nat.cast_sub (show 4 ≤ k by omega)] at hq
  have hsplit' : ((slabR c m k P A M (Radd R v ℓ)).Ω.card : ℚ) = (slabR c m k P A M R).Ω.card +
      ((slabR c m k P A M (Radd R v ℓ)).Ω.filter (HitV hc hv ℓ)).card := by exact_mod_cast hsplit
  have hk' : (9 : ℚ) ≤ k := by exact_mod_cast hk
  have hden : 0 < (k : ℚ) ^ 2 * ((k : ℚ) - 3) ^ 2 * (((k : ℚ) - 2) * ((k : ℚ) - 3)) ^ 2 := by
    have : 0 < (k : ℚ) - 3 := by linarith
    have : 0 < (k : ℚ) - 2 := by linarith
    positivity
  have hγ : gammaVK k * (slabR c m k P A M (Radd R v ℓ)).Ω.card ≤
      ((slabR c m k P A M (Radd R v ℓ)).Ω.filter (HitV hc hv ℓ)).card := by
    unfold gammaVK
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    linarith
  linarith

/-! ### The constants at `k ≥ 9` -/

theorem epsEight_le_bound : epsEight ≤ 3 / 625 := by rw [epsEight_eq]; norm_num

theorem epsG_le_bound (hk : 9 ≤ k) : epsG k ≤ 3 / (5 * ((k : ℚ) - 3) ^ 3) := by
  have hk' : (9 : ℚ) ≤ k := by exact_mod_cast hk
  have h3 : 0 < (k : ℚ) - 3 := by linarith
  unfold epsG
  calc (5 / ((k : ℚ) - 3)) ^ 3 * epsEight ≤ (5 / ((k : ℚ) - 3)) ^ 3 * (3 / 625) :=
        mul_le_mul_of_nonneg_left epsEight_le_bound (by positivity)
    _ = 3 / (5 * ((k : ℚ) - 3) ^ 3) := by field_simp; ring

theorem epsG_le_gammaK (hk : 9 ≤ k) : epsG k ≤ gammaK k := by
  have hk' : (9 : ℚ) ≤ k := by exact_mod_cast hk
  refine le_trans (epsG_le_bound hk) ?_
  unfold gammaK
  set x : ℚ := (k : ℚ) with hx
  have h3 : 0 < x - 3 := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  set u := x - 9 with hu
  have hu0 : 0 ≤ u := by linarith
  have hp : 0 ≤ 5 * (x - 4) ^ 2 * (x - 5) ^ 2 - 3 * x ^ 2 * (x - 3) := by
    have e : 5 * (x - 4) ^ 2 * (x - 5) ^ 2 - 3 * x ^ 2 * (x - 3) =
        5 * u ^ 4 + 87 * u ^ 3 + 533 * u ^ 2 + 1233 * u + 542 := by rw [hu]; ring
    rw [e]; positivity
  have := mul_nonneg (pow_nonneg h3.le 3) hp
  nlinarith

theorem epsG_le_gammaVK (hk : 9 ≤ k) : epsG k ≤ gammaVK k := by
  have hk' : (9 : ℚ) ≤ k := by exact_mod_cast hk
  refine le_trans (epsG_le_bound hk) ?_
  unfold gammaVK
  set x : ℚ := (k : ℚ) with hx
  have h3 : 0 < x - 3 := by linarith
  have h2 : 0 < x - 2 := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  set u := x - 9 with hu
  have hu0 : 0 ≤ u := by linarith
  have hp : 0 ≤ 5 * (x - 4) ^ 2 * ((x - 3) ^ 2 - (x - 2)) ^ 2 - 3 * x ^ 2 * (x - 2) ^ 2 * (x - 3) := by
    have e : 5 * (x - 4) ^ 2 * ((x - 3) ^ 2 - (x - 2)) ^ 2 - 3 * x ^ 2 * (x - 2) ^ 2 * (x - 3) =
        5 * u ^ 6 + 157 * u ^ 5 + 2006 * u ^ 4 + 13168 * u ^ 3 + 45556 * u ^ 2 + 73605 * u +
          33683 := by rw [hu]; ring
    rw [e]; positivity
  have := mul_nonneg (pow_nonneg h3.le 3) hp
  nlinarith

theorem gammaK_lt_one (hk : 9 ≤ k) : gammaK k < 1 := by
  unfold gammaK
  have hk' : (9 : ℚ) ≤ k := by exact_mod_cast hk
  have h3 : 0 < (k : ℚ) - 3 := by linarith
  rw [div_lt_one (by positivity)]
  have h1 : ((k : ℚ) - 4) ^ 2 < (k : ℚ) ^ 2 := by nlinarith
  have h2 : ((k : ℚ) - 5) ^ 2 ≤ ((k : ℚ) - 3) ^ 4 := by nlinarith
  exact mul_lt_mul h1 h2 (by nlinarith) (by positivity)

theorem gammaVK_le_one (hk : 9 ≤ k) : gammaVK k ≤ 1 := by
  unfold gammaVK
  have hk' : (9 : ℚ) ≤ k := by exact_mod_cast hk
  have h3 : 0 < (k : ℚ) - 3 := by linarith
  have h2 : 0 < (k : ℚ) - 2 := by linarith
  rw [div_le_one (by positivity)]
  have e1 : ((k : ℚ) - 4) ^ 2 ≤ (k : ℚ) ^ 2 * ((k : ℚ) - 3) ^ 2 := by nlinarith
  have e2 : (((k : ℚ) - 3) ^ 2 - ((k : ℚ) - 2)) ^ 2 ≤ (((k : ℚ) - 2) * ((k : ℚ) - 3)) ^ 2 := by
    have : 0 ≤ ((k : ℚ) - 3) ^ 2 - ((k : ℚ) - 2) := by nlinarith
    exact pow_le_pow_left₀ this (by nlinarith) 2
  calc ((k : ℚ) - 4) ^ 2 * (((k : ℚ) - 3) ^ 2 - ((k : ℚ) - 2)) ^ 2
      ≤ ((k : ℚ) ^ 2 * ((k : ℚ) - 3) ^ 2) * (((k : ℚ) - 2) * ((k : ℚ) - 3)) ^ 2 :=
        mul_le_mul e1 e2 (by positivity) (by positivity)
    _ = _ := by ring

/-! ### The seam bounds -/

/-- **Seam bounds at `k`.** A star gain `γ`, a move loss `ε` for moves through holes and a
relaxation gain `γ_V`, with `ε ≤ γ` and `ε ≤ γ_V`. -/
structure Bounds8 (k : ℕ) where
  hk : 8 ≤ k
  /-- The star gain. -/
  γ : ℚ
  /-- The move loss. -/
  ε : ℚ
  /-- The relaxation gain. -/
  γV : ℚ
  hε0 : 0 ≤ ε
  hεγ : ε ≤ γ
  hεV : ε ≤ γV
  hγ1 : γ < 1
  hV1 : γV ≤ 1
  star : ∀ {c m : ℕ} {P A : Fin m → Finset ℕ} {N : Fin m → ℕ → ℕ}, 1 ≤ c →
    (∀ v, (A v).card = k) → KeyInj k A N → ∀ (v : Fin m) {a₀ : ℕ}, a₀ ∈ A v → N v a₀ < k →
      (k - 1 ≤ (P v).card ∨ a₀ ∉ P v) →
        (Z c m k P A N : ℚ) ≤ (1 - γ) * Z c m k P A (unpair k N v a₀)
  move : ∀ {c m : ℕ} {P A : Fin m → Finset ℕ} {M : Fin m → ℕ → ℕ}, 1 ≤ c →
    (∀ v, (A v).card = k) → KeyInj k A M → ∀ (w : ℕ) {x y : ℕ}, x < k → y < k →
      HoleAt A M w x y → (1 - ε) * Z c m k P A M ≤ Z c m k P A (moveKey M w x y)
  relax : ∀ {c m : ℕ} {P A : Fin m → Finset ℕ} {M : Fin m → ℕ → ℕ} {R : Fin m → Finset ℕ}
    {v : Fin m}, 1 ≤ c → (∀ v, (A v).card = k) → KeyInj k A M → v.val + 1 < m → ∀ {ℓ : ℕ},
      ℓ < k → ℓ ∉ R v →
        ((slabR c m k P A M R).Ω.card : ℚ) ≤ (1 - γV) * (slabR c m k P A M (Radd R v ℓ)).Ω.card

/-- **The bounds at `k = 8`.** -/
noncomputable def bounds_eight : Bounds8 8 where
  hk := le_rfl
  γ := gammaEight
  ε := epsG 8
  γV := gammaV
  hε0 := epsG_nonneg (by norm_num)
  hεγ := by rw [epsG_eight]; exact epsEight_le.1
  hεV := by rw [epsG_eight]; exact epsEight_le.2
  hγ1 := by unfold gammaEight; norm_num
  hV1 := by unfold gammaV; norm_num
  star := fun hc hA hK v _ ha hx hP => star_step8 hc hA hK v ha hx hP
  move := fun hc hA hK w _ _ hx hy hh => move_stepG le_rfl hc hA hK w hx hy hh
  relax := fun hc hA hK hv _ hℓ hn => relax_step8 hc hA hK hv hℓ hn

/-- **The bounds at `k ≥ 9`.** -/
noncomputable def bounds_ge9 (hk : 9 ≤ k) : Bounds8 k where
  hk := by omega
  γ := gammaK k
  ε := epsG k
  γV := gammaVK k
  hε0 := epsG_nonneg (by omega)
  hεγ := epsG_le_gammaK hk
  hεV := epsG_le_gammaVK hk
  hγ1 := gammaK_lt_one hk
  hV1 := gammaVK_le_one hk
  star := fun hc hA hK v _ ha hx hP => star_step (by omega) hc hA hK v ha hx hP
  move := fun hc hA hK w _ _ hx hy hh => move_stepG (by omega) hc hA hK w hx hy hh
  relax := fun hc hA hK hv _ hℓ hn => relax_stepK hk hc hA hK hv hℓ hn

namespace Bounds8

variable (B : Bounds8 k)

theorem ε_lt_one : B.ε < 1 := lt_of_le_of_lt B.hεγ B.hγ1

theorem γ_nonneg : 0 ≤ B.γ := le_trans B.hε0 B.hεγ

theorem γV_nonneg : 0 ≤ B.γV := le_trans B.hε0 B.hεV

end Bounds8

/-- **Relaxing a set of pairs.** -/
theorem relax_all (B : Bounds8 k) (hc : 1 ≤ c) (hA : ∀ v, (A v).card = k) {M : Fin m → ℕ → ℕ}
    (hK : KeyInj k A M) : ∀ T : Finset (Fin m × ℕ), (∀ p ∈ T, p.1.val + 1 < m ∧ p.2 < k) →
      ((slabR c m k P A M (fun _ => ∅)).Ω.card : ℚ) ≤
        (1 - B.γV) ^ T.card * (slabR c m k P A M (RT T)).Ω.card := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
      intro _
      have e : RT (∅ : Finset (Fin m × ℕ)) = fun _ => ∅ := by
        funext v; ext ℓ; simp [mem_RT]
      rw [e, card_empty, pow_zero, one_mul]
  | insert p T hp ih =>
      intro hT
      have h1 := ih (fun q hq => hT q (mem_insert_of_mem hq))
      obtain ⟨hv, hℓ⟩ := hT p (mem_insert_self p T)
      have hn : p.2 ∉ RT T p.1 := by rw [mem_RT]; exact hp
      have e : RT (insert p T) = Radd (RT T) p.1 p.2 := by
        funext v
        ext ℓ
        rw [mem_RT, mem_insert]
        simp only [Radd]
        by_cases hv' : v = p.1
        · subst hv'
          rw [ite_eq_left rfl, mem_insert, mem_RT]
          constructor
          · rintro (h | h)
            · exact Or.inl (congrArg Prod.snd h)
            · exact Or.inr h
          · rintro (h | h)
            · exact Or.inl (Prod.ext rfl h)
            · exact Or.inr h
        · rw [ite_eq_right hv', mem_RT]
          constructor
          · rintro (h | h)
            · exact absurd (congrArg Prod.fst h) hv'
            · exact h
          · exact Or.inr
      have h2 := B.relax (P := P) (R := RT T) hc hA hK hv hℓ hn
      rw [← e] at h2
      have hγ : 0 ≤ 1 - B.γV := by linarith [B.hV1]
      rw [card_insert_of_notMem hp, pow_succ]
      calc ((slabR c m k P A M (fun _ => ∅)).Ω.card : ℚ)
          ≤ (1 - B.γV) ^ T.card * (slabR c m k P A M (RT T)).Ω.card := h1
        _ ≤ (1 - B.γV) ^ T.card * ((1 - B.γV) * (slabR c m k P A M (RT (insert p T))).Ω.card) :=
            mul_le_mul_of_nonneg_left h2 (pow_nonneg hγ _)
        _ = _ := by ring


end GridGen.Gauge
