/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Eight.Holes
import GridGen.Gauge.Eight.Bad8
import GridGen.Gauge.Eight.Box8
import GridGen.Gauge.Eight.Counts8
import GridGen.Gauge.Eight.BoxV

/-!
# The seam steps at `k = 8`

* **star gain** `γ₈ = 5184/960375` (`box_bound_eight`);
* **move loss** `ε₈`, for moves through a hole (`card_bad_le_hole`): chain weights `600` for two
  cells, `4 · 5^{L+1}` otherwise, two-cell paths counted once, exact shape counts to eighteen
  cells (`Eight/Counts8.lean`), the `(L-1)3^{L-1}` tail beyond;
* **relaxation gain** `γ_V = 152/27675` (`boxV_bound`).

`ε₈ ≤ γ₈` and `ε₈ ≤ γ_V` (`epsEight_le`), with margins of about `14%` and `16%`.
-/

open Finset
open scoped Classical

set_option linter.unusedSectionVars false

namespace GridGen.Gauge

variable {c m : ℕ} {P A : Fin m → Finset ℕ}

/-! ### Chain weights and the move loss -/

/-- The chain weights at `k = 8`: `600` for two cells, `4 · 5^{L+1}` otherwise. -/
def W8 (L : ℕ) : ℚ := if L = 2 then 600 else 4 * 5 ^ (L + 1)

theorem W8_pos (L : ℕ) : 0 < W8 L := by unfold W8; split_ifs <;> positivity

theorem W8_le {M : Fin m → ℕ → ℕ} {hc : 1 ≤ c} {w : ℕ} (hA : ∀ v, (A v).card = 8) :
    ∀ l ∈ crossPaths (m := m) hc w,
      0 < W8 l.length ∧ W8 l.length ≤ (slab c m 8 P A M).chainProd (chainOf l) := by
  intro l hl
  have hl' : CrossPath hc w l := (mem_filter.mp hl).2
  refine ⟨W8_pos _, ?_⟩
  unfold W8
  split_ifs with h2
  · have := chainProd_two (P := P) (M := M) (by norm_num) hA hl' h2
    norm_num at this
    exact_mod_cast this
  · obtain ⟨hne, hnd, hch, hlen, hcol⟩ := chainOf_props hl'
    have hD : ∀ z ∈ chainOf l, ((slab c m 8 P A M).D z).card = 8 := by
      intro z hz
      by_cases h1 : z.1.val = 1
      · rw [slab_D_one h1, hA]
      · rw [slab_D_fut (by have := hcol z hz; omega), card_range]
    have hge := chainProd_ge (P := P) (A := A) (M := M) (by norm_num) (chainOf l) hne hnd hch hD
    rw [hlen, show l.length + 2 - 1 = l.length + 1 by omega] at hge
    norm_num at hge
    have := (Nat.cast_le (α := ℚ)).mpr hge
    push_cast at this
    linarith

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
  obtain ⟨h13, h14, h15, h16, h17, h18⟩ := shapeCnt_13_18
  unfold epsEight w8 W8
  simp only [sum_range_succ, sum_range_zero, h0, h1, h2, h3, h4, h5, h6, h7,
    shapeCount_eq_cnt 8, shapeCount_eq_cnt 9, shapeCount_eq_cnt 10, shapeCount_eq_cnt 11,
    shapeCount_eq_cnt 12, shapeCount_eq_cnt 13, shapeCount_eq_cnt 14, shapeCount_eq_cnt 15,
    shapeCount_eq_cnt 16, shapeCount_eq_cnt 17, shapeCount_eq_cnt 18, shapeCnt_8, shapeCnt_9,
    shapeCnt_10, shapeCnt_11, shapeCnt_12, h13, h14, h15, h16, h17, h18]
  norm_num

/-- The star gain at `k = 8`. -/
def gammaEight : ℚ := 5184 / 960375

/-- The relaxation gain at `k = 8`. -/
def gammaV : ℚ := 152 / 27675

theorem epsEight_le : epsEight ≤ gammaEight ∧ epsEight ≤ gammaV := by
  rw [epsEight_eq]; unfold gammaEight gammaV; constructor <;> norm_num

theorem epsEight_nonneg : 0 ≤ epsEight := by rw [epsEight_eq]; norm_num

/-! ### The three steps -/

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

/-- **A move step through a hole at `k = 8`.** -/
theorem move_step8 (hc : 1 ≤ c) (hA : ∀ v, (A v).card = 8) {M : Fin m → ℕ → ℕ}
    (hK : KeyInj 8 A M) (w : ℕ) {x y : ℕ} (hx : x < 8) (hy : y < 8) (hh : HoleAt A M w x y) :
    (1 - epsEight) * Z c m 8 P A M ≤ Z c m 8 P A (moveKey M w x y) := by
  have hε := epsEight_nonneg
  by_cases hxy : x = y
  · subst hxy
    have : moveKey M w x x = M := by funext v a; simp [moveKey]
    rw [this]
    have : (0 : ℚ) ≤ Z c m 8 P A M := by positivity
    nlinarith
  have hbad := card_bad_le_hole (P := P) (hc := hc) (w := w) hK hxy hx hy hh W8 (W8_le hA)
  have hmove := card_le_move_add_bad (P := P) (A := A) (M := M) (hc := hc) (w := w) hx hy
  have hsum := sum_crossPaths_le (m := m) hc w w8 w8_nonneg
  have hle := sum_le_epsEight (Fintype.card (Cell c m))
  unfold Z
  have hZ : (0 : ℚ) ≤ (slab c m 8 P A M).Ω.card := by positivity
  have hb' : (((slab c m 8 P A M).Ω.filter (Bad hc M w x y)).card : ℚ) ≤
      (slab c m 8 P A M).Ω.card * epsEight :=
    le_trans hbad (mul_le_mul_of_nonneg_left (le_trans hsum hle) hZ)
  have hm' : ((slab c m 8 P A M).Ω.card : ℚ) ≤ (slab c m 8 P A (moveKey M w x y)).Ω.card +
      ((slab c m 8 P A M).Ω.filter (Bad hc M w x y)).card := by exact_mod_cast hmove
  nlinarith

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

/-- **Relaxing a set of pairs.** -/
theorem relax_all (hc : 1 ≤ c) (hA : ∀ v, (A v).card = 8) {M : Fin m → ℕ → ℕ}
    (hK : KeyInj 8 A M) : ∀ T : Finset (Fin m × ℕ), (∀ p ∈ T, p.1.val + 1 < m ∧ p.2 < 8) →
      ((slabR c m 8 P A M (fun _ => ∅)).Ω.card : ℚ) ≤
        (1 - gammaV) ^ T.card * (slabR c m 8 P A M (RT T)).Ω.card := by
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
      have h2 := relax_step8 (P := P) hc hA hK (R := RT T) hv hℓ hn
      rw [← e] at h2
      have hγ : 0 ≤ 1 - gammaV := by unfold gammaV; norm_num
      rw [card_insert_of_notMem hp, pow_succ]
      calc ((slabR c m 8 P A M (fun _ => ∅)).Ω.card : ℚ)
          ≤ (1 - gammaV) ^ T.card * (slabR c m 8 P A M (RT T)).Ω.card := h1
        _ ≤ (1 - gammaV) ^ T.card * ((1 - gammaV) * (slabR c m 8 P A M (RT (insert p T))).Ω.card) :=
            mul_le_mul_of_nonneg_left h2 (pow_nonneg hγ _)
        _ = _ := by ring

end GridGen.Gauge
