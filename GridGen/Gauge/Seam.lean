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

theorem epsK_nonneg (hk : 10 ≤ k) : 0 ≤ epsK k := by
  have h := sum_le_epsK hk 0
  have hnn : 0 ≤ ∑ L ∈ range (0 + 1), (shapeCount L : ℚ) * pathW k L :=
    sum_nonneg fun L _ => mul_nonneg (by positivity) (pathW_nonneg (by omega) L)
  linarith

theorem gammaK_le_one (hk : 10 ≤ k) : gammaK k ≤ 1 := by
  unfold gammaK
  have hk' : (10 : ℚ) ≤ k := by exact_mod_cast hk
  have h3 : 0 < (k : ℚ) - 3 := by linarith
  rw [div_le_one (by positivity)]
  have h1 : ((k : ℚ) - 4) ^ 2 ≤ (k : ℚ) ^ 2 := by nlinarith
  have h2 : ((k : ℚ) - 5) ^ 2 ≤ ((k : ℚ) - 3) ^ 4 := by nlinarith
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

/-! ### The slab count, and the two kinds of step -/

variable {P A : Fin m → Finset ℕ}

/-- The slab count. -/
noncomputable def Z (c m k : ℕ) (P A : Fin m → Finset ℕ) (M : Fin m → ℕ → ℕ) : ℕ :=
  (slab c m k P A M).Ω.card

/-- The count only reads the keys of the colours of the seam column. -/
theorem Z_congr {M M' : Fin m → ℕ → ℕ} (h : ∀ v, ∀ a ∈ A v, M v a = M' v a) :
    Z c m k P A M = Z c m k P A M' := by
  unfold Z
  rw [card_Ω_eq, card_Ω_eq]
  refine sum_congr rfl fun p _ => sum_congr rfl fun s hs => ?_
  congr 1
  funext v
  exact h v (s v) (((mem_states (rowG m)).mp (mem_filter.mp hs).1).1 v)

theorem keyInj_unpair {N : Fin m → ℕ → ℕ} (hK : KeyInj k A N) (v : Fin m) (a₀ : ℕ) :
    KeyInj k A (unpair k N v a₀) := by
  intro v' a a' ha ha' e hlt
  unfold unpair at e hlt
  split_ifs at e hlt with h1 h2 h2 <;> try omega
  exact hK v' a a' ha ha' e hlt

theorem keyInj_moveKey {M : Fin m → ℕ → ℕ} (hK : KeyInj k A M) (w : ℕ) {x y : ℕ}
    (hx : x < k) (hy : y < k) : KeyInj k A (moveKey M w x y) := by
  intro v a a' ha ha' e hlt
  unfold moveKey at e hlt
  split_ifs at e hlt with hw
  · have e' := (Equiv.swap x y).injective e
    refine hK v a a' ha ha' e' ?_
    by_contra hge
    push Not at hge
    rw [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)] at hlt
    omega
  · exact hK v a a' ha ha' e hlt

/-- **A star step.** -/
theorem star_step (hk : 10 ≤ k) (hc : 1 ≤ c) (hA : ∀ v, (A v).card = k) {N : Fin m → ℕ → ℕ}
    (hK : KeyInj k A N) (v : Fin m) {a₀ : ℕ} (ha : a₀ ∈ A v) (hx : N v a₀ < k)
    (hPv : k - 1 ≤ (P v).card ∨ a₀ ∉ P v) :
    (Z c m k P A N : ℚ) ≤ (1 - gammaK k) * Z c m k P A (unpair k N v a₀) := by
  have hsplit := card_unpair (k := k) (P := P) (A := A) N hc v a₀ (N v a₀) rfl
  have hbox := box_bound (P := P) (by omega) (keyInj_unpair hK v a₀) hA hc v ha hx
    (by simp [unpair]) hPv
  unfold Z
  set Z₁ := (slab c m k P A (unpair k N v a₀)).Ω.card
  set hit := ((slab c m k P A (unpair k N v a₀)).Ω.filter (Hit hc v a₀ (N v a₀))).card
  have hk' : (10 : ℚ) ≤ k := by exact_mod_cast hk
  have hq : (Z₁ : ℚ) * (((k : ℚ) - 4) ^ 2 * ((k : ℚ) - 5) ^ 2) ≤
      (hit : ℚ) * ((k : ℚ) ^ 2 * ((k : ℚ) - 3) ^ 4) := by
    have := hbox
    rw [show k - 4 = (k - 4 : ℕ) from rfl] at this
    have e4 : ((k - 4 : ℕ) : ℚ) = (k : ℚ) - 4 := by push_cast [Nat.cast_sub (by omega : 4 ≤ k)]; ring
    have e5 : ((k - 5 : ℕ) : ℚ) = (k : ℚ) - 5 := by push_cast [Nat.cast_sub (by omega : 5 ≤ k)]; ring
    have e3 : ((k - 3 : ℕ) : ℚ) = (k : ℚ) - 3 := by push_cast [Nat.cast_sub (by omega : 3 ≤ k)]; ring
    have := (Nat.cast_le (α := ℚ)).mpr hbox
    push_cast at this
    rw [e4, e5, e3] at this
    linarith
  have hsplit' : (Z₁ : ℚ) = (slab c m k P A N).Ω.card + hit := by exact_mod_cast hsplit
  have hden : 0 < (k : ℚ) ^ 2 * ((k : ℚ) - 3) ^ 4 := by
    have : 0 < (k : ℚ) - 3 := by linarith
    positivity
  have hγ : gammaK k * Z₁ ≤ hit := by
    unfold gammaK
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    linarith
  linarith

/-- **A move step.** -/
theorem move_step (hk : 10 ≤ k) (hc : 1 ≤ c) (hA : ∀ v, (A v).card = k) {M : Fin m → ℕ → ℕ}
    (hK : KeyInj k A M) (w : ℕ) {x y : ℕ} (hx : x < k) (hy : y < k) :
    (1 - epsK k) * Z c m k P A M ≤ Z c m k P A (moveKey M w x y) := by
  have hε := epsK_nonneg hk
  by_cases hxy : x = y
  · subst hxy
    have : moveKey M w x x = M := by funext v a; simp [moveKey]
    rw [this]
    have : (0 : ℚ) ≤ Z c m k P A M := by positivity
    nlinarith
  have hbad := card_bad_le (P := P) (hc := hc) (w := w) (by omega) hK hA hxy hx hy
  have hmove := card_le_move_add_bad (P := P) (A := A) (M := M) (hc := hc) (w := w) hx hy
  have hsum := sum_crossPaths_le (m := m) hc w (pathW k) (pathW_nonneg (by omega))
  have hle := sum_le_epsK hk (Fintype.card (Cell c m))
  have hpath : ∑ l ∈ crossPaths (m := m) hc w,
      (2 : ℚ) / (((k : ℚ) - 3) ^ (l.length + 1) * ((k : ℚ) - 4)) ≤ epsK k :=
    le_trans (le_of_eq (sum_congr rfl fun l _ => rfl)) (le_trans hsum hle)
  unfold Z
  have hZ : (0 : ℚ) ≤ (slab c m k P A M).Ω.card := by positivity
  have hb' : (((slab c m k P A M).Ω.filter (Bad hc M w x y)).card : ℚ) ≤
      (slab c m k P A M).Ω.card * epsK k :=
    le_trans hbad (mul_le_mul_of_nonneg_left hpath hZ)
  have hm' : ((slab c m k P A M).Ω.card : ℚ) ≤ (slab c m k P A (moveKey M w x y)).Ω.card +
      ((slab c m k P A M).Ω.filter (Bad hc M w x y)).card := by exact_mod_cast hmove
  nlinarith

/-! ### The two phases -/

theorem one_sub_eps_nonneg (hk : 10 ≤ k) : 0 ≤ 1 - epsK k := by
  have h1 := two_epsK_le_gammaK hk
  have h2 := gammaK_le_one hk
  have h3 := epsK_nonneg hk
  linarith

/-- **Seam bounds.** A star gain `γ` and a move loss `ε` with `(1 - ε)² ≥ 1 - γ`, valid on the slabs
with past lists `P` and seam lists `A`. -/
structure SlabBounds (c m k : ℕ) (P A : Fin m → Finset ℕ) where
  /-- The star gain. -/
  γ : ℚ
  /-- The move loss. -/
  ε : ℚ
  hε0 : 0 ≤ 1 - ε
  hε1 : 1 - ε ≤ 1
  hγ0 : 0 ≤ 1 - γ
  hγε : 1 - γ ≤ (1 - ε) ^ 2
  star : ∀ N : Fin m → ℕ → ℕ, KeyInj k A N → ∀ (v : Fin m) (a₀ : ℕ), a₀ ∈ A v → N v a₀ < k →
    (k - 1 ≤ (P v).card ∨ a₀ ∉ P v) →
      (Z c m k P A N : ℚ) ≤ (1 - γ) * Z c m k P A (unpair k N v a₀)
  move : ∀ M : Fin m → ℕ → ℕ, KeyInj k A M → ∀ (w x y : ℕ), x < k → y < k →
    (1 - ε) * Z c m k P A M ≤ Z c m k P A (moveKey M w x y)

/-- The bounds for `k ≥ 10`. -/
noncomputable def slabBounds_ten (hk : 10 ≤ k) (hc : 1 ≤ c) (hA : ∀ v, (A v).card = k) :
    SlabBounds c m k P A where
  γ := gammaK k
  ε := epsK k
  hε0 := one_sub_eps_nonneg hk
  hε1 := by linarith [epsK_nonneg hk]
  hγ0 := by linarith [gammaK_le_one hk]
  hγε := by
    have := two_epsK_le_gammaK hk
    nlinarith [sq_nonneg (epsK k)]
  star := fun _ hK v _ ha hx hPv => star_step hk hc hA hK v ha hx hPv
  move := fun _ hK w _ _ hx hy => move_step hk hc hA hK w hx hy

/-- The moves of one edge. -/
theorem applyEdge_step (S : SlabBounds c m k P A) (v : ℕ) :
    ∀ (ts : List (ℕ × ℕ)) {M : Fin m → ℕ → ℕ}, Small k ts → KeyInj k A M →
      (1 - S.ε) ^ ts.length * Z c m k P A M ≤ Z c m k P A (applyEdge v ts M) ∧
        KeyInj k A (applyEdge v ts M) := by
  intro ts
  induction ts with
  | nil => intro M _ hK; simp [applyEdge, hK]
  | cons p ts ih =>
      intro M hs hK
      have hp := hs p (by simp)
      obtain ⟨h1, h2⟩ := ih (fun q hq => hs q (by simp [hq])) hK
      have e : applyEdge v (p :: ts) M = moveKey (applyEdge v ts M) v p.1 p.2 := rfl
      rw [e]
      refine ⟨?_, keyInj_moveKey h2 v hp.1 hp.2⟩
      have hm := S.move _ h2 v p.1 p.2 hp.1 hp.2
      have hε := S.hε0
      rw [List.length_cons, pow_succ]
      calc (1 - S.ε) ^ ts.length * (1 - S.ε) * (Z c m k P A M : ℚ)
          = (1 - S.ε) * ((1 - S.ε) ^ ts.length * Z c m k P A M) := by ring
        _ ≤ (1 - S.ε) * Z c m k P A (applyEdge v ts M) := mul_le_mul_of_nonneg_left h1 hε
        _ ≤ _ := hm

/-- The moves of all edges. -/
theorem applyAll_step (S : SlabBounds c m k P A)
    {Bx : ℕ → Finset ℕ} {βx : ℕ → ℕ → ℕ} (hR : RowLab k Bx βx) :
    ∀ (e : ℕ) {M : Fin m → ℕ → ℕ}, KeyInj k A M →
      (1 - S.ε) ^ (∑ i ∈ range e, (rho k Bx βx i (piL k Bx βx i)).length) *
          Z c m k P A M ≤ Z c m k P A (applyAll (k := k) (Bx := Bx) (βx := βx) e M) ∧
        KeyInj k A (applyAll (k := k) (Bx := Bx) (βx := βx) e M) := by
  intro e
  induction e with
  | zero => intro M hK; simp [applyAll, hK]
  | succ e ih =>
      intro M hK
      obtain ⟨h1, h2⟩ := ih hK
      have hs := (rho_spec hR (small_piL hR e) e).2.1
      obtain ⟨h3, h4⟩ := applyEdge_step S e _ hs h2
      refine ⟨?_, h4⟩
      have hε := S.hε0
      rw [sum_range_succ, pow_add]
      calc (1 - S.ε) ^ (∑ i ∈ range e, (rho k Bx βx i (piL k Bx βx i)).length) *
            (1 - S.ε) ^ (rho k Bx βx e (piL k Bx βx e)).length * (Z c m k P A M : ℚ)
          = (1 - S.ε) ^ (rho k Bx βx e (piL k Bx βx e)).length *
              ((1 - S.ε) ^ (∑ i ∈ range e, (rho k Bx βx i (piL k Bx βx i)).length) *
                Z c m k P A M) := by ring
        _ ≤ (1 - S.ε) ^ (rho k Bx βx e (piL k Bx βx e)).length *
              Z c m k P A (applyAll (k := k) (Bx := Bx) (βx := βx) e M) :=
            mul_le_mul_of_nonneg_left h1 (pow_nonneg hε _)
        _ ≤ _ := h3

/-- The stars. -/
noncomputable def stars (A B : Fin m → Finset ℕ) : Finset (Fin m × ℕ) :=
  univ.biUnion fun v => (A v \ B v).image fun a => (v, a)

theorem mem_stars {A B : Fin m → Finset ℕ} {p : Fin m × ℕ} :
    p ∈ stars A B ↔ p.2 ∈ A p.1 ∧ p.2 ∉ B p.1 := by
  unfold stars
  simp only [mem_biUnion, mem_univ, true_and, mem_image, mem_sdiff]
  constructor
  · rintro ⟨v, a, ha, rfl⟩; exact ha
  · intro h; exact ⟨p.1, p.2, h, rfl⟩

theorem card_stars (A B : Fin m → Finset ℕ) :
    (stars A B).card = ∑ v, (A v \ B v).card := by
  unfold stars
  rw [card_biUnion]
  · exact sum_congr rfl fun v _ => card_image_of_injective _ fun a b h => by simpa using h
  · intro v _ w _ hvw
    refine Finset.disjoint_left.mpr fun p hp hq => hvw ?_
    rw [mem_image] at hp hq
    obtain ⟨a, _, rfl⟩ := hp
    obtain ⟨b, _, e⟩ := hq
    exact (congrArg Prod.fst e).symm

/-- Keys after unpairing a set of stars. -/
def starKeys (k : ℕ) (β : ℕ → ℕ → ℕ) (S : Finset (Fin m × ℕ)) : Fin m → ℕ → ℕ :=
  fun v a => if (v, a) ∈ S then k else β v.val a

/-- **The star phase.** -/
theorem star_phase (S : SlabBounds c m k P A) {B : Fin m → Finset ℕ}
    (β : ℕ → ℕ → ℕ) (hβ : ∀ v : Fin m, Set.InjOn (β v.val) (A v) ∧ ∀ a ∈ A v, β v.val a < k)
    (hP : ∀ v a, a ∈ A v → k - 1 ≤ (P v).card ∨ a ∉ P v) :
    ∀ T : Finset (Fin m × ℕ), T ⊆ stars A B →
      (Z c m k P A (fun v a => β v.val a) : ℚ) ≤
        (1 - S.γ) ^ T.card * Z c m k P A (starKeys k β T) := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
      intro _
      simp only [card_empty, pow_zero, one_mul, Nat.cast_le]
      exact le_of_eq (congrArg _ (by funext v a; simp [starKeys]))
  | insert p T hp ih =>
      intro hsub
      have hpS := hsub (mem_insert_self p T)
      rw [mem_stars] at hpS
      have h1 := ih (fun q hq => hsub (mem_insert_of_mem hq))
      have hK : KeyInj k A (starKeys k β T) := by
        intro v a a' ha ha' e hlt
        unfold starKeys at e hlt
        split_ifs at e hlt with h1 h2 h2 <;> try omega
        exact (hβ v).1 ha ha' e
      have hx : starKeys k β T p.1 p.2 < k := by
        unfold starKeys; rw [ite_eq_right (by simpa using hp)]; exact (hβ p.1).2 _ hpS.1
      have hstep := S.star _ hK p.1 p.2 hpS.1 hx (hP p.1 p.2 hpS.1)
      have e : unpair k (starKeys k β T) p.1 p.2 = starKeys k β (insert p T) := by
        funext v a
        unfold unpair starKeys
        by_cases h : v = p.1 ∧ a = p.2
        · rw [ite_eq_left h, ite_eq_left]; rw [h.1, h.2]; exact mem_insert_self _ _
        · rw [ite_eq_right h]
          have hne : (v, a) ≠ p := fun e' => h ⟨congrArg Prod.fst e', congrArg Prod.snd e'⟩
          simp only [mem_insert, hne, false_or]
      rw [e] at hstep
      have hγ : 0 ≤ 1 - S.γ := S.hγ0
      rw [card_insert_of_notMem hp, pow_succ]
      calc (Z c m k P A (fun v a => β v.val a) : ℚ)
          ≤ (1 - S.γ) ^ T.card * Z c m k P A (starKeys k β T) := h1
        _ ≤ (1 - S.γ) ^ T.card * ((1 - S.γ) * Z c m k P A (starKeys k β (insert p T))) :=
            mul_le_mul_of_nonneg_left hstep (pow_nonneg hγ _)
        _ = _ := by ring

/-! ### The core inequality -/

/-- Rows of a column, extended by empty lists. -/
def extR (A : Fin m → Finset ℕ) : ℕ → Finset ℕ := fun v => if h : v < m then A ⟨v, h⟩ else ∅

theorem extR_val (A : Fin m → Finset ℕ) (v : Fin m) : extR A v.val = A v := by
  simp [extR, v.isLt]

theorem extR_ge (A : Fin m → Finset ℕ) {v : ℕ} (h : m ≤ v) : extR A v = ∅ := by
  simp [extR, show ¬ v < m by omega]

/-- **The slab inequality.** The new gauge's keys give at least as many slab solutions as the old
gauge's keys. -/
theorem slab_core_gen (S : SlabBounds c m k P A) (hA : ∀ v, (A v).card = k)
    {B : Fin m → Finset ℕ} (hB : ∀ v, (B v).card = k) (β : ℕ → ℕ → ℕ)
    (hβ : ∀ v : Fin m, Set.InjOn (β v.val) (A v) ∧ ∀ a ∈ A v, β v.val a < k)
    (hvc : ∀ v, ∀ c ∈ extR A v ∩ extR A (v + 1), β (v + 1) c = β v c)
    (hP : ∀ v a, a ∈ A v → k - 1 ≤ (P v).card ∨ a ∉ P v) :
    Z c m k P A (fun v a => β v.val a) ≤
      Z c m k P A (fun v a => if a ∈ B v then
        glueLab k (extR B) (tilde (extR A) (extR B) β) v.val a else k) := by
  set Ax := extR A
  set Bx := extR B
  have hcard : ∀ v, (Ax v).card = (Bx v).card := by
    intro v; simp only [Ax, Bx, extR]; split_ifs with h
    · rw [hA, hB]
    · rfl
  have hβx : ∀ v, Set.InjOn (β v) (Ax v) ∧ ∀ a ∈ Ax v, β v a < k := by
    intro v; simp only [Ax, extR]; split_ifs with h
    · exact hβ ⟨v, h⟩
    · simp
  have hR : RowLab k Bx (tilde Ax Bx β) := rowLab_tilde hcard hβx
  set M0 := starKeys k β (stars A B)
  -- the star phase
  have h1 := star_phase S (B := B) β hβ hP (stars A B) (Subset.refl _)
  have hK0 : KeyInj k A M0 := by
    intro v a a' ha ha' e hlt
    simp only [M0, starKeys] at e hlt
    split_ifs at e hlt with h1 h2 h2 <;> try omega
    exact (hβ v).1 ha ha' e
  -- the moves
  obtain ⟨h2, -⟩ := applyAll_step S hR m hK0
  have hfin : Z c m k P A (applyAll (k := k) (Bx := Bx) (βx := tilde Ax Bx β) m M0) =
      Z c m k P A (fun v a => if a ∈ B v then glueLab k Bx (tilde Ax Bx β) v.val a else k) := by
    refine Z_congr fun v a ha => ?_
    rw [applyAll_eq, show min v.val m = v.val by have := v.isLt; omega]
    simp only [M0, starKeys, mem_stars]
    by_cases hb : a ∈ B v
    · rw [ite_eq_right (by simp [hb]), ite_eq_left hb]
      unfold glueLab tilde
      rw [ite_eq_left (by rw [show Ax v.val = A v from extR_val A v]; exact ha)]
    · rw [ite_eq_left ⟨ha, hb⟩, ite_eq_right hb]
      exact comp_of_ge (small_piL hR _) le_rfl
  rw [hfin] at h2
  -- counting the moves
  set H := (stars A B).card
  set T := ∑ i ∈ range m, (rho k Bx (tilde Ax Bx β) i (piL k Bx (tilde Ax Bx β) i)).length
  have hT : T ≤ 2 * H := by
    have hsd : ∀ v : Fin m, (B v \ A v).card = (A v \ B v).card := by
      intro v
      have e1 := card_sdiff_add_card_inter (B v) (A v)
      have e2 := card_sdiff_add_card_inter (A v) (B v)
      rw [inter_comm, hA] at e2
      rw [hB] at e1
      omega
    have hsumB : ∑ i ∈ range m, (Bx i \ Ax i).card = H := by
      simp only [H]
      rw [card_stars, ← Fin.sum_univ_eq_sum_range (fun i => (Bx i \ Ax i).card)]
      refine sum_congr rfl fun v _ => ?_
      rw [show Bx v.val = B v from extR_val B v, show Ax v.val = A v from extR_val A v, hsd]
    have hshift : ∑ i ∈ range m, (Bx (i + 1) \ Ax (i + 1)).card ≤
        ∑ i ∈ range m, (Bx i \ Ax i).card := by
      have e1 := sum_range_succ' (fun i => (Bx i \ Ax i).card) m
      have e2 := sum_range_succ (fun i => (Bx i \ Ax i).card) m
      have hm : (Bx m \ Ax m).card = 0 := by simp [Bx, extR_ge B (le_refl m)]
      omega
    calc T ≤ ∑ i ∈ range m, ((Bx i \ Ax i).card + (Bx (i + 1) \ Ax (i + 1)).card) :=
          sum_le_sum fun i _ => le_trans (length_rho_le hR i) (card_mismatch_le hvc i)
      _ = ∑ i ∈ range m, (Bx i \ Ax i).card + ∑ i ∈ range m, (Bx (i + 1) \ Ax (i + 1)).card :=
          sum_add_distrib
      _ ≤ 2 * H := by omega
  -- the arithmetic
  have hε := S.hε0
  have hε1 := S.hε1
  have hγ := S.hγε
  have hγ0 := S.hγ0
  have hpow : (1 - S.γ) ^ H ≤ (1 - S.ε) ^ T := by
    calc (1 - S.γ) ^ H ≤ ((1 - S.ε) ^ 2) ^ H := pow_le_pow_left₀ hγ0 hγ H
      _ = (1 - S.ε) ^ (2 * H) := by rw [← pow_mul]
      _ ≤ (1 - S.ε) ^ T := pow_le_pow_of_le_one hε hε1 hT
  have hZ0 : (0 : ℚ) ≤ Z c m k P A M0 := by positivity
  have : (Z c m k P A (fun v a => β v.val a) : ℚ) ≤
      Z c m k P A (fun v a => if a ∈ B v then glueLab k Bx (tilde Ax Bx β) v.val a else k) :=
    calc (Z c m k P A (fun v a => β v.val a) : ℚ) ≤ (1 - S.γ) ^ H * Z c m k P A M0 := h1
      _ ≤ (1 - S.ε) ^ T * Z c m k P A M0 := mul_le_mul_of_nonneg_right hpow hZ0
      _ ≤ _ := h2
  exact_mod_cast this

/-- **The slab inequality** for `k ≥ 10`. -/
theorem slab_core (hk : 10 ≤ k) (hc : 1 ≤ c) (hA : ∀ v, (A v).card = k)
    {B : Fin m → Finset ℕ} (hB : ∀ v, (B v).card = k) (β : ℕ → ℕ → ℕ)
    (hβ : ∀ v : Fin m, Set.InjOn (β v.val) (A v) ∧ ∀ a ∈ A v, β v.val a < k)
    (hvc : ∀ v, ∀ c ∈ extR A v ∩ extR A (v + 1), β (v + 1) c = β v c)
    (hP : ∀ v a, a ∈ A v → k - 1 ≤ (P v).card ∨ a ∉ P v) :
    Z c m k P A (fun v a => β v.val a) ≤
      Z c m k P A (fun v a => if a ∈ B v then
        glueLab k (extR B) (tilde (extR A) (extR B) β) v.val a else k) :=
  slab_core_gen (slabBounds_ten hk hc hA) hA hB β hβ hvc hP

end GridGen.Gauge
