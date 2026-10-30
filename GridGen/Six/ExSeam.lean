/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Six.ExState

/-!
# Height six at `k = 6`: the seam on a single-mismatch shape

`seam_shape`: a certificate for shape `j` (`certOK`, and `patS`, `patK` at every canonical
pattern) gives `Σ GU ≤ Σ GB` for every system of lists of shape `j` — rows `r < j` carrying a
`6`-list `U`, rows `r ≥ j` a `6`-list `V`, `|U ∩ V| = 5`.
-/

namespace GridGen.Six

open Finset

/-! ### The leaf, unfolded -/

theorem mskL_lt (j : ℕ) (l : List ℕ) : ∀ r, (mskL j l).getD r 0 < 256 := by
  intro r
  have h : ∀ r l, em (bmJ j r) l < 256 := fun r l =>
    lt_of_le_of_lt Nat.and_le_left (lt_trans (bmJ_lt j r) (by norm_num))
  match r with
  | 0 => exact h _ _
  | 1 => exact h _ _
  | 2 => exact h _ _
  | 3 => exact h _ _
  | 4 => exact h _ _
  | 5 => exact h _ _
  | _ + 6 => simp [mskL]

theorem tab_eq (ms : List ℕ) (hms : ∀ r, ms.getD r 0 < 256) :
    dblF (dblF (dblF (dblF (dblF (dblF 255 (ms.getD 0 0) 0) (ms.getD 1 0) 1) (ms.getD 2 0) 2)
      (ms.getD 3 0) 3) (ms.getD 4 0) 4) (ms.getD 5 0) 5 = pk 8 (atL ms 6) := by
  have h0 : (255 : ℕ) = pk 8 (atL ms 0) := by simp [atL, pk]
  have st : ∀ r < 6, dblF (pk 8 (atL ms r)) (ms.getD r 0) r = pk 8 (atL ms (r + 1)) :=
    fun r hr => by rw [dblF_eq hr, dblT_eq ms hms]
  rw [h0, st 0 (by norm_num), st 1 (by norm_num), st 2 (by norm_num), st 3 (by norm_num),
    st 4 (by norm_num), st 5 (by norm_num)]

theorem hor_eq (ms : List ℕ) : horF (pk 8 (atL ms 6)) 0 64 = itab ms := by
  have hlen : (atL ms 6).length = 64 := by rw [atL_length]; norm_num
  rw [horF_eq, itab, pk_eq_pkF 4, List.length_map, hlen]
  apply pkF_congr
  intro i hi
  rw [zero_add, getD_map_lt (by rw [hlen]; exact hi), pk_eq_pkF 8, lane_pkF _ (by rw [hlen]; exact hi)]
  intro k hk
  rw [hlen] at hk
  have := atL_lt ms 6 ((atL ms 6).getD k 0) (by
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hk)]; exact List.getElem_mem _)
  norm_num; exact this

/-- **The leaf, unfolded.** -/
theorem leafX_eq (D K j : ℕ) (cps : List (List (ℕ × ℕ) × ℕ)) (psi : List ℕ) (p : T6)
    (k : ℕ → ℕ) :
    leafX D K j cps psi p (k 0) (k 1) (k 2) (k 3) (k 4) (k 5)
      = okc6 D (D + K - penC cps (labL p k)) (accS (itab (mskL j (labL p k))) MQ6) psi := by
  unfold leafX tabF
  simp only [xN_eq]
  have := tab_eq (mskL j (labL p k)) (mskL_lt j (labL p k))
  simp only [mskL, labL, wmK, List.getD_cons_zero, List.getD_cons_succ] at this
  rw [this]
  have h2 := hor_eq (mskL j (labL p k))
  simp only [mskL, labL, wmK, List.getD_cons_zero, List.getD_cons_succ] at h2
  rw [h2, accG_eq]
  rfl

/-! ### The cone test is sound -/

theorem VL_len : ∀ i < 32, (VL.getD i []).length = 32 := by decide +kernel
theorem FL_len : ∀ d < 5, (FL.getD d []).length = 32 := by decide +kernel
theorem qUL_len : qUL.length = 32 := by decide +kernel
theorem FUN_ray : ∀ d < 5, FUN.getD d [] = FL.getD d [] := by decide +kernel
theorem FUN_Q : FUN.getD 5 [] = qLL := by decide +kernel

theorem psiL_ray (p : T6) {d : ℕ} (hd : d < 5) :
    (psiL p).getD d 0 = ∑ i : Fin 32, Vmat6 (orb p) i * Fv d i := by
  have hl : ((FL.take 5).map (dotZ (VL.getD (orb p) []))).length = 5 := by
    simp; decide +kernel
  unfold psiL
  rw [List.getD_append _ _ _ _ (by rw [hl]; exact hd), List.getD_eq_getElem _ _ (by rw [hl]; exact hd),
    List.getElem_map, List.getElem_take, ← List.getD_eq_getElem _ [] (by
      have : FL.length = 6 := by decide +kernel
      omega)]
  rw [dotZ_eq _ _ (VL_len _ (orb p).2) (FL_len d hd)]
  rfl

theorem psiL_Q (p : T6) : (psiL p).getD 5 0 = ∑ i : Fin 32, Vmat6 (orb p) i * qU i := by
  have hl : ((FL.take 5).map (dotZ (VL.getD (orb p) []))).length = 5 := by
    simp; decide +kernel
  unfold psiL
  rw [List.getD_append_right _ _ _ _ (by rw [hl]), hl]
  simp only [Nat.sub_self, List.getD_cons_zero]
  rw [dotZ_eq _ _ (VL_len _ (orb p).2) qUL_len]
  rfl

/-- **The cone test of a type is sound**: `e · GU ≤ D · (the count of the masks)` on the cone. -/
theorem okc6_sound {D e : ℕ} {ms : List ℕ} {psi : List ℕ} {p : T6}
    (h : okc6 D e (accS (itab ms) MQ6) psi = true) (hpsi : psiL p = psi) {w : Wt6}
    (hw : InCone6 w) :
    (e : ℝ) * rowV6 (orb p) w ≤ D * ∑ o : Fin 32, (cntO o ms : ℝ) * w o := by
  set S := accS (itab ms) MQ6 with hS
  have hd : ∀ d < 6, Nat.ble (Nat.add (Nat.mul e (psi.getD d 0)) (Nat.mul D (lane96 S (6 + d))))
      (Nat.mul D (lane96 S d)) = true := by
    unfold okc6 at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := h
    intro d hd
    interval_cases d <;> assumption
  -- the integer inequalities
  have hz : ∀ d < 6, ((e * psi.getD d 0 : ℕ) : ℤ)
      ≤ D * ∑ o : Fin 32, cntO o ms * ((FUN.getD d []).getD o 0 : ℕ) := by
    intro d hd'
    have h1 := hd d hd'
    rw [Nat.ble_eq, lane96_eq, lane96_eq] at h1
    have h2 := lanes_fun ms hd'
    rw [← hS] at h2
    rw [← h2]
    simp only [Nat.add_eq, Nat.mul_eq] at h1
    have : ((e * psi.getD d 0 + D * lane 96 S (6 + d) : ℕ) : ℤ) ≤ ((D * lane 96 S d : ℕ) : ℤ) := by
      exact_mod_cast h1
    push_cast at this ⊢
    linarith
  have hc : ∀ o : Fin 32, (0 : ℝ) ≤ cntO o ms := fun o => by
    have := (card_orb_setOf ms o).symm ▸ (Nat.cast_nonneg (α := ℤ) _)
    exact_mod_cast this
  rcases hw with hq | ⟨d, hd', rfl⟩
  · -- the box
    have h5 := hz 5 (by norm_num)
    rw [FUN_Q, ← hpsi, psiL_Q] at h5
    have h5' : (e : ℝ) * (∑ i : Fin 32, (Vmat6 (orb p) i : ℝ) * qU i)
        ≤ D * ∑ o : Fin 32, (cntO o ms : ℝ) * qL o := by
      have : ((e * ∑ i : Fin 32, Vmat6 (orb p) i * qU i : ℕ) : ℤ)
          ≤ D * ∑ o : Fin 32, cntO o ms * (qLL.getD o 0 : ℕ) := h5
      have := (Int.cast_le (R := ℝ)).mpr this
      push_cast at this
      exact this
    have hu : rowV6 (orb p) w ≤ (∑ i : Fin 32, (Vmat6 (orb p) i : ℝ) * qU i) / 10000000 := by
      unfold rowV6
      rw [Finset.sum_div]
      refine Finset.sum_le_sum fun i _ => ?_
      have := (hq i).2
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
    have hl : (∑ o : Fin 32, (cntO o ms : ℝ) * qL o) / 10000000 ≤ ∑ o : Fin 32, (cntO o ms : ℝ) * w o := by
      rw [Finset.sum_div]
      refine Finset.sum_le_sum fun o _ => ?_
      have := (hq o).1
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left this (hc o)
    have he : (0 : ℝ) ≤ e := Nat.cast_nonneg _
    have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg _
    calc (e : ℝ) * rowV6 (orb p) w
        ≤ e * ((∑ i : Fin 32, (Vmat6 (orb p) i : ℝ) * qU i) / 10000000) :=
          mul_le_mul_of_nonneg_left hu he
      _ = (e * (∑ i : Fin 32, (Vmat6 (orb p) i : ℝ) * qU i)) / 10000000 := by ring
      _ ≤ (D * ∑ o : Fin 32, (cntO o ms : ℝ) * qL o) / 10000000 := by
          apply div_le_div_of_nonneg_right h5' (by norm_num)
      _ = D * ((∑ o : Fin 32, (cntO o ms : ℝ) * qL o) / 10000000) := by ring
      _ ≤ D * ∑ o : Fin 32, (cntO o ms : ℝ) * w o := mul_le_mul_of_nonneg_left hl hD
  · -- a ray
    have h5 := hz d (by omega)
    rw [FUN_ray d hd', ← hpsi, psiL_ray p hd'] at h5
    have h5' : (e : ℝ) * (∑ i : Fin 32, (Vmat6 (orb p) i : ℝ) * Fv d i)
        ≤ D * ∑ o : Fin 32, (cntO o ms : ℝ) * Fv d o := by
      have : ((e * ∑ i : Fin 32, Vmat6 (orb p) i * Fv d i : ℕ) : ℤ)
          ≤ D * ∑ o : Fin 32, cntO o ms * ((FL.getD d []).getD o 0 : ℕ) := h5
      have := (Int.cast_le (R := ℝ)).mpr this
      push_cast at this
      exact this
    have hF : (0 : ℝ) < Fv d 0 := by exact_mod_cast Fv_pos d (by omega)
    unfold rowV6 rayW
    have e1 : ∑ i : Fin 32, (Vmat6 (orb p) i : ℝ) * ((Fv d i : ℝ) / Fv d 0)
        = (∑ i : Fin 32, (Vmat6 (orb p) i : ℝ) * Fv d i) / Fv d 0 := by
      rw [Finset.sum_div]; refine Finset.sum_congr rfl fun i _ => by ring
    have e2 : ∑ o : Fin 32, (cntO o ms : ℝ) * ((Fv d o : ℝ) / Fv d 0)
        = (∑ o : Fin 32, (cntO o ms : ℝ) * Fv d o) / Fv d 0 := by
      rw [Finset.sum_div]; refine Finset.sum_congr rfl fun o _ => by ring
    rw [e1, e2, mul_div_assoc', mul_div_assoc']
    exact div_le_div_of_nonneg_right h5' hF.le

end GridGen.Six
