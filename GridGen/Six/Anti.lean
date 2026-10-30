/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Six.Greedy

/-!
# Height six: the greedy value is antitone in the intersections

`N6g n e` (`GridGen/Six/Greedy.lean`) is nonincreasing in each consecutive intersection `eⱼ` on
the range `eⱼ ≤ min (nⱼ, nⱼ₊₁)`, `nᵢ ≥ 5` (`N6g_anti`). The review
(`ai_research_notes/H6_K6_REVIEW_2026-10-29.md` §3) observed this on all 2,581,720
neighbouring pairs of the relaxation; here it is proved symbolically, the same way as
`greedy_min6`:

* raising `eⱼ` at fixed triples changes the value by exactly `-(eⱼ' - eⱼ)` times a product of
  sub-path counts (`dir_e1` … `dir_e5`; e.g. `N(rows 3..6)` for `e₁`);
* it raises the triples `T_{j-1}, T_j` by at most as much, and the value `H6` is Lipschitz in
  each triple with slope at most a sub-path count (`up_t1` … `up_t4`);
* the direct loss dominates (`anti_e1` … `anti_e5`).

It is used to reduce the pointwise check of a mismatch class to one state per pattern of
bonuses (`GridGen/Six/Point.lean`).
-/

namespace GridGen.Six

section up

variable {n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 : ℤ}
  (hn1 : 5 ≤ n1) (hn2 : 5 ≤ n2) (hn3 : 5 ≤ n3) (hn4 : 5 ≤ n4) (hn5 : 5 ≤ n5) (hn6 : 5 ≤ n6)
  (he1 : e1 ≤ n1) (he5 : e5 ≤ n6)
include hn1 hn2 hn3 hn4 hn5 hn6 he1 he5

theorem up_t1 {t1 t1' t2 t3 t4 : ℤ} (h : t1 ≤ t1') :
    H6 n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1' t2 t3 t4
      - H6 n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2 t3 t4
      ≤ (t1' - t1) * (n4 * n5 * n6 - e4 * n6 - n4 * e5 + t4) := by
  unfold H6
  rw [N6z_split, N6z_split]
  have hB := B6_t1 n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t1' t2 t3 t4
  have hm := min_move1 (b := t2) h
  set m := min t1 t2
  set m' := min t1' t2
  set m2 := min t2 t3
  set m3 := min t3 t4
  set P2 := max 0 (m2 + m3 - t3)
  have hP := max0_move (u := m + m2 - t2) (u' := m' + m2 - t2)
  rw [show m' + m2 - t2 - (m + m2 - t2) = m' - m by ring, min_eq_left hm.1,
    max_eq_right hm.1] at hP
  set P := max 0 (m + m2 - t2)
  set P' := max 0 (m' + m2 - t2)
  have hX := min_move1 (b := P2) (show P ≤ P' by linarith)
  have k1 : 0 ≤ (n5 * n6 - e5 - n6) * (m' - m) := by
    apply mul_nonneg _ (by linarith); nlinarith
  have k2 : n6 * (P' - P) ≤ n6 * (m' - m) := mul_le_mul_of_nonneg_left hP.2 (by linarith)
  nlinarith

theorem up_t4 {t1 t2 t3 t4 t4' : ℤ} (h : t4 ≤ t4') :
    H6 n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2 t3 t4'
      - H6 n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2 t3 t4
      ≤ (t4' - t4) * (n1 * n2 * n3 - e1 * n3 - n1 * e2 + t1) := by
  unfold H6
  rw [N6z_split, N6z_split]
  have hB := B6_t4 n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2 t3 t4 t4'
  have hm := min_move2 (a := t3) h
  set m := min t3 t4
  set m' := min t3 t4'
  set m1 := min t1 t2
  set m2 := min t2 t3
  set P1 := max 0 (m1 + m2 - t2)
  have hP := max0_move (u := m2 + m - t3) (u' := m2 + m' - t3)
  rw [show m2 + m' - t3 - (m2 + m - t3) = m' - m by ring, min_eq_left hm.1,
    max_eq_right hm.1] at hP
  set P := max 0 (m2 + m - t3)
  set P' := max 0 (m2 + m' - t3)
  have hX := min_move2 (a := P1) (show P ≤ P' by linarith)
  have k1 : 0 ≤ (n1 * n2 - e1 - n1) * (m' - m) := by
    apply mul_nonneg _ (by linarith); nlinarith
  have k2 : n1 * (P' - P) ≤ n1 * (m' - m) := mul_le_mul_of_nonneg_left hP.2 (by linarith)
  nlinarith

theorem up_t2 {t1 t2 t2' t3 t4 : ℤ} (h : t2 ≤ t2') :
    H6 n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2' t3 t4
      - H6 n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2 t3 t4
      ≤ (t2' - t2) * (n1 * (n5 * n6 - e5) + 1) := by
  unfold H6
  rw [N6z_split, N6z_split]
  have hB := B6_t2 n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2 t2' t3 t4
  have h1 := min_move2 (a := t1) h
  have h2 := min_move1 (b := t3) h
  set a := min t1 t2
  set a' := min t1 t2'
  set b := min t2 t3
  set b' := min t2' t3
  set c := min t3 t4
  have hP1 := max0_move (u := a + b - t2) (u' := a' + b' - t2')
  have hP2 := max0_move (u := b + c - t3) (u' := b' + c - t3)
  rw [show b' + c - t3 - (b + c - t3) = b' - b by ring, min_eq_left h2.1,
    max_eq_right h2.1] at hP2
  have l1 : min 0 (a' + b' - t2' - (a + b - t2)) ≥ -(t2' - t2) := le_min (by linarith) (by linarith)
  have l2 : max 0 (a' + b' - t2' - (a + b - t2)) ≤ a' - a :=
    max_le (by linarith) (by linarith)
  set P := max 0 (a + b - t2)
  set P' := max 0 (a' + b' - t2')
  set Q := max 0 (b + c - t3)
  set Q' := max 0 (b' + c - t3)
  have hX := (min_move_gen (a := P) (b := Q) (a' := P') (b' := Q')).1
  have hX' : min (P' - P) (Q' - Q) ≥ -(t2' - t2) := le_min (by linarith) (by linarith)
  have k1 : 0 ≤ (n5 * n6 - e5 - n6) * (a' - a) := by
    apply mul_nonneg _ (by linarith); nlinarith
  have k2 : 0 ≤ (n1 * n6 - n1) * (b' - b) := by
    apply mul_nonneg _ (by linarith); nlinarith
  have k3 : n6 * (P' - P) ≤ n6 * (a' - a) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have k4 : n1 * (Q' - Q) ≤ n1 * (b' - b) := mul_le_mul_of_nonneg_left hP2.2 (by linarith)
  nlinarith

theorem up_t3 {t1 t2 t3 t3' t4 : ℤ} (h : t3 ≤ t3') :
    H6 n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2 t3' t4
      - H6 n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2 t3 t4
      ≤ (t3' - t3) * (n6 * (n1 * n2 - e1) + 1) := by
  unfold H6
  rw [N6z_split, N6z_split]
  have hB := B6_t3 n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2 t3 t3' t4
  have h1 := min_move2 (a := t2) h
  have h2 := min_move1 (b := t4) h
  set a := min t1 t2
  set b := min t2 t3
  set b' := min t2 t3'
  set c := min t3 t4
  set c' := min t3' t4
  have hP1 := max0_move (u := a + b - t2) (u' := a + b' - t2)
  have hP2 := max0_move (u := b + c - t3) (u' := b' + c' - t3')
  rw [show a + b' - t2 - (a + b - t2) = b' - b by ring, min_eq_left h1.1,
    max_eq_right h1.1] at hP1
  have l1 : min 0 (b' + c' - t3' - (b + c - t3)) ≥ -(t3' - t3) := le_min (by linarith) (by linarith)
  have l2 : max 0 (b' + c' - t3' - (b + c - t3)) ≤ c' - c :=
    max_le (by linarith) (by linarith)
  set P := max 0 (a + b - t2)
  set P' := max 0 (a + b' - t2)
  set Q := max 0 (b + c - t3)
  set Q' := max 0 (b' + c' - t3')
  have hX := (min_move_gen (a := P) (b := Q) (a' := P') (b' := Q')).1
  have hX' : min (P' - P) (Q' - Q) ≥ -(t3' - t3) := le_min (by linarith) (by linarith)
  have k1 : 0 ≤ (n1 * n2 - e1 - n1) * (c' - c) := by
    apply mul_nonneg _ (by linarith); nlinarith
  have k2 : 0 ≤ (n1 * n6 - n6) * (b' - b) := by
    apply mul_nonneg _ (by linarith); nlinarith
  have k3 : n1 * (Q' - Q) ≤ n1 * (c' - c) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have k4 : n6 * (P' - P) ≤ n6 * (b' - b) := mul_le_mul_of_nonneg_left hP1.2 (by linarith)
  nlinarith

end up

/-! ### The direct dependence on the intersections -/

theorem dir_e1 (n1 n2 n3 n4 n5 n6 e1 e1' e2 e3 e4 e5 t1 t2 t3 t4 : ℤ) :
    H6 n1 n2 n3 n4 n5 n6 e1' e2 e3 e4 e5 t1 t2 t3 t4 - H6 n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2 t3 t4
      = -(e1' - e1) * (n3 * n4 * n5 * n6 - e3 * n5 * n6 - n3 * e4 * n6 - n3 * n4 * e5 + t3 * n6
        + e3 * e5 + n3 * t4 - min t3 t4) := by
  unfold H6 N6z; ring

theorem dir_e2 (n1 n2 n3 n4 n5 n6 e1 e2 e2' e3 e4 e5 t1 t2 t3 t4 : ℤ) :
    H6 n1 n2 n3 n4 n5 n6 e1 e2' e3 e4 e5 t1 t2 t3 t4 - H6 n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2 t3 t4
      = -(e2' - e2) * (n1 * (n4 * n5 * n6 - e4 * n6 - n4 * e5 + t4)) := by
  unfold H6 N6z; ring

theorem dir_e3 (n1 n2 n3 n4 n5 n6 e1 e2 e3 e3' e4 e5 t1 t2 t3 t4 : ℤ) :
    H6 n1 n2 n3 n4 n5 n6 e1 e2 e3' e4 e5 t1 t2 t3 t4 - H6 n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2 t3 t4
      = -(e3' - e3) * ((n1 * n2 - e1) * (n5 * n6 - e5)) := by
  unfold H6 N6z; ring

theorem dir_e4 (n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e4' e5 t1 t2 t3 t4 : ℤ) :
    H6 n1 n2 n3 n4 n5 n6 e1 e2 e3 e4' e5 t1 t2 t3 t4 - H6 n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2 t3 t4
      = -(e4' - e4) * (n6 * (n1 * n2 * n3 - e1 * n3 - n1 * e2 + t1)) := by
  unfold H6 N6z; ring

theorem dir_e5 (n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 e5' t1 t2 t3 t4 : ℤ) :
    H6 n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5' t1 t2 t3 t4 - H6 n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 t1 t2 t3 t4
      = -(e5' - e5) * (n1 * n2 * n3 * n4 - e1 * n3 * n4 - n1 * e2 * n4 - n1 * n2 * e3 + t1 * n4
        + e1 * e3 + n1 * t2 - min t1 t2) := by
  unfold H6 N6z; ring

/-! ### The greedy triples move by at most the move of an intersection -/

theorem max0_lip {u u' : ℤ} (h : u ≤ u') : 0 ≤ max 0 u' - max 0 u ∧ max 0 u' - max 0 u ≤ u' - u := by
  constructor <;> rcases le_total 0 u with h1 | h1 <;> rcases le_total 0 u' with h2 | h2 <;>
    simp only [max_eq_left, max_eq_right, h1, h2] <;> linarith

/-! ### Antitone in each intersection -/

section anti

variable {n1 n2 n3 n4 n5 n6 : ℤ}
  (hn1 : 5 ≤ n1) (hn2 : 5 ≤ n2) (hn3 : 5 ≤ n3) (hn4 : 5 ≤ n4) (hn5 : 5 ≤ n5) (hn6 : 5 ≤ n6)
include hn1 hn2 hn3 hn4 hn5 hn6

theorem anti_e1 {e1 e1' e2 e3 e4 e5 : ℤ} (h : e1 ≤ e1') (he1 : e1' ≤ n1) (he3 : e3 ≤ n4)
    (he4 : e4 ≤ n5) (he5 : e5 ≤ n5) (he5' : e5 ≤ n6) :
    N6g n1 n2 n3 n4 n5 n6 e1' e2 e3 e4 e5 ≤ N6g n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 := by
  unfold N6g
  set T1 := max 0 (e1 + e2 - n2)
  set T1' := max 0 (e1' + e2 - n2)
  set T2 := max 0 (e2 + e3 - n3)
  set T3 := max 0 (e3 + e4 - n4)
  set T4 := max 0 (e4 + e5 - n5)
  have hT := max0_lip (u := e1 + e2 - n2) (u' := e1' + e2 - n2) (by linarith)
  have hT3 : 0 ≤ T3 := le_max_left _ _
  have hT4 : 0 ≤ T4 := le_max_left _ _
  have u1 := up_t1 hn1 hn2 hn3 hn4 hn5 hn6 he1 he5' (e2 := e2) (e3 := e3) (e4 := e4)
    (t2 := T2) (t3 := T3) (t4 := T4) (show T1 ≤ T1' by linarith)
  have d1 := dir_e1 n1 n2 n3 n4 n5 n6 e1 e1' e2 e3 e4 e5 T1 T2 T3 T4
  have hm : min T3 T4 ≤ T3 := min_le_left _ _
  have hC : 0 ≤ n4 * n5 * n6 - e4 * n6 - n4 * e5 + T4 := by
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ n5 - e4 by linarith) (show (0 : ℤ) ≤ n6 by linarith),
      mul_nonneg (show (0 : ℤ) ≤ n5 - e5 by linarith) (show (0 : ℤ) ≤ n4 by linarith),
      mul_nonneg (mul_nonneg (show (0 : ℤ) ≤ n4 - 2 by linarith) (show (0 : ℤ) ≤ n5 by linarith))
        (show (0 : ℤ) ≤ n6 - 2 by linarith)]
  have hkey : n4 * n5 * n6 - e4 * n6 - n4 * e5 + T4 ≤ n3 * n4 * n5 * n6 - e3 * n5 * n6
      - n3 * e4 * n6 - n3 * n4 * e5 + T3 * n6 + e3 * e5 + n3 * T4 - min T3 T4 := by
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ n3 - 5 by linarith) (show (0 : ℤ) ≤ n4 - 5 by linarith),
      mul_nonneg (show (0 : ℤ) ≤ n4 - e3 by linarith) (show (0 : ℤ) ≤ n5 * n6 - e5 by nlinarith),
      mul_nonneg (show (0 : ℤ) ≤ n5 - e4 by linarith) (show (0 : ℤ) ≤ n6 by linarith),
      mul_nonneg (show (0 : ℤ) ≤ n3 - 1 by linarith) hT4,
      mul_nonneg hT3 (show (0 : ℤ) ≤ n6 - 1 by linarith),
      mul_nonneg (mul_nonneg (show (0 : ℤ) ≤ n3 - 5 by linarith) (show (0 : ℤ) ≤ n4 - 5 by linarith))
        (show (0 : ℤ) ≤ n5 * n6 - e5 by nlinarith),
      mul_nonneg (show (0 : ℤ) ≤ n3 - 5 by linarith) (show (0 : ℤ) ≤ n5 * n6 - e5 by nlinarith),
      mul_nonneg (show (0 : ℤ) ≤ n4 - 5 by linarith) (show (0 : ℤ) ≤ n5 * n6 - e5 by nlinarith),
      mul_nonneg (show (0 : ℤ) ≤ n3 - 5 by linarith)
        (mul_nonneg (show (0 : ℤ) ≤ n5 - e4 by linarith) (show (0 : ℤ) ≤ n6 by linarith)),
      mul_nonneg (show (0 : ℤ) ≤ n5 - e5 by linarith) (show (0 : ℤ) ≤ n3 * n4 - n4 by nlinarith)]
  have k1 : (T1' - T1) * (n4 * n5 * n6 - e4 * n6 - n4 * e5 + T4)
      ≤ (e1' - e1) * (n4 * n5 * n6 - e4 * n6 - n4 * e5 + T4) :=
    mul_le_mul_of_nonneg_right (by linarith) hC
  have k2 : (e1' - e1) * (n4 * n5 * n6 - e4 * n6 - n4 * e5 + T4)
      ≤ (e1' - e1) * (n3 * n4 * n5 * n6 - e3 * n5 * n6 - n3 * e4 * n6 - n3 * n4 * e5 + T3 * n6
        + e3 * e5 + n3 * T4 - min T3 T4) := mul_le_mul_of_nonneg_left hkey (by linarith)
  linarith

theorem anti_e2 {e1 e2 e2' e3 e4 e5 : ℤ} (h : e2 ≤ e2') (he1 : e1 ≤ n1)
    (he4 : e4 ≤ n5) (he5 : e5 ≤ n5) (he5' : e5 ≤ n6) :
    N6g n1 n2 n3 n4 n5 n6 e1 e2' e3 e4 e5 ≤ N6g n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 := by
  unfold N6g
  set T1 := max 0 (e1 + e2 - n2)
  set T1' := max 0 (e1 + e2' - n2)
  set T2 := max 0 (e2 + e3 - n3)
  set T2' := max 0 (e2' + e3 - n3)
  set T3 := max 0 (e3 + e4 - n4)
  set T4 := max 0 (e4 + e5 - n5)
  have hT1 := max0_lip (u := e1 + e2 - n2) (u' := e1 + e2' - n2) (by linarith)
  have hT2 := max0_lip (u := e2 + e3 - n3) (u' := e2' + e3 - n3) (by linarith)
  have hT4 : 0 ≤ T4 := le_max_left _ _
  have u1 := up_t1 hn1 hn2 hn3 hn4 hn5 hn6 he1 he5' (e2 := e2') (e3 := e3) (e4 := e4)
    (t2 := T2') (t3 := T3) (t4 := T4) (show T1 ≤ T1' by linarith)
  have u2 := up_t2 hn1 hn2 hn3 hn4 hn5 hn6 he1 he5' (e2 := e2') (e3 := e3) (e4 := e4)
    (t1 := T1) (t3 := T3) (t4 := T4) (show T2 ≤ T2' by linarith)
  have d2 := dir_e2 n1 n2 n3 n4 n5 n6 e1 e2 e2' e3 e4 e5 T1 T2 T3 T4
  have hC : 0 ≤ n4 * n5 * n6 - e4 * n6 - n4 * e5 + T4 := by
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ n5 - e4 by linarith) (show (0 : ℤ) ≤ n6 by linarith),
      mul_nonneg (show (0 : ℤ) ≤ n5 - e5 by linarith) (show (0 : ℤ) ≤ n4 by linarith),
      mul_nonneg (mul_nonneg (show (0 : ℤ) ≤ n4 - 2 by linarith) (show (0 : ℤ) ≤ n5 by linarith))
        (show (0 : ℤ) ≤ n6 - 2 by linarith)]
  have hN : 0 ≤ n1 * (n5 * n6 - e5) + 1 := by
    have : 0 ≤ n5 * n6 - e5 := by nlinarith
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ n1 by linarith) this]
  have hkey : n4 * n5 * n6 - e4 * n6 - n4 * e5 + T4 + (n1 * (n5 * n6 - e5) + 1)
      ≤ n1 * (n4 * n5 * n6 - e4 * n6 - n4 * e5 + T4) := by
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ n1 - 5 by linarith) (show (0 : ℤ) ≤ n4 - 5 by linarith),
      mul_nonneg (show (0 : ℤ) ≤ n5 - e4 by linarith) (show (0 : ℤ) ≤ n6 by linarith),
      mul_nonneg (show (0 : ℤ) ≤ n1 - 1 by linarith) hT4,
      mul_nonneg (mul_nonneg (show (0 : ℤ) ≤ n1 - 5 by linarith) (show (0 : ℤ) ≤ n4 - 5 by linarith))
        (show (0 : ℤ) ≤ n5 * n6 - e5 by nlinarith),
      mul_nonneg (show (0 : ℤ) ≤ n1 - 5 by linarith) (show (0 : ℤ) ≤ n5 * n6 - e5 by nlinarith),
      mul_nonneg (show (0 : ℤ) ≤ n4 - 5 by linarith) (show (0 : ℤ) ≤ n5 * n6 - e5 by nlinarith),
      mul_nonneg (show (0 : ℤ) ≤ n1 - 5 by linarith)
        (mul_nonneg (show (0 : ℤ) ≤ n5 - e4 by linarith) (show (0 : ℤ) ≤ n6 by linarith)),
      mul_nonneg (show (0 : ℤ) ≤ n5 - e5 by linarith) (show (0 : ℤ) ≤ n6 - 1 by linarith),
      mul_nonneg (show (0 : ℤ) ≤ n5 - 5 by linarith) (show (0 : ℤ) ≤ n6 - 5 by linarith)]
  have k1 : (T1' - T1) * (n4 * n5 * n6 - e4 * n6 - n4 * e5 + T4)
      ≤ (e2' - e2) * (n4 * n5 * n6 - e4 * n6 - n4 * e5 + T4) :=
    mul_le_mul_of_nonneg_right (by linarith) hC
  have k2 : (T2' - T2) * (n1 * (n5 * n6 - e5) + 1) ≤ (e2' - e2) * (n1 * (n5 * n6 - e5) + 1) :=
    mul_le_mul_of_nonneg_right (by linarith) hN
  have k3 := mul_le_mul_of_nonneg_left hkey (show (0 : ℤ) ≤ e2' - e2 by linarith)
  linarith

theorem anti_e3 {e1 e2 e3 e3' e4 e5 : ℤ} (h : e3 ≤ e3') (he1 : e1 ≤ n1) (he1' : e1 ≤ n2)
    (he5 : e5 ≤ n5) (he5' : e5 ≤ n6) :
    N6g n1 n2 n3 n4 n5 n6 e1 e2 e3' e4 e5 ≤ N6g n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 := by
  unfold N6g
  set T1 := max 0 (e1 + e2 - n2)
  set T2 := max 0 (e2 + e3 - n3)
  set T2' := max 0 (e2 + e3' - n3)
  set T3 := max 0 (e3 + e4 - n4)
  set T3' := max 0 (e3' + e4 - n4)
  set T4 := max 0 (e4 + e5 - n5)
  have hT2 := max0_lip (u := e2 + e3 - n3) (u' := e2 + e3' - n3) (by linarith)
  have hT3 := max0_lip (u := e3 + e4 - n4) (u' := e3' + e4 - n4) (by linarith)
  have u2 := up_t2 hn1 hn2 hn3 hn4 hn5 hn6 he1 he5' (e2 := e2) (e3 := e3') (e4 := e4)
    (t1 := T1) (t3 := T3') (t4 := T4) (show T2 ≤ T2' by linarith)
  have u3 := up_t3 hn1 hn2 hn3 hn4 hn5 hn6 he1 he5' (e2 := e2) (e3 := e3') (e4 := e4)
    (t1 := T1) (t2 := T2) (t4 := T4) (show T3 ≤ T3' by linarith)
  have d3 := dir_e3 n1 n2 n3 n4 n5 n6 e1 e2 e3 e3' e4 e5 T1 T2 T3 T4
  have hA : 0 ≤ n1 * (n5 * n6 - e5) + 1 := by
    have : 0 ≤ n5 * n6 - e5 := by nlinarith
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ n1 by linarith) this]
  have hB : 0 ≤ n6 * (n1 * n2 - e1) + 1 := by
    have : 0 ≤ n1 * n2 - e1 := by nlinarith
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ n6 by linarith) this]
  have hkey : n1 * (n5 * n6 - e5) + 1 + (n6 * (n1 * n2 - e1) + 1)
      ≤ (n1 * n2 - e1) * (n5 * n6 - e5) := by
    have a1 : 4 * n1 ≤ n1 * n2 - e1 := by nlinarith
    have a2 : 4 * n6 ≤ n5 * n6 - e5 := by nlinarith
    nlinarith [mul_le_mul a1 a2 (by linarith) (by linarith),
      mul_nonneg (show (0 : ℤ) ≤ n1 * n2 - e1 - 4 * n1 by linarith)
        (show (0 : ℤ) ≤ n5 * n6 - e5 - 4 * n6 by linarith)]
  have k1 : (T2' - T2) * (n1 * (n5 * n6 - e5) + 1) ≤ (e3' - e3) * (n1 * (n5 * n6 - e5) + 1) :=
    mul_le_mul_of_nonneg_right (by linarith) hA
  have k2 : (T3' - T3) * (n6 * (n1 * n2 - e1) + 1) ≤ (e3' - e3) * (n6 * (n1 * n2 - e1) + 1) :=
    mul_le_mul_of_nonneg_right (by linarith) hB
  have k3 := mul_le_mul_of_nonneg_left hkey (show (0 : ℤ) ≤ e3' - e3 by linarith)
  linarith

theorem anti_e4 {e1 e2 e3 e4 e4' e5 : ℤ} (h : e4 ≤ e4') (he1 : e1 ≤ n1) (he1' : e1 ≤ n2)
    (he2 : e2 ≤ n2) (he5 : e5 ≤ n6) :
    N6g n1 n2 n3 n4 n5 n6 e1 e2 e3 e4' e5 ≤ N6g n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 := by
  unfold N6g
  set T1 := max 0 (e1 + e2 - n2)
  set T2 := max 0 (e2 + e3 - n3)
  set T3 := max 0 (e3 + e4 - n4)
  set T3' := max 0 (e3 + e4' - n4)
  set T4 := max 0 (e4 + e5 - n5)
  set T4' := max 0 (e4' + e5 - n5)
  have hT3 := max0_lip (u := e3 + e4 - n4) (u' := e3 + e4' - n4) (by linarith)
  have hT4 := max0_lip (u := e4 + e5 - n5) (u' := e4' + e5 - n5) (by linarith)
  have hT1 : 0 ≤ T1 := le_max_left _ _
  have u3 := up_t3 hn1 hn2 hn3 hn4 hn5 hn6 he1 he5 (e2 := e2) (e3 := e3) (e4 := e4')
    (t1 := T1) (t2 := T2) (t4 := T4') (show T3 ≤ T3' by linarith)
  have u4 := up_t4 hn1 hn2 hn3 hn4 hn5 hn6 he1 he5 (e2 := e2) (e3 := e3) (e4 := e4')
    (t1 := T1) (t2 := T2) (t3 := T3) (show T4 ≤ T4' by linarith)
  have d4 := dir_e4 n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e4' e5 T1 T2 T3 T4
  have hC : 0 ≤ n1 * n2 * n3 - e1 * n3 - n1 * e2 + T1 := by
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ n2 - e1 by linarith) (show (0 : ℤ) ≤ n3 by linarith),
      mul_nonneg (show (0 : ℤ) ≤ n2 - e2 by linarith) (show (0 : ℤ) ≤ n1 by linarith),
      mul_nonneg (mul_nonneg (show (0 : ℤ) ≤ n1 - 2 by linarith) (show (0 : ℤ) ≤ n2 by linarith))
        (show (0 : ℤ) ≤ n3 - 2 by linarith)]
  have hN : 0 ≤ n6 * (n1 * n2 - e1) + 1 := by
    have : 0 ≤ n1 * n2 - e1 := by nlinarith
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ n6 by linarith) this]
  have hkey : n6 * (n1 * n2 - e1) + 1 + (n1 * n2 * n3 - e1 * n3 - n1 * e2 + T1)
      ≤ n6 * (n1 * n2 * n3 - e1 * n3 - n1 * e2 + T1) := by
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ n6 - 5 by linarith) (show (0 : ℤ) ≤ n3 - 5 by linarith),
      mul_nonneg (show (0 : ℤ) ≤ n2 - e2 by linarith) (show (0 : ℤ) ≤ n1 by linarith),
      mul_nonneg (show (0 : ℤ) ≤ n6 - 1 by linarith) hT1,
      mul_nonneg (mul_nonneg (show (0 : ℤ) ≤ n6 - 5 by linarith) (show (0 : ℤ) ≤ n3 - 5 by linarith))
        (show (0 : ℤ) ≤ n1 * n2 - e1 by nlinarith),
      mul_nonneg (show (0 : ℤ) ≤ n6 - 5 by linarith) (show (0 : ℤ) ≤ n1 * n2 - e1 by nlinarith),
      mul_nonneg (show (0 : ℤ) ≤ n3 - 5 by linarith) (show (0 : ℤ) ≤ n1 * n2 - e1 by nlinarith),
      mul_nonneg (show (0 : ℤ) ≤ n6 - 5 by linarith)
        (mul_nonneg (show (0 : ℤ) ≤ n2 - e2 by linarith) (show (0 : ℤ) ≤ n1 by linarith)),
      mul_nonneg (show (0 : ℤ) ≤ n2 - e1 by linarith) (show (0 : ℤ) ≤ n1 - 1 by linarith),
      mul_nonneg (show (0 : ℤ) ≤ n1 - 5 by linarith) (show (0 : ℤ) ≤ n2 - 5 by linarith)]
  have k1 : (T3' - T3) * (n6 * (n1 * n2 - e1) + 1) ≤ (e4' - e4) * (n6 * (n1 * n2 - e1) + 1) :=
    mul_le_mul_of_nonneg_right (by linarith) hN
  have k2 : (T4' - T4) * (n1 * n2 * n3 - e1 * n3 - n1 * e2 + T1)
      ≤ (e4' - e4) * (n1 * n2 * n3 - e1 * n3 - n1 * e2 + T1) :=
    mul_le_mul_of_nonneg_right (by linarith) hC
  have k3 := mul_le_mul_of_nonneg_left hkey (show (0 : ℤ) ≤ e4' - e4 by linarith)
  linarith

theorem anti_e5 {e1 e2 e3 e4 e5 e5' : ℤ} (h : e5 ≤ e5') (he1 : e1 ≤ n1) (he1' : e1 ≤ n2)
    (he2 : e2 ≤ n2) (he3 : e3 ≤ n3) (he5 : e5' ≤ n6) :
    N6g n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5' ≤ N6g n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 := by
  unfold N6g
  set T1 := max 0 (e1 + e2 - n2)
  set T2 := max 0 (e2 + e3 - n3)
  set T3 := max 0 (e3 + e4 - n4)
  set T4 := max 0 (e4 + e5 - n5)
  set T4' := max 0 (e4 + e5' - n5)
  have hT := max0_lip (u := e4 + e5 - n5) (u' := e4 + e5' - n5) (by linarith)
  have hT1 : 0 ≤ T1 := le_max_left _ _
  have hT2 : 0 ≤ T2 := le_max_left _ _
  have u4 := up_t4 hn1 hn2 hn3 hn4 hn5 hn6 he1 he5 (e2 := e2) (e3 := e3) (e4 := e4)
    (t1 := T1) (t2 := T2) (t3 := T3) (show T4 ≤ T4' by linarith)
  have d5 := dir_e5 n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 e5' T1 T2 T3 T4
  have hm : min T1 T2 ≤ T2 := min_le_right _ _
  have hC : 0 ≤ n1 * n2 * n3 - e1 * n3 - n1 * e2 + T1 := by
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ n2 - e1 by linarith) (show (0 : ℤ) ≤ n3 by linarith),
      mul_nonneg (show (0 : ℤ) ≤ n2 - e2 by linarith) (show (0 : ℤ) ≤ n1 by linarith),
      mul_nonneg (mul_nonneg (show (0 : ℤ) ≤ n1 - 2 by linarith) (show (0 : ℤ) ≤ n2 by linarith))
        (show (0 : ℤ) ≤ n3 - 2 by linarith)]
  have hkey : n1 * n2 * n3 - e1 * n3 - n1 * e2 + T1 ≤ n1 * n2 * n3 * n4 - e1 * n3 * n4
      - n1 * e2 * n4 - n1 * n2 * e3 + T1 * n4 + e1 * e3 + n1 * T2 - min T1 T2 := by
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ n4 - 5 by linarith) (show (0 : ℤ) ≤ n3 - 5 by linarith),
      mul_nonneg (show (0 : ℤ) ≤ n3 - e3 by linarith) (show (0 : ℤ) ≤ n1 * n2 - e1 by nlinarith),
      mul_nonneg (show (0 : ℤ) ≤ n2 - e2 by linarith) (show (0 : ℤ) ≤ n1 by linarith),
      mul_nonneg (show (0 : ℤ) ≤ n4 - 1 by linarith) hT1,
      mul_nonneg hT2 (show (0 : ℤ) ≤ n1 - 1 by linarith),
      mul_nonneg (mul_nonneg (show (0 : ℤ) ≤ n4 - 5 by linarith) (show (0 : ℤ) ≤ n3 - 5 by linarith))
        (show (0 : ℤ) ≤ n1 * n2 - e1 by nlinarith),
      mul_nonneg (show (0 : ℤ) ≤ n4 - 5 by linarith) (show (0 : ℤ) ≤ n1 * n2 - e1 by nlinarith),
      mul_nonneg (show (0 : ℤ) ≤ n3 - 5 by linarith) (show (0 : ℤ) ≤ n1 * n2 - e1 by nlinarith),
      mul_nonneg (show (0 : ℤ) ≤ n4 - 5 by linarith)
        (mul_nonneg (show (0 : ℤ) ≤ n2 - e2 by linarith) (show (0 : ℤ) ≤ n1 by linarith)),
      mul_nonneg (show (0 : ℤ) ≤ n2 - e1 by linarith) (show (0 : ℤ) ≤ n3 * n4 - n3 by nlinarith)]
  have k1 : (T4' - T4) * (n1 * n2 * n3 - e1 * n3 - n1 * e2 + T1)
      ≤ (e5' - e5) * (n1 * n2 * n3 - e1 * n3 - n1 * e2 + T1) :=
    mul_le_mul_of_nonneg_right (by linarith) hC
  have k2 := mul_le_mul_of_nonneg_left hkey (show (0 : ℤ) ≤ e5' - e5 by linarith)
  linarith

/-- **The greedy value is antitone in the consecutive intersections.** -/
theorem N6g_anti {e1 e2 e3 e4 e5 e1' e2' e3' e4' e5' : ℤ} (h1 : e1 ≤ e1') (h2 : e2 ≤ e2')
    (h3 : e3 ≤ e3') (h4 : e4 ≤ e4') (h5 : e5 ≤ e5')
    (g1 : e1' ≤ n1) (g1' : e1' ≤ n2) (g2 : e2' ≤ n2) (g3 : e3' ≤ n3) (g3' : e3' ≤ n4)
    (g4 : e4' ≤ n5) (g5 : e5' ≤ n5) (g5' : e5' ≤ n6) :
    N6g n1 n2 n3 n4 n5 n6 e1' e2' e3' e4' e5' ≤ N6g n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 := by
  have s1 := anti_e1 hn1 hn2 hn3 hn4 hn5 hn6 (e2 := e2) (e3 := e3) (e4 := e4) (e5 := e5) h1 g1
    (by linarith) (by linarith) (by linarith) (by linarith)
  have s2 := anti_e2 hn1 hn2 hn3 hn4 hn5 hn6 (e1 := e1') (e3 := e3) (e4 := e4) (e5 := e5) h2 g1
    (by linarith) (by linarith) (by linarith)
  have s3 := anti_e3 hn1 hn2 hn3 hn4 hn5 hn6 (e1 := e1') (e2 := e2') (e4 := e4) (e5 := e5) h3 g1
    g1' (by linarith) (by linarith)
  have s4 := anti_e4 hn1 hn2 hn3 hn4 hn5 hn6 (e1 := e1') (e2 := e2') (e3 := e3') (e5 := e5) h4 g1
    g1' g2 (by linarith)
  have s5 := anti_e5 hn1 hn2 hn3 hn4 hn5 hn6 (e1 := e1') (e2 := e2') (e3 := e3') (e4 := e4') h5 g1
    g1' g2 g3 g5'
  linarith

end anti

end GridGen.Six
