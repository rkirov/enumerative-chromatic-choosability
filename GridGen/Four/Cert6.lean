/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.Seam6
import GridGen.Four.Cert

/-!
# Height four, `k = 6`: the capped certificate away from the small mismatches

The capped certificate `F6cap` holds at every integer mismatch triple `(μ₂, μ₃, μ₄) ∈ [0,6]³`
except `(0,0,0)` and sixteen small ones (`Small6`), which are treated exactly. Each of the 326
points is a rational inequality checked by `norm_num`, after bounding the main logarithms below by
`x - x²/2` and the chord slope `zslope` above through `log (1 + y) ≤ y - y²/2 + y³/3`; the
smallest value is about `1.6·10⁻³`, at `(1,2,1)`.
-/

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace GridGen.Four

open Real

/-- The third-order upper bound for the logarithm near `1`. -/
theorem log_le_cubic {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1 / 5) :
    log (1 + y) ≤ y - y ^ 2 / 2 + y ^ 3 / 3 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -y)
    (by rw [abs_neg, abs_of_nonneg h0]; linarith) 4
  have e : ∑ i ∈ Finset.range 4, (-y) ^ (i + 1) / ((i : ℝ) + 1)
      = -y + y ^ 2 / 2 - y ^ 3 / 3 + y ^ 4 / 4 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num; ring
  rw [e, sub_neg_eq_add, abs_neg, abs_of_nonneg h0] at h
  have h2 := (abs_le.mp h).2
  have h3 : y ^ (4 + 1) / (1 - y) ≤ y ^ 4 / 4 := by
    rw [div_le_iff₀ (by linarith)]
    have := pow_nonneg h0 4
    nlinarith
  linarith

/-- The rational upper bound for the chord slope. -/
noncomputable def zsU (n μ : ℝ) : ℝ :=
  min (1 / (n * (n - 1)))
    ((2 / (n ^ 2 - n + 1 + μ - 2) - (2 / (n ^ 2 - n + 1 + μ - 2)) ^ 2 / 2
      + (2 / (n ^ 2 - n + 1 + μ - 2)) ^ 3 / 3) / 2)

theorem zslope_le_zsU {μ : ℝ} (hμ : 0 ≤ μ) :
    zslope (((6 : ℕ) : ℝ) - 1) μ ≤ zsU (((6 : ℕ) : ℝ) - 1) μ := by
  unfold zslope zsU
  refine min_le_min le_rfl (div_le_div_of_nonneg_right ?_ zero_le_two)
  have hD : (0 : ℝ) < (((6 : ℕ) : ℝ) - 1) ^ 2 - (((6 : ℕ) : ℝ) - 1) + 1 + μ - 2 := by
    norm_num; linarith
  have e : ((((6 : ℕ) : ℝ) - 1) ^ 2 - (((6 : ℕ) : ℝ) - 1) + 1 + μ)
      / ((((6 : ℕ) : ℝ) - 1) ^ 2 - (((6 : ℕ) : ℝ) - 1) + 1 + μ - 2)
      = 1 + 2 / ((((6 : ℕ) : ℝ) - 1) ^ 2 - (((6 : ℕ) : ℝ) - 1) + 1 + μ - 2) := by
    rw [one_add_div hD.ne']; congr 1; ring
  rw [e]
  refine log_le_cubic (div_nonneg zero_le_two hD.le) ?_
  rw [div_le_iff₀ hD]; norm_num; linarith

/-- The rational lower bound for `F6cap`. -/
noncomputable def F6g (a b c : ℝ) : ℝ :=
  let n : ℝ := ((6 : ℕ) : ℝ) - 1
  (a / kA n - a ^ 2 / (2 * kA n ^ 2)) + (b / kA n - b ^ 2 / (2 * kA n ^ 2))
    + (c / kA n - c ^ 2 / (2 * kA n ^ 2))
    - (zsU n a * (min (qe6 * a) 1 + min (qm6 * a) 1) + zsU n b * (2 * min (qm6 * b) 1)
      + zsU n c * (min (qm6 * c) 1 + min (qe6 * c) 1))
    - J3 a b * ((a + 1) * min (b + 1) (n + 3 - a) / (n ^ 2 * (n - 1) ^ 2) + ku3 n * qe6)
    - J4 a b c * ((min ((b + 1) * (c + 1)) ((n + 3 - b) * (n + 3 - c)) + (c + 1))
        / (n * (n - 1) ^ 3) + ku4e n * qe6 + ku4b n)
    - 209 / 14123

theorem F6g_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    F6g a b c ≤ F6cap a b c := by
  have hA : 0 < kA (((6 : ℕ) : ℝ) - 1) := by unfold kA; norm_num
  have l2 := log_quad ha hA
  have l3 := log_quad hb hA
  have l4 := log_quad hc hA
  have mn : ∀ {q x : ℝ}, 0 ≤ q → 0 ≤ x → 0 ≤ min (q * x) 1 := fun hq hx =>
    le_min (mul_nonneg hq hx) zero_le_one
  have hq : (0 : ℝ) ≤ qm6 := by unfold qm6; norm_num
  have hqe : (0 : ℝ) ≤ qe6 := by unfold qe6; norm_num
  have s2 := mul_le_mul_of_nonneg_right (zslope_le_zsU ha)
    (add_nonneg (mn hqe ha) (mn hq ha))
  have s3 : zslope (((6 : ℕ) : ℝ) - 1) b * (2 * min (qm6 * b) 1)
      ≤ zsU (((6 : ℕ) : ℝ) - 1) b * (2 * min (qm6 * b) 1) :=
    mul_le_mul_of_nonneg_right (zslope_le_zsU hb) (mul_nonneg zero_le_two (mn hq hb))
  have s4 := mul_le_mul_of_nonneg_right (zslope_le_zsU hc)
    (add_nonneg (mn hq hc) (mn hqe hc))
  have e : F6cap a b c - F6g a b c
      = (log (1 + a / kA (((6 : ℕ) : ℝ) - 1))
          - (a / kA (((6 : ℕ) : ℝ) - 1) - a ^ 2 / (2 * kA (((6 : ℕ) : ℝ) - 1) ^ 2)))
        + (log (1 + b / kA (((6 : ℕ) : ℝ) - 1))
          - (b / kA (((6 : ℕ) : ℝ) - 1) - b ^ 2 / (2 * kA (((6 : ℕ) : ℝ) - 1) ^ 2)))
        + (log (1 + c / kA (((6 : ℕ) : ℝ) - 1))
          - (c / kA (((6 : ℕ) : ℝ) - 1) - c ^ 2 / (2 * kA (((6 : ℕ) : ℝ) - 1) ^ 2)))
        + (zsU (((6 : ℕ) : ℝ) - 1) a * (min (qe6 * a) 1 + min (qm6 * a) 1)
          - zslope (((6 : ℕ) : ℝ) - 1) a * (min (qe6 * a) 1 + min (qm6 * a) 1))
        + (zsU (((6 : ℕ) : ℝ) - 1) b * (2 * min (qm6 * b) 1)
          - zslope (((6 : ℕ) : ℝ) - 1) b * (2 * min (qm6 * b) 1))
        + (zsU (((6 : ℕ) : ℝ) - 1) c * (min (qm6 * c) 1 + min (qe6 * c) 1)
          - zslope (((6 : ℕ) : ℝ) - 1) c * (min (qm6 * c) 1 + min (qe6 * c) 1)) := by
    unfold F6g F6cap F6core
    ring
  rw [← sub_nonneg, e]
  exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (sub_nonneg.2 l2)
    (sub_nonneg.2 l3)) (sub_nonneg.2 l4)) (sub_nonneg.2 s2)) (sub_nonneg.2 s3)) (sub_nonneg.2 s4)

/-- The mismatch triples treated exactly (with `(0,0,0)`, where `F6val` vanishes). -/
def small6 : List (ℕ × ℕ × ℕ) :=
  [(0, 0, 0), (0, 0, 1), (0, 0, 2), (0, 1, 0), (0, 1, 1), (0, 1, 2), (0, 2, 0), (0, 2, 1),
    (0, 2, 2), (0, 3, 0), (0, 3, 1), (1, 0, 0), (1, 0, 1), (1, 1, 0), (1, 1, 1), (1, 2, 0),
    (2, 0, 0)]

def Small6 (a b c : ℕ) : Prop := (a, b, c) ∈ small6

instance (a b c : ℕ) : Decidable (Small6 a b c) := by unfold Small6; infer_instance

set_option maxHeartbeats 4000000 in
theorem cert6_0 {b c : ℕ} (hb : b ≤ 6) (hc : c ≤ 6) (hs : ¬ Small6 0 b c) :
    0 ≤ F6cap ((0 : ℕ) : ℝ) b c := by
  refine le_trans ?_ (F6g_le (Nat.cast_nonneg _) (Nat.cast_nonneg b) (Nat.cast_nonneg c))
  interval_cases b <;> interval_cases c <;>
    first
    | (exfalso; exact hs (by decide))
    | norm_num [F6g, zsU, J3, J4, kA, kt, ku3, ku4e, ku4b, qm6, qe6, min_def]

set_option maxHeartbeats 4000000 in
theorem cert6_1 {b c : ℕ} (hb : b ≤ 6) (hc : c ≤ 6) (hs : ¬ Small6 1 b c) :
    0 ≤ F6cap ((1 : ℕ) : ℝ) b c := by
  refine le_trans ?_ (F6g_le (Nat.cast_nonneg _) (Nat.cast_nonneg b) (Nat.cast_nonneg c))
  interval_cases b <;> interval_cases c <;>
    first
    | (exfalso; exact hs (by decide))
    | norm_num [F6g, zsU, J3, J4, kA, kt, ku3, ku4e, ku4b, qm6, qe6, min_def]

set_option maxHeartbeats 4000000 in
theorem cert6_2 {b c : ℕ} (hb : b ≤ 6) (hc : c ≤ 6) (hs : ¬ Small6 2 b c) :
    0 ≤ F6cap ((2 : ℕ) : ℝ) b c := by
  refine le_trans ?_ (F6g_le (Nat.cast_nonneg _) (Nat.cast_nonneg b) (Nat.cast_nonneg c))
  interval_cases b <;> interval_cases c <;>
    first
    | (exfalso; exact hs (by decide))
    | norm_num [F6g, zsU, J3, J4, kA, kt, ku3, ku4e, ku4b, qm6, qe6, min_def]

set_option maxHeartbeats 4000000 in
theorem cert6_3 {b c : ℕ} (hb : b ≤ 6) (hc : c ≤ 6) (hs : ¬ Small6 3 b c) :
    0 ≤ F6cap ((3 : ℕ) : ℝ) b c := by
  refine le_trans ?_ (F6g_le (Nat.cast_nonneg _) (Nat.cast_nonneg b) (Nat.cast_nonneg c))
  interval_cases b <;> interval_cases c <;>
    first
    | (exfalso; exact hs (by decide))
    | norm_num [F6g, zsU, J3, J4, kA, kt, ku3, ku4e, ku4b, qm6, qe6, min_def]

set_option maxHeartbeats 4000000 in
theorem cert6_4 {b c : ℕ} (hb : b ≤ 6) (hc : c ≤ 6) (hs : ¬ Small6 4 b c) :
    0 ≤ F6cap ((4 : ℕ) : ℝ) b c := by
  refine le_trans ?_ (F6g_le (Nat.cast_nonneg _) (Nat.cast_nonneg b) (Nat.cast_nonneg c))
  interval_cases b <;> interval_cases c <;>
    first
    | (exfalso; exact hs (by decide))
    | norm_num [F6g, zsU, J3, J4, kA, kt, ku3, ku4e, ku4b, qm6, qe6, min_def]

set_option maxHeartbeats 4000000 in
theorem cert6_5 {b c : ℕ} (hb : b ≤ 6) (hc : c ≤ 6) (hs : ¬ Small6 5 b c) :
    0 ≤ F6cap ((5 : ℕ) : ℝ) b c := by
  refine le_trans ?_ (F6g_le (Nat.cast_nonneg _) (Nat.cast_nonneg b) (Nat.cast_nonneg c))
  interval_cases b <;> interval_cases c <;>
    first
    | (exfalso; exact hs (by decide))
    | norm_num [F6g, zsU, J3, J4, kA, kt, ku3, ku4e, ku4b, qm6, qe6, min_def]

set_option maxHeartbeats 4000000 in
theorem cert6_6 {b c : ℕ} (hb : b ≤ 6) (hc : c ≤ 6) (hs : ¬ Small6 6 b c) :
    0 ≤ F6cap ((6 : ℕ) : ℝ) b c := by
  refine le_trans ?_ (F6g_le (Nat.cast_nonneg _) (Nat.cast_nonneg b) (Nat.cast_nonneg c))
  interval_cases b <;> interval_cases c <;>
    first
    | (exfalso; exact hs (by decide))
    | norm_num [F6g, zsU, J3, J4, kA, kt, ku3, ku4e, ku4b, qm6, qe6, min_def]

/-- **The capped certificate at `k = 6`.** -/
theorem cert6 {a b c : ℕ} (ha : a ≤ 6) (hb : b ≤ 6) (hc : c ≤ 6) (hs : ¬ Small6 a b c) :
    0 ≤ F6cap a b c := by
  interval_cases a
  · exact cert6_0 hb hc hs
  · exact cert6_1 hb hc hs
  · exact cert6_2 hb hc hs
  · exact cert6_3 hb hc hs
  · exact cert6_4 hb hc hs
  · exact cert6_5 hb hc hs
  · exact cert6_6 hb hc hs

end GridGen.Four
