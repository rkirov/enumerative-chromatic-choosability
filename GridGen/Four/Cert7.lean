/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.Seam

/-!
# Height four, `k = 7`: the capped certificate away from the five smallest mismatches

At `k = 7` the uncapped certificate `Fval` fails, but with the pattern term capped at `(1-ρ)/ρ`
(`Fcap`) it holds at every integer mismatch triple `(μ₂, μ₃, μ₄) ∈ [0,7]³` except `(0,0,0)` and
the five smallest, `(0,1,0)`, `(1,0,0)`, `(0,0,1)`, `(0,1,1)`, `(0,2,0)`, which `GridGen/Four/Small7*`
treat exactly. Each of the 506 points is a rational inequality checked by `norm_num`; the
smallest value is about `3.6·10⁻⁴`, at `(1,1,0)`.
-/

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace GridGen.Four

open Real

/-- The polynomial lower bound for `Fcap`, with the indicators as parameters. -/
noncomputable def Fgc (A n q u3 u4e u4b cp j3 j4 a b c : ℝ) : ℝ :=
  (a / A - a ^ 2 / (2 * A ^ 2)) + (b / A - b ^ 2 / (2 * A ^ 2)) + (c / A - c ^ 2 / (2 * A ^ 2))
    - 2 * q * (a + b + c) / (n * (n - 1))
    - j3 * ((a + 1) * (b + 1) / (n ^ 2 * (n - 1) ^ 2) + u3 * q)
    - j4 * ((b + 2) * (c + 1) / (n * (n - 1) ^ 3) + u4e * q + u4b)
    - cp

theorem Fcap_ge_Fgc {k : ℕ} (hk : 7 ≤ k) {μ2 μ3 μ4 : ℝ} (p2 : 0 ≤ μ2) (p3 : 0 ≤ μ3)
    (p4 : 0 ≤ μ4) :
    Fgc (kA ((k : ℝ) - 1)) ((k : ℝ) - 1) (qk k) (ku3 ((k : ℝ) - 1)) (ku4e ((k : ℝ) - 1))
        (ku4b ((k : ℝ) - 1)) ((1 - rho k) / rho k) (J3 μ2 μ3) (J4 μ2 μ3 μ4) μ2 μ3 μ4
      ≤ Fcap k μ2 μ3 μ4 := by
  have hk' : (7 : ℝ) ≤ k := by exact_mod_cast hk
  have hA : 0 < kA ((k : ℝ) - 1) := by unfold kA; nlinarith
  have l2 := log_quad p2 hA
  have l3 := log_quad p3 hA
  have l4 := log_quad p4 hA
  unfold Fcap Fgc
  linarith

/-- The excluded mismatch triples. -/
def Small7 (a b c : ℕ) : Prop :=
  (a = 0 ∧ b = 0 ∧ c = 0) ∨ (a = 0 ∧ b = 1 ∧ c = 0) ∨ (a = 1 ∧ b = 0 ∧ c = 0) ∨
    (a = 0 ∧ b = 0 ∧ c = 1) ∨ (a = 0 ∧ b = 1 ∧ c = 1) ∨ (a = 0 ∧ b = 2 ∧ c = 0)

set_option maxHeartbeats 1000000 in
theorem cert7_0 {b c : ℕ} (hb : b ≤ 7) (hc : c ≤ 7) (hs : ¬ Small7 0 b c) :
    0 ≤ Fcap 7 (0 : ℕ) b c := by
  refine le_trans ?_ (Fcap_ge_Fgc le_rfl (Nat.cast_nonneg _) (Nat.cast_nonneg b)
    (Nat.cast_nonneg c))
  unfold Small7 at hs
  interval_cases b <;> interval_cases c <;>
    first
    | (exfalso; exact hs (by decide))
    | norm_num [Fgc, J3, J4, kA, kt, ku3, ku4e, ku4b, qk, rho]

set_option maxHeartbeats 1000000 in
theorem cert7_1 {b c : ℕ} (hb : b ≤ 7) (hc : c ≤ 7) (hs : ¬ Small7 1 b c) :
    0 ≤ Fcap 7 (1 : ℕ) b c := by
  refine le_trans ?_ (Fcap_ge_Fgc le_rfl (Nat.cast_nonneg _) (Nat.cast_nonneg b)
    (Nat.cast_nonneg c))
  unfold Small7 at hs
  interval_cases b <;> interval_cases c <;>
    first
    | (exfalso; exact hs (by decide))
    | norm_num [Fgc, J3, J4, kA, kt, ku3, ku4e, ku4b, qk, rho]

set_option maxHeartbeats 1000000 in
theorem cert7_2 {b c : ℕ} (hb : b ≤ 7) (hc : c ≤ 7) (hs : ¬ Small7 2 b c) :
    0 ≤ Fcap 7 (2 : ℕ) b c := by
  refine le_trans ?_ (Fcap_ge_Fgc le_rfl (Nat.cast_nonneg _) (Nat.cast_nonneg b)
    (Nat.cast_nonneg c))
  unfold Small7 at hs
  interval_cases b <;> interval_cases c <;>
    first
    | (exfalso; exact hs (by decide))
    | norm_num [Fgc, J3, J4, kA, kt, ku3, ku4e, ku4b, qk, rho]

set_option maxHeartbeats 1000000 in
theorem cert7_3 {b c : ℕ} (hb : b ≤ 7) (hc : c ≤ 7) (hs : ¬ Small7 3 b c) :
    0 ≤ Fcap 7 (3 : ℕ) b c := by
  refine le_trans ?_ (Fcap_ge_Fgc le_rfl (Nat.cast_nonneg _) (Nat.cast_nonneg b)
    (Nat.cast_nonneg c))
  unfold Small7 at hs
  interval_cases b <;> interval_cases c <;>
    first
    | (exfalso; exact hs (by decide))
    | norm_num [Fgc, J3, J4, kA, kt, ku3, ku4e, ku4b, qk, rho]

set_option maxHeartbeats 1000000 in
theorem cert7_4 {b c : ℕ} (hb : b ≤ 7) (hc : c ≤ 7) (hs : ¬ Small7 4 b c) :
    0 ≤ Fcap 7 (4 : ℕ) b c := by
  refine le_trans ?_ (Fcap_ge_Fgc le_rfl (Nat.cast_nonneg _) (Nat.cast_nonneg b)
    (Nat.cast_nonneg c))
  unfold Small7 at hs
  interval_cases b <;> interval_cases c <;>
    first
    | (exfalso; exact hs (by decide))
    | norm_num [Fgc, J3, J4, kA, kt, ku3, ku4e, ku4b, qk, rho]

set_option maxHeartbeats 1000000 in
theorem cert7_5 {b c : ℕ} (hb : b ≤ 7) (hc : c ≤ 7) (hs : ¬ Small7 5 b c) :
    0 ≤ Fcap 7 (5 : ℕ) b c := by
  refine le_trans ?_ (Fcap_ge_Fgc le_rfl (Nat.cast_nonneg _) (Nat.cast_nonneg b)
    (Nat.cast_nonneg c))
  unfold Small7 at hs
  interval_cases b <;> interval_cases c <;>
    first
    | (exfalso; exact hs (by decide))
    | norm_num [Fgc, J3, J4, kA, kt, ku3, ku4e, ku4b, qk, rho]

set_option maxHeartbeats 1000000 in
theorem cert7_6 {b c : ℕ} (hb : b ≤ 7) (hc : c ≤ 7) (hs : ¬ Small7 6 b c) :
    0 ≤ Fcap 7 (6 : ℕ) b c := by
  refine le_trans ?_ (Fcap_ge_Fgc le_rfl (Nat.cast_nonneg _) (Nat.cast_nonneg b)
    (Nat.cast_nonneg c))
  unfold Small7 at hs
  interval_cases b <;> interval_cases c <;>
    first
    | (exfalso; exact hs (by decide))
    | norm_num [Fgc, J3, J4, kA, kt, ku3, ku4e, ku4b, qk, rho]

set_option maxHeartbeats 1000000 in
theorem cert7_7 {b c : ℕ} (hb : b ≤ 7) (hc : c ≤ 7) (hs : ¬ Small7 7 b c) :
    0 ≤ Fcap 7 (7 : ℕ) b c := by
  refine le_trans ?_ (Fcap_ge_Fgc le_rfl (Nat.cast_nonneg _) (Nat.cast_nonneg b)
    (Nat.cast_nonneg c))
  unfold Small7 at hs
  interval_cases b <;> interval_cases c <;>
    first
    | (exfalso; exact hs (by decide))
    | norm_num [Fgc, J3, J4, kA, kt, ku3, ku4e, ku4b, qk, rho]

/-- **The capped certificate at `k = 7`.** -/
theorem cert7 {a b c : ℕ} (ha : a ≤ 7) (hb : b ≤ 7) (hc : c ≤ 7) (hs : ¬ Small7 a b c) :
    0 ≤ Fcap 7 a b c := by
  interval_cases a
  · exact cert7_0 hb hc hs
  · exact cert7_1 hb hc hs
  · exact cert7_2 hb hc hs
  · exact cert7_3 hb hc hs
  · exact cert7_4 hb hc hs
  · exact cert7_5 hb hc hs
  · exact cert7_6 hb hc hs
  · exact cert7_7 hb hc hs

end GridGen.Four
