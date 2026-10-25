/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.LogBounds

/-!
# Height four: the log count ratio of one column, as a real inequality

The number of successors of a column factors into four row rates. With the data
`(nᵢ, e₁₂, e₂₃, e₃₄, t₁₂₃, t₂₃₄, q)` of the actual successor lists and the uniform data fixed by
the pattern bits `c₁₃, c₂₄, c₁₄`, the rate bounds of `LogBounds.lean` combine into a lower bound
on `log (N / Nᵁ)`: the main terms `log (1 + μᵢ/A) - zᵢ/(nℓ)`, the bonuses `β₀ h`, and the
third- and fourth-row errors, which are charged either to the mismatches (`J₃, J₄`) or, when
there are none, to the bonuses (`b₃`, `b₄`). This file holds the pieces (`log_count_split`,
`row3_charge`, `row4_charge`, `bonus_sum`); `CountBound6.lean` assembles them at `k = 6`
(`count_log_bound6`).
-/

namespace GridGen.Four

open Real GridGen.Lookback

/-- The count of four rows from its data. -/
noncomputable def N4 (n1 n2 n3 n4 e12 e23 e34 t123 t234 q : ℝ) : ℝ :=
  n4 * (n3 * (n1 * n2 - e12) - (n1 * e23 - t123)) - (n1 * (n2 * e34 - t234) - e12 * e34 + q)

/-- The uniform count for the pattern bits. -/
noncomputable def N4U (n c13 c24 c14 : ℝ) : ℝ :=
  N4 n n n n (n - 1) (n - 1) (n - 1) (n - 2 + c13) (n - 2 + c24) (n - 3 + c13 + c24 + c14)

/-- `log (a/b) = log (c/d) + log (a/c) - log (b/d)` for positive reals. -/
theorem log_split {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    log (a / b) = log (c / d) + log (a / c) - log (b / d) := by
  rw [Real.log_div ha.ne' hb.ne', Real.log_div hc.ne' hd.ne', Real.log_div ha.ne' hc.ne',
    Real.log_div hb.ne' hd.ne']
  ring

/-- The positivity of the prefix counts from the counting constraints. -/
theorem counts_pos {n n1 n2 n3 n4 e12 e23 t123 M4 : ℝ} (hn : 5 ≤ n) (hn1 : n ≤ n1) (hn2 : n ≤ n2)
    (hn3 : n ≤ n3) (hn4 : n ≤ n4) (he12 : e12 ≤ n1) (hM3 : n1 * e23 - t123 ≤ n1 * n2 - e12)
    (hM4 : M4 ≤ n3 * (n1 * n2 - e12) - (n1 * e23 - t123)) :
    0 < n1 * n2 - e12 ∧ 0 < n3 * (n1 * n2 - e12) - (n1 * e23 - t123) ∧
      0 < n4 * (n3 * (n1 * n2 - e12) - (n1 * e23 - t123)) - M4 := by
  have h2 : 0 < n1 * n2 - e12 := by nlinarith
  have h3 : 0 < n3 * (n1 * n2 - e12) - (n1 * e23 - t123) := by nlinarith
  refine ⟨h2, h3, by nlinarith⟩

/-- **The count ratio as a sum of four row logs.** -/
theorem log_count_split {n n1 N2 N3 N4 N2U N3U N4U : ℝ} (hn : 0 < n) (hn1 : 0 < n1)
    (h2 : 0 < N2) (h3 : 0 < N3) (h4 : 0 < N4) (h2U : 0 < N2U) (h3U : 0 < N3U) (h4U : 0 < N4U) :
    log (N4 / N4U) = log (n1 / n) + log ((N2 / n1) / (N2U / n)) + log ((N3 / N2) / (N3U / N2U))
      + log ((N4 / N3) / (N4U / N3U)) := by
  rw [← Real.log_mul (by positivity) (by positivity), ← Real.log_mul (by positivity) (by positivity),
    ← Real.log_mul (by positivity) (by positivity)]
  congr 1
  field_simp

/-! ### Constants (in `n = k - 1`) -/

noncomputable def kA (n : ℝ) : ℝ := n ^ 2 - n + 1
noncomputable def kt (n : ℝ) : ℝ := kA n / n
noncomputable def ku3 (n : ℝ) : ℝ := (n - 1) / (n ^ 2 * kt n ^ 2)
noncomputable def ku4e (n : ℝ) : ℝ := 1 / ((n - 1) ^ 2 * kt n)
noncomputable def ku4b (n : ℝ) : ℝ := 1 / (n * kt n ^ 2 * (n - 1))
noncomputable def kb3 (n : ℝ) : ℝ := 1 / (n ^ 2 * (n - 1) ^ 2) + ku3 n
noncomputable def kb4 (n : ℝ) : ℝ := 2 / (n * (n - 1) ^ 3) + ku4e n + ku4b n
noncomputable def kβ0 (n : ℝ) : ℝ := (n - 1) / (n * (n + 1)) - (n + 2) / (n * (n + 1) * (n - 1))

/-- The mismatch indicators. -/
noncomputable def J3 (μ2 μ3 : ℝ) : ℝ := if μ2 + μ3 = 0 then 0 else 1
noncomputable def J4 (μ2 μ3 μ4 : ℝ) : ℝ := if μ2 + μ3 + μ4 = 0 then 0 else 1

/-- The uniform fourth count is positive. -/
theorem N4U_pos {n c13 c24 c14 : ℝ} (hn : 5 ≤ n) (hc13 : c13 = 0 ∨ c13 = 1)
    (hc24 : c24 = 0 ∨ c24 = 1) (hc14 : c14 = 0 ∨ c14 = 1) (h1314 : c13 * c14 = 0)
    (h2414 : c24 * c14 = 0) : 0 < N4U n c13 c24 c14 := by
  unfold N4U N4
  rcases hc14 with rfl | rfl
  · rcases hc13 with rfl | rfl <;> rcases hc24 with rfl | rfl <;> nlinarith
  · have e13 : c13 = 0 := by simpa using h1314
    have e24 : c24 = 0 := by simpa using h2414
    subst e13 e24
    nlinarith

/-- The uniform third count is positive. -/
theorem N3U_pos {n c13 : ℝ} (hn : 5 ≤ n) (hc : c13 = 0 ∨ c13 = 1) :
    0 < n * (n ^ 2 - n + 1) - (n * (n - 1) - (n - 2 + c13)) := by
  rcases hc with rfl | rfl <;> nlinarith

/-- `n - (n-1)/n = t`. -/
theorem main_unif {n : ℝ} (hn : 0 < n) : n - (n - 1) / n = (n ^ 2 - n + 1) / n := by
  field_simp; ring

/-- **The bonuses.** The row gains `(n-1)h/(n(n+1))` pay for the next-row losses. -/
theorem bonus_sum {n h1 h2 h3 h4 μ2 μ3 μ4 : ℝ} (hn : 5 ≤ n)
    (hh1 : 0 ≤ h1) (hh2 : 0 ≤ h2) (hh3 : 0 ≤ h3) (hh4 : 0 ≤ h4)
    (hμ2k : μ2 ≤ n + 1) (hμ3k : μ3 ≤ n + 1) (hμ4k : μ4 ≤ n + 1) :
    kβ0 n * (h1 + h2 + h3 + h4)
      ≤ ((n - 1) / n) * h1 / (n + 1)
        + (((n - 1) / n) * h2 / (n + 1) - (μ2 + 1) * h1 / (n * (n + 1) * (n - 1)))
        + (((n - 1) / n) * h3 / (n + 1) - (μ3 + 1) * h2 / (n * (n + 1) * (n - 1)))
        + (((n - 1) / n) * h4 / (n + 1) - (μ4 + 1) * h3 / (n * (n + 1) * (n - 1))) := by
  have hD : 0 < n * (n + 1) * (n - 1) := by
    have : 0 < n - 1 := by linarith
    positivity
  have f : ∀ μ h : ℝ, 0 ≤ h → μ ≤ n + 1 →
      (μ + 1) * h / (n * (n + 1) * (n - 1)) ≤ (n + 2) * h / (n * (n + 1) * (n - 1)) := by
    intro μ h hh hμ
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hh) hD.le
  have f2 := f μ2 h1 hh1 hμ2k
  have f3 := f μ3 h2 hh2 hμ3k
  have f4 := f μ4 h3 hh3 hμ4k
  have f5 : 0 ≤ (n + 2) * h4 / (n * (n + 1) * (n - 1)) := by
    have : 0 ≤ n + 2 := by linarith
    positivity
  have hid : kβ0 n * (h1 + h2 + h3 + h4)
      = ((n - 1) / n) * h1 / (n + 1) + ((n - 1) / n) * h2 / (n + 1)
        + ((n - 1) / n) * h3 / (n + 1) + ((n - 1) / n) * h4 / (n + 1)
        - (n + 2) * h1 / (n * (n + 1) * (n - 1)) - (n + 2) * h2 / (n * (n + 1) * (n - 1))
        - (n + 2) * h3 / (n * (n + 1) * (n - 1)) - (n + 2) * h4 / (n * (n + 1) * (n - 1)) := by
    unfold kβ0
    have : n ≠ 0 := by linarith
    have : n + 1 ≠ 0 := by linarith
    have : n - 1 ≠ 0 := by linarith
    field_simp; ring
  linarith

/-- **Row three, the error.** The actual-versus-main deviation and the uniform excess are charged
to `J₃`, or, in a defect-free column with a bonus row, to `b₃`. -/
theorem row3_charge {n n1 n2 n3 e12 e23 t123 μ2 μ3 h1 h2 h3 h4 z2 z3 c13 : ℝ} (hn : 5 ≤ n)
    (hh1 : h1 = 0 ∨ h1 = 1) (hh2 : h2 = 0 ∨ h2 = 1) (hh3 : h3 = 0 ∨ h3 = 1) (hh4 : 0 ≤ h4)
    (hn1 : n1 = n + h1) (hn2 : n2 = n + h2) (hn3 : n3 = n + h3)
    (hμ2 : 0 ≤ μ2) (hμ3 : 0 ≤ μ3) (hz2 : 0 ≤ z2) (hz3 : 0 ≤ z3)
    (he12 : e12 = (n - 1 - μ2) + h1 + h2 + z2) (he23 : e23 = (n - 1 - μ3) + h2 + h3 + z3)
    (he12a : 0 ≤ e12) (he12b : e12 ≤ n1) (he12c : e12 ≤ n2)
    (he23a : 0 ≤ e23) (he23b : e23 ≤ n2)
    (ht123 : e12 + e23 - n2 ≤ t123)
    (hM30 : 0 ≤ n1 * e23 - t123) (hM3N : n1 * e23 - t123 ≤ n1 * n2 - e12)
    (hc13 : c13 = 0 ∨ c13 = 1)
    (hZ3 : μ2 = 0 → μ3 = 0 → h1 = 0 → h2 = 0 → h3 = 0 →
      z2 = 0 ∧ z3 = 0 ∧ t123 = n - 2 + c13) :
    -(J3 μ2 μ3 * ((μ2 + 1) * (μ3 + 1) / (n ^ 2 * (n - 1) ^ 2) + ku3 n * c13))
        - kb3 n * (h1 + h2 + h3 + h4)
      ≤ log (((n3 * (n1 * n2 - e12) - (n1 * e23 - t123)) / (n1 * n2 - e12)) / (n3 - e23 / n2))
        - log (((n * (n ^ 2 - n + 1) - (n * (n - 1) - (n - 2 + c13))) / (n ^ 2 - n + 1))
          / ((n ^ 2 - n + 1) / n)) := by
  have hn0 : 0 < n := by linarith
  have hl0 : 0 < n - 1 := by linarith
  have hb1 : 0 ≤ h1 ∧ h1 ≤ 1 := by rcases hh1 with rfl | rfl <;> norm_num
  have hb2 : 0 ≤ h2 ∧ h2 ≤ 1 := by rcases hh2 with rfl | rfl <;> norm_num
  have hb3 : 0 ≤ h3 ∧ h3 ≤ 1 := by rcases hh3 with rfl | rfl <;> norm_num
  have hc : 0 ≤ c13 ∧ c13 ≤ 1 := by rcases hc13 with rfl | rfl <;> norm_num
  have herr := rate3_err (n1 := n1) (n2 := n2) (n3 := n3) (e12 := e12) (e23 := e23)
    (t123 := t123) hn (by rw [hn1]; linarith) (by rw [hn1]; linarith)
    (by rw [hn2]; linarith) (by rw [hn2]; linarith) (by rw [hn3]; linarith)
    (by rw [hn3]; linarith) he12a he12b he12c he23a he23b ht123 hM30 hM3N
    (μ2 := μ2) (μ3 := μ3) (by rw [hn2, he12]; linarith) (by rw [hn2, he23]; linarith) hμ2 hμ3
  have hunif := rate3_unif hn hc13
  have eku : (n - 1) / (n ^ 2 * ((n ^ 2 - n + 1) / n) ^ 2) * c13 = ku3 n * c13 := by
    unfold ku3 kt kA; ring
  rw [eku] at hunif
  have hku : 0 ≤ ku3 n := by unfold ku3 kt kA; have : 0 < n ^ 2 - n + 1 := by nlinarith
                             positivity
  have hkb : 0 ≤ 1 / (n ^ 2 * (n - 1) ^ 2) := by positivity
  have hkb3 : kb3 n = 1 / (n ^ 2 * (n - 1) ^ 2) + ku3 n := rfl
  by_cases hJ : μ2 + μ3 = 0
  · have e2 : μ2 = 0 := by linarith
    have e3 : μ3 = 0 := by linarith
    simp only [J3, hJ, ite_true, zero_mul, neg_zero, zero_sub]
    subst e2 e3
    by_cases hh : h1 = 0 ∧ h2 = 0 ∧ h3 = 0
    · obtain ⟨r1, r2, r3⟩ := hh
      obtain ⟨y2, y3, yt⟩ := hZ3 rfl rfl r1 r2 r3
      subst r1 r2 r3 y2 y3
      rw [hn1, hn2, hn3, he12, he23, yt, show n + 0 - (n - 1 - 0 + 0 + 0 + 0) / (n + 0)
        = (n ^ 2 - n + 1) / n by rw [← main_unif hn0]; ring_nf]
      have : ((n + 0) * ((n + 0) * (n + 0) - (n - 1 - 0 + 0 + 0 + 0))
            - ((n + 0) * (n - 1 - 0 + 0 + 0 + 0) - (n - 2 + c13)))
          / ((n + 0) * (n + 0) - (n - 1 - 0 + 0 + 0 + 0))
          = (n * (n ^ 2 - n + 1) - (n * (n - 1) - (n - 2 + c13))) / (n ^ 2 - n + 1) := by ring
      rw [this, sub_self]
      have : 0 ≤ kb3 n * (0 + 0 + 0 + h4) := by rw [hkb3]; positivity
      linarith
    · have hS : 1 ≤ h1 + h2 + h3 + h4 := by
        rcases hh1 with rfl | rfl <;> rcases hh2 with rfl | rfl <;> rcases hh3 with rfl | rfl <;>
          simp at hh <;> linarith
      have hS' : kb3 n * 1 ≤ kb3 n * (h1 + h2 + h3 + h4) :=
        mul_le_mul_of_nonneg_left hS (by rw [hkb3]; positivity)
      have hc' : ku3 n * c13 ≤ ku3 n := mul_le_of_le_one_right hku hc.2
      have herr' : -(1 / (n ^ 2 * (n - 1) ^ 2)) ≤ log (((n3 * (n1 * n2 - e12)
          - (n1 * e23 - t123)) / (n1 * n2 - e12)) / (n3 - e23 / n2)) := by
        simpa using herr
      linarith
  · simp only [J3, hJ, ite_false, one_mul]
    have : 0 ≤ kb3 n * (h1 + h2 + h3 + h4) :=
      mul_nonneg (by rw [hkb3]; positivity) (by linarith)
    linarith

/-- `1/(nt(n-1)³) ≤ 1/((n-1)²t)`. -/
theorem tail_le_ku4e {n : ℝ} (hn : 5 ≤ n) :
    1 / (n * ((n ^ 2 - n + 1) / n) * (n - 1) ^ 3) ≤ ku4e n := by
  unfold ku4e kt kA
  have hl : 0 < n - 1 := by linarith
  have ht : 0 < (n ^ 2 - n + 1) / n := by apply div_pos <;> nlinarith
  apply one_div_le_one_div_of_le (by positivity)
  have : (n - 1) ^ 2 * ((n ^ 2 - n + 1) / n) * 1 ≤ (n - 1) ^ 2 * ((n ^ 2 - n + 1) / n) * (n * (n - 1)) :=
    mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  nlinarith

set_option maxHeartbeats 2000000 in
/-- **Row four, the error.** As for row three, with the defect-free tail of `rate4_tail` when only
row one has a bonus. -/
theorem row4_charge {k : ℕ} (hk6 : 6 ≤ k) (hkle : k ≤ 7) {n : ℝ} (hnk : n = (k : ℝ) - 1)
    {n1 n2 n3 n4 e12 e23 e34 t123 t234 q h1 h2 h3 h4 μ2 μ3 μ4 z2 z3 z4 c13 c24 c14 : ℝ}
    (hh1 : h1 = 0 ∨ h1 = 1) (hh2 : h2 = 0 ∨ h2 = 1) (hh3 : h3 = 0 ∨ h3 = 1) (hh4 : h4 = 0 ∨ h4 = 1)
    (hn1 : n1 = n + h1) (hn2 : n2 = n + h2) (hn3 : n3 = n + h3) (hn4 : n4 = n + h4)
    (hμ2 : 0 ≤ μ2) (hμ3 : 0 ≤ μ3) (hμ4 : 0 ≤ μ4) (hz3 : 0 ≤ z3) (hz4 : 0 ≤ z4)
    (he12 : e12 = (n - 1 - μ2) + h1 + h2 + z2) (he23 : e23 = (n - 1 - μ3) + h2 + h3 + z3)
    (he34 : e34 = (n - 1 - μ4) + h3 + h4 + z4)
    (he12a : 0 ≤ e12) (he12b : e12 ≤ n1) (he23c : e23 ≤ n3)
    (he34a : 0 ≤ e34) (he34b : e34 ≤ n3)
    (ht0 : 0 ≤ t123) (ht1 : t123 ≤ n1) (ht234 : e23 + e34 - n3 ≤ t234) (hq : q ≤ t123)
    (hM30 : 0 ≤ n1 * e23 - t123) (hM3N : n1 * e23 - t123 ≤ n1 * n2 - e12)
    (hM40 : 0 ≤ n1 * (n2 * e34 - t234) - e12 * e34 + q)
    (hM4N : n1 * (n2 * e34 - t234) - e12 * e34 + q ≤ n3 * (n1 * n2 - e12) - (n1 * e23 - t123))
    (hc13 : c13 = 0 ∨ c13 = 1) (hc24 : c24 = 0 ∨ c24 = 1) (hc14 : c14 = 0 ∨ c14 = 1)
    (h1314 : c13 * c14 = 0) (h2414 : c24 * c14 = 0)
    (hZ4 : μ2 = 0 → μ3 = 0 → μ4 = 0 → h2 = 0 → h3 = 0 → h4 = 0 →
      z2 = 0 ∧ z3 = 0 ∧ z4 = 0 ∧ t234 = n - 2 + c24 ∧
      (h1 = 0 → t123 = n - 2 + c13 ∧ q = n - 3 + c13 + c24 + c14) ∧
      (h1 = 1 → t123 = n - 1 ∧ q = t234 ∧ c13 = 0 ∧ c14 = 0)) :
    -(J4 μ2 μ3 μ4 * ((μ3 + 2) * (μ4 + 1) / (n * (n - 1) ^ 3) + ku4e n * c24 + ku4b n))
        - kb4 n * (h1 + h2 + h3 + h4)
      ≤ log (rate4 n1 n2 n3 n4 e12 e23 e34 t123 t234 q / (n4 - e34 / n3))
        - log (r4U n c13 c24 c14 / ((n ^ 2 - n + 1) / n)) := by
  have hk6' : (6 : ℝ) ≤ k := by exact_mod_cast hk6
  have hn : 5 ≤ n := by rw [hnk]; linarith
  have hn0 : 0 < n := by linarith
  have hl0 : 0 < n - 1 := by linarith
  have hb1 : 0 ≤ h1 ∧ h1 ≤ 1 := by rcases hh1 with rfl | rfl <;> norm_num
  have hb2 : 0 ≤ h2 ∧ h2 ≤ 1 := by rcases hh2 with rfl | rfl <;> norm_num
  have hb3 : 0 ≤ h3 ∧ h3 ≤ 1 := by rcases hh3 with rfl | rfl <;> norm_num
  have hb4 : 0 ≤ h4 ∧ h4 ≤ 1 := by rcases hh4 with rfl | rfl <;> norm_num
  have hc : 0 ≤ c24 ∧ c24 ≤ 1 := by rcases hc24 with rfl | rfl <;> norm_num
  have herr := rate4_err (n1 := n1) (n2 := n2) (n3 := n3) (n4 := n4) (e12 := e12) (e23 := e23)
    (e34 := e34) (t123 := t123) (t234 := t234) (q := q) (μ3 := μ3) (μ4 := μ4) hn
    (by rw [hn1]; linarith) (by rw [hn1]; linarith) (by rw [hn2]; linarith) (by rw [hn2]; linarith)
    (by rw [hn3]; linarith) (by rw [hn3]; linarith) (by rw [hn4]; linarith) (by rw [hn4]; linarith)
    he12a he12b he23c he34a he34b ht234 hq ht0 ht1 hM30 hM3N hM40 hM4N
    (by rw [hn3, he23]; linarith) (by rw [hn3, he34]; linarith) hμ3 hμ4
  have herr' : -((μ3 + 2) * (μ4 + 1) / (n * (n - 1) ^ 3))
      ≤ log (rate4 n1 n2 n3 n4 e12 e23 e34 t123 t234 q / (n4 - e34 / n3)) := herr
  clear herr
  have e1 : (k : ℝ) - 1 = n := by rw [hnk]
  have e2 : (k : ℝ) - 2 = n - 1 := by rw [hnk]; ring
  have e3 : (k : ℝ) - 3 = n - 2 := by rw [hnk]; ring
  have e0 : (k : ℝ) = n + 1 := by rw [hnk]; ring
  have hunif := rate4_unif hk6 hkle hc13 hc24 hc14 h1314 h2414
  rw [e1, e2] at hunif
  have eku : c24 / ((n - 1) ^ 2 * ((n ^ 2 - n + 1) / n))
      + 1 / (n * ((n ^ 2 - n + 1) / n) ^ 2 * (n - 1)) = ku4e n * c24 + ku4b n := by
    unfold ku4e ku4b kt kA; ring
  rw [eku] at hunif
  have ht : 0 < (n ^ 2 - n + 1) / n := by apply div_pos <;> nlinarith
  have hku4e : 0 ≤ ku4e n := by
    unfold ku4e kt kA; exact (one_div_pos.mpr (mul_pos (by positivity) ht)).le
  have hku4b : 0 ≤ ku4b n := by
    unfold ku4b kt kA; exact (one_div_pos.mpr (mul_pos (mul_pos hn0 (pow_pos ht 2)) hl0)).le
  have hkb4 : kb4 n = 2 / (n * (n - 1) ^ 3) + ku4e n + ku4b n := rfl
  have h2p : 0 ≤ 2 / (n * (n - 1) ^ 3) :=
    div_nonneg zero_le_two (mul_pos hn0 (pow_pos hl0 3)).le
  have hkb4p : 0 ≤ kb4 n := by rw [hkb4]; exact add_nonneg (add_nonneg h2p hku4e) hku4b
  by_cases hJ : μ2 + μ3 + μ4 = 0
  · have f2 : μ2 = 0 := by linarith
    have f3 : μ3 = 0 := by linarith
    have f4 : μ4 = 0 := by linarith
    simp only [J4, hJ, ite_true, zero_mul, neg_zero, zero_sub]
    subst f2 f3 f4
    by_cases hh : h2 = 0 ∧ h3 = 0 ∧ h4 = 0
    · obtain ⟨r2, r3, r4⟩ := hh
      obtain ⟨y2, y3, y4, yt, Y0, Y1⟩ := hZ4 rfl rfl rfl r2 r3 r4
      subst r2 r3 r4 y2 y3 y4
      have a2 : n2 = n := by rw [hn2]; ring
      have a3 : n3 = n := by rw [hn3]; ring
      have a4 : n4 = n := by rw [hn4]; ring
      have b23 : e23 = n - 1 := by rw [he23]; ring
      have b34 : e34 = n - 1 := by rw [he34]; ring
      rw [a2, a3, a4, b23, b34, yt, main_unif hn0]
      rcases hh1 with r1 | r1
      · obtain ⟨u1, u2⟩ := Y0 r1
        subst r1
        have a1 : n1 = n := by rw [hn1]; ring
        have b12 : e12 = n - 1 := by rw [he12]; ring
        rw [a1, b12, u1, u2]
        simp only [r4U, sub_self]
        have : 0 ≤ kb4 n * (0 + 0 + 0 + 0) := by simp
        linarith
      · obtain ⟨u1, u2, u3, u4⟩ := Y1 r1
        subst r1 u3 u4
        have a1 : n1 = n + 1 := by rw [hn1]
        have b12 : e12 = n := by rw [he12]; ring
        rw [a1, b12, u1, u2, yt]
        have htail := rate4_tail hk6 hkle hc24
        rw [e1, e2, e3, e0, main_unif hn0] at htail
        have h1t := tail_le_ku4e hn
        have h1k : kb4 n * (1 + 0 + 0 + 0) = kb4 n := by ring
        rw [h1k, hkb4]
        linarith
    · have hS : 1 ≤ h1 + h2 + h3 + h4 := by
        rcases hh2 with rfl | rfl <;> rcases hh3 with rfl | rfl <;> rcases hh4 with rfl | rfl <;>
          simp at hh <;> linarith
      have hS' : kb4 n * 1 ≤ kb4 n * (h1 + h2 + h3 + h4) := mul_le_mul_of_nonneg_left hS hkb4p
      have hc' : ku4e n * c24 ≤ ku4e n := mul_le_of_le_one_right hku4e hc.2
      have herr2 : -(2 / (n * (n - 1) ^ 3))
          ≤ log (rate4 n1 n2 n3 n4 e12 e23 e34 t123 t234 q / (n4 - e34 / n3)) := by
        simpa using herr'
      linarith
  · simp only [J4, hJ, ite_false, one_mul]
    have : 0 ≤ kb4 n * (h1 + h2 + h3 + h4) := mul_nonneg hkb4p (by linarith)
    linarith

end GridGen.Four
