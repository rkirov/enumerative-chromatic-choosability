import GridGen.PolymerParityBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! # Uniform parity budgets for an arbitrary maximum degree

The matrix exponential with entries `37/100` and `117/100` dominates
every finite child-port product. Its value at `10000/35721` is certified
by the standard exponential Taylor remainder estimate, using rational arithmetic.
-/

namespace GridGen.Polymer

noncomputable def uniformEven (t : ℝ) : ℝ :=
  Real.exp (37 / 100 * t) * Real.cosh (117 / 100 * t)

noncomputable def uniformOdd (t : ℝ) : ℝ :=
  Real.exp (37 / 100 * t) * Real.sinh (117 / 100 * t)

theorem uniformEven_nonneg (t : ℝ) : 0 ≤ uniformEven t := by
  unfold uniformEven
  exact mul_nonneg (Real.exp_pos _).le (le_trans (by norm_num) (Real.one_le_cosh _))

theorem uniformOdd_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ uniformOdd t := by
  unfold uniformOdd
  exact mul_nonneg (Real.exp_pos _).le (Real.sinh_nonneg_iff.mpr (by positivity))

theorem uniformParity_add (s t : ℝ) :
    uniformEven (s + t) = uniformEven s * uniformEven t + uniformOdd s * uniformOdd t ∧
    uniformOdd (s + t) = uniformOdd s * uniformEven t + uniformEven s * uniformOdd t := by
  unfold uniformEven uniformOdd
  simp only [mul_add, Real.exp_add, Real.cosh_add, Real.sinh_add]
  constructor <;> ring

theorem uniformEven_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    uniformEven s ≤ uniformEven t := by
  unfold uniformEven
  apply mul_le_mul
  · exact Real.exp_le_exp.mpr (by linarith)
  · apply Real.cosh_le_cosh.mpr
    rw [abs_of_nonneg (by positivity : 0 ≤ 117 / 100 * s),
      abs_of_nonneg (by have := hs.trans hst; positivity : 0 ≤ 117 / 100 * t)]
    linarith
  · exact le_trans (by norm_num) (Real.one_le_cosh _)
  · exact (Real.exp_pos _).le

theorem uniformOdd_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    uniformOdd s ≤ uniformOdd t := by
  unfold uniformOdd
  apply mul_le_mul
  · exact Real.exp_le_exp.mpr (by linarith)
  · exact Real.sinh_le_sinh.mpr (by linarith)
  · exact Real.sinh_nonneg_iff.mpr (by positivity)
  · exact (Real.exp_pos _).le

theorem uniformParity_linear {x : ℝ} (hx : 0 ≤ x) :
    1 + x * (37 / 100) ≤ uniformEven x ∧ x * (117 / 100) ≤ uniformOdd x := by
  have he : 1 ≤ Real.exp (37 / 100 * x) := Real.one_le_exp_iff.mpr (by positivity)
  constructor
  · have hh := mul_le_mul_of_nonneg_left (Real.one_le_cosh (117 / 100 * x))
      (Real.exp_pos (37 / 100 * x)).le
    have hl := Real.add_one_le_exp (37 / 100 * x)
    unfold uniformEven
    nlinarith
  · have hh := mul_le_mul_of_nonneg_right he
      (Real.sinh_nonneg_iff.mpr (by positivity : 0 ≤ 117 / 100 * x))
    have hl := Real.self_le_sinh_iff.mpr (by positivity : 0 ≤ 117 / 100 * x)
    unfold uniformOdd
    nlinarith

theorem parityPower_le_uniform {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    (parityPower (1 + x * (37 / 100)) (x * (117 / 100)) n).1 ≤ uniformEven (n * x) ∧
    (parityPower (1 + x * (37 / 100)) (x * (117 / 100)) n).2 ≤ uniformOdd (n * x) := by
  induction n with
  | zero => simp [parityPower, uniformEven, uniformOdd]
  | succ n ih =>
    have hn := parityPower_nonneg (by positivity : 0 ≤ 1 + x * (37 / 100))
      (by positivity : 0 ≤ x * (117 / 100)) n
    have hl := uniformParity_linear hx
    have hnx : 0 ≤ (n : ℝ) * x := mul_nonneg (Nat.cast_nonneg _) hx
    have he := uniformEven_nonneg x
    have ho := uniformOdd_nonneg hx
    have h₁ := mul_le_mul hl.1 ih.1 hn.1 he
    have h₂ := mul_le_mul hl.2 ih.2 hn.2 ho
    have h₃ := mul_le_mul hl.2 ih.1 hn.1 ho
    have h₄ := mul_le_mul hl.1 ih.2 hn.2 he
    have hadd := uniformParity_add x (n * x)
    have harg : ((n + 1 : ℕ) : ℝ) * x = x + n * x := by push_cast; ring
    rw [harg, hadd.1, hadd.2]
    exact ⟨add_le_add h₁ h₂, add_le_add h₃ h₄⟩

theorem uniformParity_exponentials (t : ℝ) :
    uniformEven t = (Real.exp (154 / 100 * t) + Real.exp (-(80 / 100 * t))) / 2 ∧
    uniformOdd t = (Real.exp (154 / 100 * t) - Real.exp (-(80 / 100 * t))) / 2 := by
  unfold uniformEven uniformOdd
  rw [Real.cosh_eq, Real.sinh_eq]
  simp only [← mul_div_assoc, mul_add, mul_sub, ← Real.exp_add]
  have hp : 37 / 100 * t + 117 / 100 * t = 154 / 100 * t := by ring
  have hm : 37 / 100 * t + -(117 / 100 * t) = -(80 / 100 * t) := by ring
  rw [hp, hm]
  exact ⟨rfl, rfl⟩

/-- Exact numerical certificate: Taylor degree seven already leaves a positive margin. -/
theorem uniformParity_endpoint :
    uniformEven (10000 / 35721) ≤ 117 / 100 ∧
    uniformOdd (10000 / 35721) ≤ 37 / 100 := by
  have hp := Real.exp_bound (x := (2200 / 5103 : ℝ)) (by norm_num) (n := 8) (by norm_num)
  have hm := Real.exp_bound (x := (-(8000 / 35721) : ℝ)) (by norm_num) (n := 8) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hp hm
  obtain ⟨hp₁, hp₂⟩ := abs_le.mp hp
  obtain ⟨hm₁, hm₂⟩ := abs_le.mp hm
  rw [(uniformParity_exponentials _).1, (uniformParity_exponentials _).2]
  norm_num
  constructor <;> linarith

theorem parityPower_uniform_budget {x : ℝ} (hx : 0 ≤ x) (n : ℕ)
    (hn : (n : ℝ) * x ≤ 10000 / 35721) :
    (parityPower (1 + x * (37 / 100)) (x * (117 / 100)) n).1 ≤ 117 / 100 ∧
    (parityPower (1 + x * (37 / 100)) (x * (117 / 100)) n).2 ≤ 37 / 100 := by
  have h := parityPower_le_uniform hx n
  have hnx := mul_nonneg (Nat.cast_nonneg n) hx
  exact ⟨h.1.trans ((uniformEven_mono hnx hn).trans uniformParity_endpoint.1),
    h.2.trans ((uniformOdd_mono hnx hn).trans uniformParity_endpoint.2)⟩

/-- The uniform certificate: for every degree bound `D` and activity with `D x ≤ 10000/35721`,
the hyperbolic majorant bounds branches and roots alike by `(117/100, 37/100)`. -/
theorem parityCert_uniform {D : ℕ} {x : ℝ} (hx : 0 ≤ x) (hDx : (D : ℝ) * x ≤ 10000 / 35721) :
    ParityCert D x (117 / 100) (37 / 100) (37 / 100) := by
  have hpred : ((D - 1 : ℕ) : ℝ) * x ≤ 10000 / 35721 :=
    le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le D 1) hx) hDx
  exact ⟨hx, by norm_num, by norm_num, parityPower_uniform_budget hx (D - 1) hpred,
    (parityPower_uniform_budget hx D hDx).2, by norm_num⟩

end GridGen.Polymer
