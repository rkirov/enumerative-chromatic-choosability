/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.Defs
import Mathlib.Data.Fintype.Sum

/-!
# Analytic lemmas for the capacity lemma

* `gibbs` — the Gibbs inequality `∑ p log (T / p) ≤ log ∑ T`;
* `gmean` — geometric means over a finset of colours, through `exp` and `log`;
* `pendant_gmean` — root dominance for a pendant fibre: if every colour of `X` forbids at most
  one colour of `C`, and distinct colours forbid distinct ones, then the geometric mean over
  `X` of the allowed sums is at least `(m - 1)` times the geometric mean of the weights on `C`.
-/

namespace Outerplanar

open Finset

/-- **Gibbs' inequality.** -/
theorem gibbs {α : Type*} (s : Finset α) (p T : α → ℝ) (hp : ∀ J ∈ s, 0 ≤ p J)
    (hsum : ∑ J ∈ s, p J = 1) (hT : ∀ J ∈ s, 0 < p J → 0 < T J) (hT0 : ∀ J ∈ s, 0 ≤ T J) :
    ∑ J ∈ s, p J * Real.log (T J / p J) ≤ Real.log (∑ J ∈ s, T J) := by
  set S := ∑ J ∈ s, T J with hS
  have hSpos : 0 < S := by
    obtain ⟨J, hJ, hpJ⟩ : ∃ J ∈ s, 0 < p J := by
      by_contra h
      have : ∑ J ∈ s, p J = 0 := Finset.sum_eq_zero fun J hJ =>
        le_antisymm (not_lt.mp fun hlt => h ⟨J, hJ, hlt⟩) (hp J hJ)
      linarith
    exact lt_of_lt_of_le (hT J hJ hpJ) (Finset.single_le_sum (f := T) (fun i hi => hT0 i hi) hJ)
  have key : ∀ J ∈ s, p J * Real.log (T J / p J) ≤ p J * Real.log S + T J / S - p J := by
    intro J hJ
    rcases (hp J hJ).eq_or_lt with h0 | hpos
    · rw [← h0]
      simpa using div_nonneg (hT0 J hJ) hSpos.le
    · have hTJ := hT J hJ hpos
      have h1 : Real.log (T J / p J) = Real.log S + Real.log (T J / (p J * S)) := by
        rw [← Real.log_mul hSpos.ne' (by positivity)]
        congr 1
        field_simp
      have h2 : Real.log (T J / (p J * S)) ≤ T J / (p J * S) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [h1]
      have h3 : p J * (T J / (p J * S) - 1) = T J / S - p J := by field_simp
      nlinarith [mul_le_mul_of_nonneg_left h2 hpos.le]
  calc ∑ J ∈ s, p J * Real.log (T J / p J)
      ≤ ∑ J ∈ s, (p J * Real.log S + T J / S - p J) := Finset.sum_le_sum key
    _ = Real.log S := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_div,
        hsum, ← hS, div_self hSpos.ne']
      ring

/-- The geometric mean of `v` over `F`, for positive `v`. -/
noncomputable def gmean (F : Finset ℕ) (v : ℕ → ℝ) : ℝ :=
  Real.exp ((F.card : ℝ)⁻¹ * ∑ c ∈ F, Real.log (v c))

theorem gmean_pos (F : Finset ℕ) (v : ℕ → ℝ) : 0 < gmean F v := Real.exp_pos _

theorem log_gmean (F : Finset ℕ) (v : ℕ → ℝ) :
    Real.log (gmean F v) = (F.card : ℝ)⁻¹ * ∑ c ∈ F, Real.log (v c) := Real.log_exp _

theorem gmean_pow {F : Finset ℕ} {v : ℕ → ℝ} (hF : F.Nonempty) (hv : ∀ c ∈ F, 0 < v c) :
    gmean F v ^ F.card = ∏ c ∈ F, v c := by
  have hc : (F.card : ℝ) ≠ 0 := by exact_mod_cast hF.card_ne_zero
  rw [gmean, ← Real.exp_nat_mul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul, Real.exp_sum]
  exact Finset.prod_congr rfl fun c hc => Real.exp_log (hv c hc)

theorem gmean_eq_one {F : Finset ℕ} {v : ℕ → ℝ} (hv : ∀ c ∈ F, 0 < v c)
    (h : ∏ c ∈ F, v c = 1) : gmean F v = 1 := by
  rw [gmean, ← Real.log_prod (fun c hc => (hv c hc).ne'), h]
  simp

theorem gmean_mul {F : Finset ℕ} {v u : ℕ → ℝ} (hv : ∀ c ∈ F, 0 < v c) (hu : ∀ c ∈ F, 0 < u c) :
    gmean F (fun c => v c * u c) = gmean F v * gmean F u := by
  rw [gmean, gmean, gmean, ← Real.exp_add, ← mul_add, ← Finset.sum_add_distrib]
  congr 2
  exact Finset.sum_congr rfl fun c hc => Real.log_mul (hv c hc).ne' (hu c hc).ne'

theorem gmean_mono {F : Finset ℕ} {v u : ℕ → ℝ} (hv : ∀ c ∈ F, 0 < v c)
    (h : ∀ c ∈ F, v c ≤ u c) : gmean F v ≤ gmean F u := by
  rw [gmean, gmean]
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.sum_le_sum fun c hc => Real.log_le_log (hv c hc) (h c hc)

/-- AM–GM. -/
theorem card_mul_gmean_le_sum {F : Finset ℕ} {v : ℕ → ℝ} (hF : F.Nonempty)
    (hv : ∀ c ∈ F, 0 < v c) : (F.card : ℝ) * gmean F v ≤ ∑ c ∈ F, v c := by
  have hc : (0 : ℝ) < F.card := by exact_mod_cast hF.card_pos
  set a := (∑ c ∈ F, v c) / F.card with ha
  have hsum : 0 < ∑ c ∈ F, v c := Finset.sum_pos hv hF
  have hapos : 0 < a := div_pos hsum hc
  have h1 : ∑ c ∈ F, Real.log (v c / a) ≤ ∑ c ∈ F, (v c / a - 1) :=
    Finset.sum_le_sum fun c hc' => Real.log_le_sub_one_of_pos (div_pos (hv c hc') hapos)
  have h2 : ∑ c ∈ F, (v c / a - 1) = 0 := by
    have h2' : (∑ c ∈ F, v c) / a = F.card := by rw [ha]; field_simp
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, h2']
    simp
  have h3 : ∑ c ∈ F, Real.log (v c / a) = ∑ c ∈ F, Real.log (v c) - F.card * Real.log a := by
    rw [Finset.sum_congr rfl fun c hc' => Real.log_div (hv c hc').ne' hapos.ne']
    rw [Finset.sum_sub_distrib]
    simp
  have h4 : (F.card : ℝ)⁻¹ * ∑ c ∈ F, Real.log (v c) ≤ Real.log a := by
    rw [inv_mul_le_iff₀ hc]
    linarith
  have h5 : gmean F v ≤ a := by
    rw [gmean]
    calc Real.exp _ ≤ Real.exp (Real.log a) := Real.exp_le_exp.mpr h4
      _ = a := Real.exp_log hapos
  calc (F.card : ℝ) * gmean F v ≤ F.card * a := mul_le_mul_of_nonneg_left h5 hc.le
    _ = ∑ c ∈ F, v c := by rw [ha]; field_simp

open Classical in
/-- **Pendant fibre, logarithmic form.** `R x c` says that the colour `x` of `X` forbids the
colour `c` of `C`; it is a partial matching. -/
theorem pendant_log {m : ℕ} (hm : 2 ≤ m) (X C : Finset ℕ) (hX : X.card = m) (hC : C.card = m)
    (R : ℕ → ℕ → Prop)
    (hR1 : ∀ x ∈ X, ∀ c ∈ C, ∀ c' ∈ C, R x c → R x c' → c = c')
    (hR2 : ∀ x ∈ X, ∀ x' ∈ X, ∀ c ∈ C, R x c → R x' c → x = x')
    (θ : ℕ → ℝ) (hθ : ∀ c ∈ C, 0 < θ c) :
    (m : ℝ) * Real.log ((m : ℝ) - 1) + ∑ c ∈ C, Real.log (θ c)
      ≤ ∑ x ∈ X, Real.log (∑ c ∈ C with ¬ R x c, θ c) := by
  -- extend the partial matching to a bijection
  let f : X → ℕ := fun x => if h : ∃ c ∈ C, R x c then h.choose else 0
  have hf : ∀ x : X, ∀ c ∈ C, R x c → f x = c := by
    intro x c hc hR
    have h : ∃ c ∈ C, R x c := ⟨c, hc, hR⟩
    simp only [f, dite_eq_left h]
    exact hR1 x x.2 _ h.choose_spec.1 c hc h.choose_spec.2 hR
  obtain ⟨g, hg⟩ := Set.MapsTo.exists_equiv_extend_of_card_eq (α := X) (t := C)
    (s := {x : X | ∃ c ∈ C, R x c}) (f := f) (by simp [hX, hC])
    (by
      rintro x ⟨c, hc, hR⟩
      rw [hf x c hc hR]; exact hc)
    (by
      rintro x ⟨c, hc, hR⟩ x' ⟨c', hc', hR'⟩ hxx
      rw [hf x c hc hR, hf x' c' hc' hR'] at hxx
      subst hxx
      exact Subtype.ext (hR2 x x.2 x' x'.2 c hc hR hR'))
  have hgR : ∀ x : X, ∀ c ∈ C, R x c → (g x : ℕ) = c := by
    intro x c hc hR
    rw [hg x ⟨c, hc, hR⟩, hf x c hc hR]
  have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  set Λ := ∑ c ∈ C, Real.log (θ c) with hΛ
  -- the bound for one colour of `X`
  have key : ∀ x : X, Real.log ((m : ℝ) - 1) + ((m : ℝ) - 1)⁻¹ * (Λ - Real.log (θ (g x)))
      ≤ Real.log (∑ c ∈ C with ¬ R x c, θ c) := by
    intro x
    have hgx : (g x : ℕ) ∈ C := (g x).2
    have hcard : (C.erase (g x)).card = m - 1 := by rw [Finset.card_erase_of_mem hgx, hC]
    have hne : (C.erase (g x)).Nonempty := by
      rw [← Finset.card_pos, hcard]; omega
    have hpos : ∀ c ∈ C.erase (g x), 0 < θ c := fun c hc => hθ c (Finset.mem_of_mem_erase hc)
    have hsub : C.erase (g x) ⊆ C.filter fun c => ¬ R x c := by
      intro c hc
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_of_mem_erase hc, fun hR => ?_⟩
      exact Finset.ne_of_mem_erase hc (hgR x c (Finset.mem_of_mem_erase hc) hR).symm
    have h1 : ∑ c ∈ C.erase (g x), θ c ≤ ∑ c ∈ C with ¬ R x c, θ c :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun c hc _ =>
        (hθ c (Finset.mem_filter.mp hc).1).le
    have h2 := card_mul_gmean_le_sum hne hpos
    rw [hcard] at h2
    have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [hcast] at h2
    have h3 : Real.log (((m : ℝ) - 1) * gmean (C.erase (g x)) θ)
        ≤ Real.log (∑ c ∈ C with ¬ R x c, θ c) :=
      Real.log_le_log (mul_pos hm1 (gmean_pos _ _)) (h2.trans h1)
    rw [Real.log_mul hm1.ne' (gmean_pos _ _).ne', log_gmean, hcard, hcast] at h3
    have h4 : ∑ c ∈ C.erase (g x), Real.log (θ c) = Λ - Real.log (θ (g x)) := by
      rw [hΛ, ← Finset.add_sum_erase C _ hgx]; ring
    rwa [h4] at h3
  have hsumg : ∑ x : X, Real.log (θ (g x)) = Λ := by
    rw [hΛ, ← Finset.sum_coe_sort C]
    exact Equiv.sum_comp g fun c : C => Real.log (θ c)
  have hcardX : (Finset.univ : Finset X).card = m := by simp [hX]
  calc (m : ℝ) * Real.log ((m : ℝ) - 1) + Λ
      = ∑ x : X, (Real.log ((m : ℝ) - 1) + ((m : ℝ) - 1)⁻¹ * (Λ - Real.log (θ (g x)))) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hsumg]
        simp only [Finset.sum_const, hcardX, nsmul_eq_mul]
        field_simp
    _ ≤ ∑ x : X, Real.log (∑ c ∈ C with ¬ R x c, θ c) := Finset.sum_le_sum fun x _ => key x
    _ = ∑ x ∈ X, Real.log (∑ c ∈ C with ¬ R x c, θ c) :=
        Finset.sum_coe_sort X fun x => Real.log (∑ c ∈ C with ¬ R x c, θ c)

open Classical in
/-- **Pendant fibre.** The geometric mean over `X` of the allowed sums dominates `m - 1` times
the geometric mean of the weights. -/
theorem pendant_gmean {m : ℕ} (hm : 2 ≤ m) (X C : Finset ℕ) (hX : X.card = m) (hC : C.card = m)
    (R : ℕ → ℕ → Prop)
    (hR1 : ∀ x ∈ X, ∀ c ∈ C, ∀ c' ∈ C, R x c → R x c' → c = c')
    (hR2 : ∀ x ∈ X, ∀ x' ∈ X, ∀ c ∈ C, R x c → R x' c → x = x')
    (θ : ℕ → ℝ) (hθ : ∀ c ∈ C, 0 < θ c) :
    ((m : ℝ) - 1) * gmean C θ ≤ gmean X fun x => ∑ c ∈ C with ¬ R x c, θ c := by
  have h := pendant_log hm X C hX hC R hR1 hR2 θ hθ
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  rw [← Real.exp_log hm1, gmean, gmean, ← Real.exp_add, hX, hC]
  apply Real.exp_le_exp.mpr
  have : Real.log ((m : ℝ) - 1) + (m : ℝ)⁻¹ * ∑ c ∈ C, Real.log (θ c)
      = (m : ℝ)⁻¹ * ((m : ℝ) * Real.log ((m : ℝ) - 1) + ∑ c ∈ C, Real.log (θ c)) := by
    field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-- Every allowed sum of a pendant fibre is positive. -/
theorem pendant_pos {m : ℕ} (hm : 2 ≤ m) (C : Finset ℕ) (hC : C.card = m) (R : ℕ → Prop)
    [DecidablePred R] (hR : ∀ c ∈ C, ∀ c' ∈ C, R c → R c' → c = c')
    (θ : ℕ → ℝ) (hθ : ∀ c ∈ C, 0 < θ c) : 0 < ∑ c ∈ C with ¬ R c, θ c := by
  apply Finset.sum_pos (fun c hc => hθ c (Finset.mem_filter.mp hc).1)
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hne
  have : C.card ≤ 1 := Finset.card_le_one.mpr fun a ha b hb =>
    hR a ha b hb (not_not.mp (hne ha)) (not_not.mp (hne hb))
  omega

end Outerplanar
