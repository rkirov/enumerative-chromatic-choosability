/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.Cover

/-!
# The thread theorem for sections that are matched or cut on every edge

`Cover.capGE_of_thread` is a variant of the one-thread theorem `Cover.capGE_of_witness`: the
section `b` is, on every edge, either matched or cut at both of its ends, and the law lives on
the nonempty sets with no two cyclically consecutive elements. No hypothesis on the capacity of
the cover without `b` is needed, because the empty set carries no mass.
-/

namespace Outerplanar

open Finset

namespace Cover

variable {n : ℕ} [NeZero n] (P : Cover n)

open Classical in
/-- **The thread theorem.** If a `k`-fold partial cover has a section `b` that on every edge is
matched or cut at both ends, then a law on the nonempty sets without two consecutive elements,
with all marginals `1 / k`, whose entropy relative to `arcW (k - 1)` is at least `log C`, shows
that the capacity is at least `C`. -/
theorem capGE_of_thread {k : ℕ} (hk : 3 ≤ k) (hcard : ∀ i, (P.F i).card = k)
    (hM : P.IsMatching) {b : Fin n → ℕ} (hb1 : ∀ i, b i ∈ P.F i)
    (hb2 : ∀ i, P.M i (b i) (b (i + 1)) ∨
      ((∀ y ∈ P.F (i + 1), ¬ P.M i (b i) y) ∧ (∀ x ∈ P.F i, ¬ P.M i x (b (i + 1)))))
    {C : ℝ} (hC : 0 < C) (p : Finset (Fin n) → ℝ) (hp0 : ∀ J, 0 ≤ p J)
    (hpgood : ∀ J, 0 < p J → J ≠ ∅ ∧ (∀ i, i ∈ J → i + 1 ∉ J) ∧ 0 < arcW (k - 1) J)
    (hpsum : ∑ J, p J = 1) (hpmarg : ∀ i, ∑ J with i ∈ J, p J = 1 / (k : ℝ))
    (hpent : Real.log C ≤ ∑ J, p J * Real.log (arcW (k - 1) J / p J))
    (b' : Fin n → ℕ) : P.CapGE univ b' C := by
  intro w hw
  have hZb : P.Z univ b' w = P.Z univ b w := by rw [Z, Z, P.cols_univ b' b]
  rw [hZb]
  have hwpos : ∀ i, ∀ c ∈ P.F i, 0 < w i c := fun i => (hw i (mem_univ i)).1
  set u : Fin n → ℝ := fun i => w i (b i) with hu_def
  have hu : ∀ i, 0 < u i := fun i => hwpos i _ (hb1 i)
  have hk1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hkpos : (0 : ℝ) < (k : ℝ) - 1 := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  -- the cover without `b`
  have hFE : ∀ i, (P.erase b).F i = (P.F i).erase (b i) := fun _ => rfl
  have hcardE : ∀ i, ((P.erase b).F i).card = k - 1 := fun i => by
    rw [hFE, Finset.card_erase_of_mem (hb1 i), hcard]
  have hME : (P.erase b).IsMatching := fun i =>
    ⟨fun x hx y hy y' hy' => (hM i).1 x (Finset.mem_of_mem_erase hx) y
        (Finset.mem_of_mem_erase hy) y' (Finset.mem_of_mem_erase hy'),
      fun x hx x' hx' y hy => (hM i).2 x (Finset.mem_of_mem_erase hx) x'
        (Finset.mem_of_mem_erase hx') y (Finset.mem_of_mem_erase hy)⟩
  have hwE : ∀ i, ∀ c ∈ (P.erase b).F i, 0 < w i c := fun i c hc =>
    hwpos i c (Finset.mem_of_mem_erase hc)
  have hgm : ∀ i, Real.log (gmean ((P.erase b).F i) (w i))
      = -(((k : ℝ) - 1)⁻¹ * Real.log (u i)) := by
    intro i
    rw [log_gmean, hcardE, hk1, hFE]
    have h1 : ∑ c ∈ P.F i, Real.log (w i c) = 0 := by
      rw [← Real.log_prod (fun c hc => (hwpos i c hc).ne'), (hw i (mem_univ i)).2, Real.log_one]
    rw [← Finset.add_sum_erase _ _ (hb1 i)] at h1
    have h2 : ∑ c ∈ (P.F i).erase (b i), Real.log (w i c) = -Real.log (u i) := by
      rw [hu_def]; linarith
    rw [h2]; ring
  -- the colourings, sorted by the set of vertices coloured `b`
  let Jset : (Fin n → ℕ) → Finset (Fin n) := fun f => univ.filter fun i => f i = b i
  let T : Finset (Fin n) → ℝ := fun J =>
    ∑ f ∈ (P.cols univ b).filter (fun f => Jset f = J), ∏ i, w i (f i)
  have hZT : P.Z univ b w = ∑ J, T J := (Finset.sum_fiberwise _ Jset _).symm
  have hterm : ∀ f ∈ P.cols univ b, 0 ≤ ∏ i, w i (f i) := fun f hf =>
    Finset.prod_nonneg fun i _ => (hwpos i _ (((P.mem_cols.mp hf).1 i).1 (mem_univ i))).le
  have hT0 : ∀ J, 0 ≤ T J := fun J =>
    Finset.sum_nonneg fun f hf => hterm f (Finset.mem_filter.mp hf).1
  let G : Finset (Fin n) → ℝ := fun J => ∏ i ∈ Jᶜ, gmean ((P.erase b).F i) (w i)
  have hGpos : ∀ J, 0 < G J := fun J => Finset.prod_pos fun i _ => gmean_pos _ _
  let τ : Finset (Fin n) → ℝ := fun J => (∏ i ∈ J, u i) * (arcW (k - 1) J * G J)
  have hUpos : ∀ J : Finset (Fin n), 0 < ∏ i ∈ J, u i := fun J => Finset.prod_pos fun i _ => hu i
  have hτ : ∀ J, 0 < p J → τ J ≤ T J := by
    intro J hpJ
    obtain ⟨hJ, hgood, -⟩ := hpgood J hpJ
    have hsub : (P.erase b).cols Jᶜ b ⊆ (P.cols univ b).filter (fun f => Jset f = J) := by
      intro f hf
      have hf' := (P.erase b).mem_cols.mp hf
      have hin : ∀ t, t ∈ J → f t = b t := fun t ht => (hf'.1 t).2 (by simpa using ht)
      have hout : ∀ t, t ∉ J → f t ∈ P.F t ∧ f t ≠ b t := fun t ht => by
        have := (hf'.1 t).1 (by simpa using ht)
        rw [hFE] at this
        exact ⟨Finset.mem_of_mem_erase this, Finset.ne_of_mem_erase this⟩
      rw [Finset.mem_filter, mem_cols]
      refine ⟨⟨fun t => ⟨fun _ => ?_, fun h => absurd (mem_univ t) h⟩, fun t _ _ => ?_⟩, ?_⟩
      · by_cases ht : t ∈ J
        · rw [hin t ht]; exact hb1 t
        · exact (hout t ht).1
      · by_cases ht : t ∈ J <;> by_cases ht1 : t + 1 ∈ J
        · exact absurd ht1 (hgood t ht)
        · rw [hin t ht]
          rcases hb2 t with hmt | hcut
          · intro hMx
            exact (hout _ ht1).2 ((hM t).1 (b t) (hb1 t) _ (hout _ ht1).1 _ (hb1 _) hMx hmt)
          · exact hcut.1 _ (hout _ ht1).1
        · rw [hin _ ht1]
          rcases hb2 t with hmt | hcut
          · intro hMx
            exact (hout _ ht).2 ((hM t).2 _ (hout _ ht).1 (b t) (hb1 t) _ (hb1 _) hMx hmt)
          · exact hcut.2 _ (hout _ ht).1
        · exact hf'.2 t (by simpa using ht) (by simpa using ht1)
      · ext t
        simp only [Jset, Finset.mem_filter, mem_univ, true_and]
        exact ⟨fun h => by_contra fun ht => (hout t ht).2 h, hin t⟩
    have hZ : (∏ i ∈ J, u i) * (P.erase b).Z Jᶜ b w ≤ T J := by
      rw [Z, Finset.mul_sum]
      calc ∑ f ∈ (P.erase b).cols Jᶜ b, (∏ i ∈ J, u i) * ∏ i ∈ Jᶜ, w i (f i)
          = ∑ f ∈ (P.erase b).cols Jᶜ b, ∏ i, w i (f i) := by
            refine Finset.sum_congr rfl fun f hf => ?_
            rw [← Finset.prod_mul_prod_compl J fun i => w i (f i)]
            congr 1
            refine Finset.prod_congr rfl fun i hi => ?_
            rw [((((P.erase b).mem_cols.mp hf).1 i).2 (by simpa using hi))]
        _ ≤ T J := Finset.sum_le_sum_of_subset_of_nonneg hsub fun f hf _ =>
            hterm f (Finset.mem_filter.mp hf).1
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (hUpos J).le) hZ
    have hne : Jᶜ ≠ univ := by
      intro h
      exact hJ (by simpa using h)
    have := (P.erase b).arc_le_Z (m := k - 1) (by omega) hcardE hME b _ Jᶜ rfl hne w
      (fun i _ => hwE i)
    have hprod : (∏ i ∈ Jᶜ, if i - 1 ∈ Jᶜ then ((k - 1 : ℕ) : ℝ) - 1 else ((k - 1 : ℕ) : ℝ))
        = arcW (k - 1) J := by
      rw [arcW]
      refine Finset.prod_congr rfl fun i _ => ?_
      by_cases h : i - 1 ∈ J <;> simp [h]
    rw [hprod] at this
    exact this
  have hτpos : ∀ J, 0 < p J → 0 < τ J := fun J hpJ =>
    mul_pos (hUpos J) (mul_pos (hpgood J hpJ).2.2 (hGpos J))
  -- Gibbs
  have hg := gibbs univ p T (fun J _ => hp0 J) hpsum
    (fun J _ hpJ => lt_of_lt_of_le (hτpos J hpJ) (hτ J hpJ)) (fun J _ => hT0 J)
  rw [← hZT] at hg
  have hZpos : 0 < P.Z univ b w := by
    obtain ⟨J, -, hpJ⟩ : ∃ J ∈ (univ : Finset (Finset (Fin n))), 0 < p J := by
      by_contra h
      have : ∑ J, p J = 0 := Finset.sum_eq_zero fun J hJ =>
        le_antisymm (not_lt.mp fun hlt => h ⟨J, hJ, hlt⟩) (hp0 J)
      linarith
    rw [hZT]
    exact lt_of_lt_of_le (lt_of_lt_of_le (hτpos J hpJ) (hτ J hpJ))
      (Finset.single_le_sum (fun J _ => hT0 J) (mem_univ J))
  have h1 : ∑ J, p J * Real.log (τ J / p J) ≤ ∑ J, p J * Real.log (T J / p J) :=
    Finset.sum_le_sum fun J _ => by
      rcases (hp0 J).eq_or_lt with h | h
      · rw [← h]; simp
      · exact mul_le_mul_of_nonneg_left (Real.log_le_log (div_pos (hτpos J h) h)
          (div_le_div_of_nonneg_right (hτ J h) h.le)) h.le
  have h2 : ∀ J, p J * Real.log (τ J / p J) = p J * Real.log (arcW (k - 1) J / p J)
      + (p J * ∑ i ∈ J, Real.log (u i)
        - ((k : ℝ) - 1)⁻¹ * (p J * ∑ i ∈ Jᶜ, Real.log (u i))) := by
    intro J
    rcases (hp0 J).eq_or_lt with h | h
    · rw [← h]; simp
    · have hgpos := (hpgood J h).2.2
      have e1 : τ J / p J = (∏ i ∈ J, u i) * ((arcW (k - 1) J / p J) * G J) := by
        simp only [τ]; field_simp
      rw [e1, Real.log_mul (hUpos J).ne' (mul_pos (div_pos hgpos h) (hGpos J)).ne',
        Real.log_mul (div_pos hgpos h).ne' (hGpos J).ne',
        Real.log_prod (fun i _ => (hu i).ne'), Real.log_prod (fun i _ => (gmean_pos _ _).ne'),
        Finset.sum_congr rfl fun i _ => hgm i, Finset.sum_neg_distrib, ← Finset.mul_sum]
      ring
  have h3 : ∑ J, p J * Real.log (τ J / p J)
      = ∑ J, p J * Real.log (arcW (k - 1) J / p J) := by
    rw [Finset.sum_congr rfl fun J _ => h2 J, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, sum_mul_sum_mem, sum_mul_sum_compl, hpsum]
    have hz : ∑ i, (∑ J with i ∈ J, p J) * Real.log (u i)
        - ((k : ℝ) - 1)⁻¹ * ∑ i, (1 - ∑ J with i ∈ J, p J) * Real.log (u i) = 0 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [hpmarg i]
      have hk0 : (k : ℝ) ≠ 0 := by
        have : (3 : ℝ) ≤ k := by exact_mod_cast hk
        linarith
      field_simp
      ring
    rw [hz, add_zero]
  have : Real.log C ≤ Real.log (P.Z univ b w) := by linarith
  exact (Real.log_le_log_iff hC hZpos).mp this

end Cover

end Outerplanar
