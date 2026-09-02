import Mathlib

/-!
# Certificate → obligation bridge (one seam).

From the integer `checkSeam` data (row marginals, per-entry fourth-root witness, `R₊⁴ρ<1`)
construct the real `law`/`K`/`r` and prove exactly the per-seam hypotheses that
`entropy_half_from_card` consumes: stochastic `K`, `hentry`, and `hRp` (via `seam_cert_rational`).
-/

open Real Finset

namespace Grid3.Three.SeamBridge

noncomputable def rho : ℝ := (5 + Real.sqrt 17) / 2

theorem seam_cert_rational (r : ℚ) (hr0 : 0 ≤ r) (h1 : 5 * r < 2)
    (h2 : 17 * r ^ 2 < (2 - 5 * r) ^ 2) : (r : ℝ) * rho < 1 := by
  have hrr : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr0
  have h1r : 5 * (r : ℝ) < 2 := by exact_mod_cast h1
  have h2r : 17 * (r : ℝ) ^ 2 < (2 - 5 * (r : ℝ)) ^ 2 := by exact_mod_cast h2
  have hpos : 0 < 2 - 5 * (r : ℝ) := by linarith
  have hsq : ((r : ℝ) * Real.sqrt 17) ^ 2 < (2 - 5 * (r : ℝ)) ^ 2 := by
    have e : ((r : ℝ) * Real.sqrt 17) ^ 2 = 17 * (r : ℝ) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 17)]; ring
    rw [e]; exact h2r
  have hs : (r : ℝ) * Real.sqrt 17 < 2 - 5 * (r : ℝ) := by
    nlinarith [hsq, hpos, mul_nonneg hrr (Real.sqrt_nonneg 17)]
  rw [rho]; nlinarith [hs]

/-- Scaling helper for the rational seam check. -/
theorem ratcond (a b : ℚ) (hb : 0 < b) (h1 : 5 * a < 2 * b) (h2 : 17 * a ^ 2 < (2 * b - 5 * a) ^ 2) :
    5 * (a / b) < 2 ∧ 17 * (a / b) ^ 2 < (2 - 5 * (a / b)) ^ 2 := by
  have hb2 : (0 : ℚ) < b ^ 2 := by positivity
  refine ⟨?_, ?_⟩
  · rw [← mul_div_assoc, div_lt_iff₀ hb]; linarith
  · have e1 : (17 : ℚ) * (a / b) ^ 2 = 17 * a ^ 2 / b ^ 2 := by rw [div_pow]; ring
    have e2 : (2 - 5 * (a / b)) ^ 2 = (2 * b - 5 * a) ^ 2 / b ^ 2 := by
      rw [show (2 : ℚ) - 5 * (a / b) = (2 * b - 5 * a) / b by field_simp, div_pow]
    rw [e1, e2, div_lt_div_iff₀ hb2 hb2]
    exact mul_lt_mul_of_pos_right h2 hb2

/-- **One-seam bridge.**  Integer certificate ⇒ real `law`,`K`,`r` with the per-seam obligations. -/
theorem seam_bridge {ι κ : Type*} [Fintype ι] [Fintype κ]
    (lawc : ι → ℕ) (Xint : ι → κ → ℕ) (kwit : ι → κ → ℕ)
    (hlawpos : ∀ c, 0 < lawc c)
    (hrow : ∀ c, ∑ s, Xint c s = lawc c * 1000)
    (cB : κ → ℕ) (hcol : ∀ t, ∑ c, Xint c t = cB t * 1000)
    (hentry : ∀ c s, Xint c s * 108 * (10 ^ 6) ^ 4 ≤ (kwit c s) ^ 4 * (108000 * lawc c))
    (hb1 : 5 * (∑ c, ∑ s, Xint c s * kwit c s) ^ 4 < 2 * (108000 * 10 ^ 6) ^ 4)
    (hb2 : 17 * (∑ c, ∑ s, Xint c s * kwit c s) ^ 8 <
      (2 * (108000 * 10 ^ 6) ^ 4 - 5 * (∑ c, ∑ s, Xint c s * kwit c s) ^ 4) ^ 2) :
    ∃ (law : ι → ℝ) (K : ι → κ → ℝ) (r : ι → κ → ℝ),
      (∀ c, 0 ≤ law c) ∧ (∀ c s, 0 ≤ K c s) ∧ (∀ c, ∑ s, K c s = 1) ∧
      (∀ c s, 0 ≤ r c s) ∧
      (∀ c s, law c * K c s ≤ (r c s) ^ 4 * law c) ∧
      ((∑ c, ∑ s, law c * K c s * r c s) ^ 4 * rho < 1) ∧
      (∀ t, ∑ c, law c * K c t = (cB t : ℝ) / 108) := by
  refine ⟨fun c => (lawc c : ℝ) / 108,
          fun c s => (Xint c s : ℝ) / (1000 * lawc c),
          fun c s => (kwit c s : ℝ) / (10 ^ 6), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c; positivity
  · intro c s; positivity
  · intro c
    have hlc : (0 : ℝ) < 1000 * (lawc c : ℝ) :=
      mul_pos (by norm_num) (by exact_mod_cast hlawpos c)
    rw [← Finset.sum_div]
    have hs : (∑ s, (Xint c s : ℝ)) = (lawc c : ℝ) * 1000 := by exact_mod_cast hrow c
    rw [hs, mul_comm (lawc c : ℝ) 1000, div_self (ne_of_gt hlc)]
  · intro c s; positivity
  · intro c s
    have key : (Xint c s : ℝ) * 108 * (10 ^ 6) ^ 4 ≤ (kwit c s : ℝ) ^ 4 * (108000 * lawc c) := by
      exact_mod_cast hentry c s
    have hlc : (0 : ℝ) < (lawc c : ℝ) := by exact_mod_cast hlawpos c
    have hlawK : (lawc c : ℝ) / 108 * ((Xint c s : ℝ) / (1000 * lawc c)) = (Xint c s : ℝ) / 108000 := by
      field_simp; ring
    rw [hlawK, div_pow, div_mul_div_comm, div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith [key]
  · set NR : ℕ := ∑ c, ∑ s, Xint c s * kwit c s with hNR
    have hterm : ∀ c s, ((lawc c : ℝ) / 108) * ((Xint c s : ℝ) / (1000 * lawc c))
          * ((kwit c s : ℝ) / (10 ^ 6)) = (Xint c s * kwit c s : ℝ) / (108000 * 10 ^ 6) := by
      intro c s
      have hlc : (lawc c : ℝ) ≠ 0 := by exact_mod_cast (hlawpos c).ne'
      field_simp; ring
    have hsum : (∑ c, ∑ s, ((lawc c : ℝ) / 108) * ((Xint c s : ℝ) / (1000 * lawc c))
          * ((kwit c s : ℝ) / (10 ^ 6))) = (NR : ℝ) / (108000 * 10 ^ 6) := by
      simp_rw [hterm, ← Finset.sum_div]
      rw [hNR]; push_cast; ring
    rw [hsum]
    -- ((NR:ℝ)/Dr)^4 * rho < 1  via seam_cert_rational with r_rat = NR^4/Dr^4
    have hDr : (0 : ℚ) < (108000 * 10 ^ 6 : ℚ) ^ 4 := by norm_num
    have hDrR : ((108000 * 10 ^ 6 : ℚ) ^ 4 : ℝ) = ((108000 : ℝ) * 10 ^ 6) ^ 4 := by push_cast; ring
    have hcast : ((NR : ℝ) / (108000 * 10 ^ 6)) ^ 4
        = (((NR : ℚ) ^ 4 / (108000 * 10 ^ 6 : ℚ) ^ 4 : ℚ) : ℝ) := by push_cast; ring
    rw [hcast]
    have hb1q : (5 : ℚ) * (NR : ℚ) ^ 4 < 2 * (108000 * 10 ^ 6 : ℚ) ^ 4 := by exact_mod_cast hb1
    have hle : 5 * NR ^ 4 ≤ 2 * (108000 * 10 ^ 6) ^ 4 := le_of_lt hb1
    have hb2q : (17 : ℚ) * ((NR : ℚ) ^ 4) ^ 2 <
        (2 * (108000 * 10 ^ 6 : ℚ) ^ 4 - 5 * (NR : ℚ) ^ 4) ^ 2 := by
      have hsub : ((2 * (108000 * 10 ^ 6) ^ 4 - 5 * NR ^ 4 : ℕ) : ℚ)
          = 2 * (108000 * 10 ^ 6 : ℚ) ^ 4 - 5 * (NR : ℚ) ^ 4 := by
        rw [Nat.cast_sub hle]; push_cast; ring
      calc (17 : ℚ) * ((NR : ℚ) ^ 4) ^ 2
          = ((17 * NR ^ 8 : ℕ) : ℚ) := by push_cast; ring
        _ < (((2 * (108000 * 10 ^ 6) ^ 4 - 5 * NR ^ 4) ^ 2 : ℕ) : ℚ) := by exact_mod_cast hb2
        _ = (2 * (108000 * 10 ^ 6 : ℚ) ^ 4 - 5 * (NR : ℚ) ^ 4) ^ 2 := by rw [Nat.cast_pow, hsub]
    obtain ⟨c1, c2⟩ := ratcond ((NR : ℚ) ^ 4) ((108000 * 10 ^ 6 : ℚ) ^ 4) (by positivity) hb1q hb2q
    exact seam_cert_rational _ (by positivity) c1 c2
  · -- right marginal: ∑_c law·K = cB/108
    intro t
    have hlawK : ∀ c, (lawc c : ℝ) / 108 * ((Xint c t : ℝ) / (1000 * lawc c)) = (Xint c t : ℝ) / 108000 := by
      intro c
      have hlc : (lawc c : ℝ) ≠ 0 := by exact_mod_cast (hlawpos c).ne'
      field_simp; ring
    simp_rw [hlawK, ← Finset.sum_div]
    have hs : (∑ c, (Xint c t : ℝ)) = (cB t : ℝ) * 1000 := by exact_mod_cast hcol t
    rw [hs]; ring

end Grid3.Three.SeamBridge
