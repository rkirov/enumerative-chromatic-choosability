/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.State6

/-!
# Height four, `k = 6`: the seam inequality from a certificate

As `Seam.lean`, with the `k = 6` gain `Λ₆` (`State6.lean`) and the sharp fibre bounds
(`Fibre6.lean`). A one-colour pin weighs at most `q = 1/(1 + 2ρ) = 250/737` of the uniform weights
on a middle row and `qₑ = 1/(1 + 3ρ) = 500/1961` on an end row (`ρ = 487/500`), and never more than
the whole. So the averaged gain is at least `F6val` (pattern term `η(1 + 4q)T`) or `F6cap` (pattern
term `209/14123`), functions of the three mismatches alone.
-/

namespace GridGen.Four

open Finset Real

/-- The sharp fibre shares at `k = 6`: middle rows and end rows. -/
noncomputable def qm6 : ℝ := 250 / 737
noncomputable def qe6 : ℝ := 500 / 1961

/-- The common part of the averaged gain at `k = 6`. -/
noncomputable def F6core (μ2 μ3 μ4 : ℝ) : ℝ :=
  log (1 + μ2 / kA (((6 : ℕ) : ℝ) - 1)) + log (1 + μ3 / kA (((6 : ℕ) : ℝ) - 1))
    + log (1 + μ4 / kA (((6 : ℕ) : ℝ) - 1))
    - (zslope (((6 : ℕ) : ℝ) - 1) μ2 * (min (qe6 * μ2) 1 + min (qm6 * μ2) 1)
      + zslope (((6 : ℕ) : ℝ) - 1) μ3 * (2 * min (qm6 * μ3) 1)
      + zslope (((6 : ℕ) : ℝ) - 1) μ4 * (min (qm6 * μ4) 1 + min (qe6 * μ4) 1))
    - J3 μ2 μ3 * ((μ2 + 1) * min (μ3 + 1) ((((6 : ℕ) : ℝ) - 1) + 3 - μ2)
        / ((((6 : ℕ) : ℝ) - 1) ^ 2 * ((((6 : ℕ) : ℝ) - 1) - 1) ^ 2)
        + ku3 (((6 : ℕ) : ℝ) - 1) * qe6)
    - J4 μ2 μ3 μ4 * ((min ((μ3 + 1) * (μ4 + 1))
          (((((6 : ℕ) : ℝ) - 1) + 3 - μ3) * ((((6 : ℕ) : ℝ) - 1) + 3 - μ4)) + (μ4 + 1))
        / ((((6 : ℕ) : ℝ) - 1) * ((((6 : ℕ) : ℝ) - 1) - 1) ^ 3)
        + ku4e (((6 : ℕ) : ℝ) - 1) * qe6 + ku4b (((6 : ℕ) : ℝ) - 1))

/-- The averaged gain at `k = 6`, with the uncapped pattern term. -/
noncomputable def F6val (μ2 μ3 μ4 : ℝ) : ℝ :=
  F6core μ2 μ3 μ4 - eta 6 * (1 + 4 * qm6) * (μ2 + 2 * μ3 + μ4)

/-- The averaged gain at `k = 6`, with the pattern term capped at `209/14123`. -/
noncomputable def F6cap (μ2 μ3 μ4 : ℝ) : ℝ := F6core μ2 μ3 μ4 - 209 / 14123

theorem zslope_nonneg {n μ : ℝ} (hn : 2 ≤ n) (hμ : 0 ≤ μ) : 0 ≤ zslope n μ := by
  unfold zslope
  have hA : 0 < n ^ 2 - n + 1 + μ - 2 := by nlinarith
  refine le_min (by apply div_nonneg zero_le_one; nlinarith) ?_
  apply div_nonneg _ zero_le_two
  apply Real.log_nonneg
  rw [le_div_iff₀ hA]; linarith

/-- The gain at `k = 6` as a constant plus the state bits. -/
theorem Lamc6_eq (B₁ B₂ B₃ B₄ : Finset ℕ) (s : T4) :
    Lamc6 B₁ B₂ B₃ B₄ s =
      (log (1 + mu 6 B₁ B₂ / kA (((6 : ℕ) : ℝ) - 1)) + log (1 + mu 6 B₂ B₃ / kA (((6 : ℕ) : ℝ) - 1))
        + log (1 + mu 6 B₃ B₄ / kA (((6 : ℕ) : ℝ) - 1))
        - J3 (mu 6 B₁ B₂) (mu 6 B₂ B₃) * ((mu 6 B₁ B₂ + 1)
            * min (mu 6 B₂ B₃ + 1) ((((6 : ℕ) : ℝ) - 1) + 3 - mu 6 B₁ B₂)
            / ((((6 : ℕ) : ℝ) - 1) ^ 2 * ((((6 : ℕ) : ℝ) - 1) - 1) ^ 2))
        - J4 (mu 6 B₁ B₂) (mu 6 B₂ B₃) (mu 6 B₃ B₄) * ((min ((mu 6 B₂ B₃ + 1) * (mu 6 B₃ B₄ + 1))
            (((((6 : ℕ) : ℝ) - 1) + 3 - mu 6 B₂ B₃) * ((((6 : ℕ) : ℝ) - 1) + 3 - mu 6 B₃ B₄))
            + (mu 6 B₃ B₄ + 1)) / ((((6 : ℕ) : ℝ) - 1) * ((((6 : ℕ) : ℝ) - 1) - 1) ^ 3)
            + ku4b (((6 : ℕ) : ℝ) - 1)))
      - (zslope (((6 : ℕ) : ℝ) - 1) (mu 6 B₁ B₂) * zz B₁ B₂ (r1 s) (r2 s)
        + zslope (((6 : ℕ) : ℝ) - 1) (mu 6 B₂ B₃) * zz B₂ B₃ (r2 s) (r3 s)
        + zslope (((6 : ℕ) : ℝ) - 1) (mu 6 B₃ B₄) * zz B₃ B₄ (r3 s) (r4 s))
      - J3 (mu 6 B₁ B₂) (mu 6 B₂ B₃) * ku3 (((6 : ℕ) : ℝ) - 1) * c13 s
      - J4 (mu 6 B₁ B₂) (mu 6 B₂ B₃) (mu 6 B₃ B₄) * ku4e (((6 : ℕ) : ℝ) - 1) * c24 s
      + (kβ0 (((6 : ℕ) : ℝ) - 1) - kb3 (((6 : ℕ) : ℝ) - 1) - kb4 (((6 : ℕ) : ℝ) - 1))
          * (hb B₁ (r1 s) + hb B₂ (r2 s) + hb B₃ (r3 s) + hb B₄ (r4 s))
      - min (eta 6 * PS 6 B₁ B₂ B₃ B₄ s) (209 / 14123) := by
  unfold Lamc6 CB6 countBound6
  ring

/-- The bonus coefficients at `k = 6`. -/
theorem bonus_coef6 :
    0 ≤ kβ0 (((6 : ℕ) : ℝ) - 1) - kb3 (((6 : ℕ) : ℝ) - 1) - kb4 (((6 : ℕ) : ℝ) - 1) - 4 * eta 6 ∧
    0 ≤ kβ0 (((6 : ℕ) : ℝ) - 1) - kb3 (((6 : ℕ) : ℝ) - 1) - kb4 (((6 : ℕ) : ℝ) - 1) := by
  norm_num [kβ0, kb3, kb4, ku3, ku4e, ku4b, kt, kA, eta, rho_six]

/-- **A one-colour pin bound**, from the per-colour fibre: `Σ u·[g ∈ D] ≤ min (q|D|, 1) · Σ u`. -/
theorem pin_min {Ω : Finset T4} (u : T4 → ℝ) (hu0 : ∀ t, 0 ≤ u t) (g : T4 → ℕ) {q : ℝ}
    (hc : ∀ c, ∑ t ∈ Ω.filter (fun t => g t = c), u t ≤ q * ∑ t ∈ Ω, u t) (D : Finset ℕ) :
    ∑ t ∈ Ω, u t * (if g t ∈ D then 1 else 0) ≤ min (q * D.card) 1 * ∑ t ∈ Ω, u t := by
  have hW : 0 ≤ ∑ t ∈ Ω, u t := Finset.sum_nonneg (fun t _ => hu0 t)
  have h1 := fibre_mem u g (m := 1) (R := q) (fun c => by rw [one_mul]; exact hc c) D
  rw [one_mul] at h1
  have h2 : ∑ t ∈ Ω, u t * (if g t ∈ D then 1 else 0) ≤ ∑ t ∈ Ω, u t :=
    Finset.sum_le_sum (fun t _ => by split_ifs <;> simp [hu0 t])
  rcases le_total (q * D.card) 1 with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h, one_mul]; exact h2

/-- **The seam inequality at `k = 6` from either certificate**, for one system of lists. -/
theorem seam_of_cert6 {w : Wt} (hw : InBox 6 w) {X₁ X₂ X₃ X₄ B₁ B₂ B₃ B₄ : Finset ℕ}
    (hX₁ : 6 - 1 ≤ X₁.card) (hX₂ : 6 - 1 ≤ X₂.card) (hX₃ : 6 - 1 ≤ X₃.card)
    (hX₄ : 6 - 1 ≤ X₄.card)
    (hB₁ : B₁.card = 6) (hB₂ : B₂.card = 6) (hB₃ : B₃.card = 6) (hB₄ : B₄.card = 6)
    (hcert : 0 ≤ F6val (mu 6 B₁ B₂) (mu 6 B₂ B₃) (mu 6 B₃ B₄)
      ∨ 0 ≤ F6cap (mu 6 B₁ B₂) (mu 6 B₂ B₃) (mu 6 B₃ B₄)) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄, GU 6 w s ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄, GB w B₁ B₂ B₃ B₄ s := by
  have hρ6 := rho_six
  set Ω := sts X₁ X₂ X₃ X₄ with hΩ
  set u : T4 → ℝ := GU 6 w with hu
  have hu0 : ∀ t, 0 ≤ u t := GU_nonneg (by norm_num) hw
  have hR : ∀ t ∈ Ω, ∀ t' ∈ Ω, u t ≤ (500 / 487) * u t' := fun t ht t' ht' => by
    have := GU_ratio (by norm_num) hw (proper_of_mem_sts ht) (proper_of_mem_sts ht')
    rw [hρ6] at this; norm_num at this ⊢; linarith
  set W := ∑ s ∈ Ω, u s with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg (fun s _ => hu0 s)
  -- the sharp pins
  have pe : ∀ (P : T4 → Prop) [DecidablePred P],
      (500 / 487 + (((6 - 2 : ℕ) : ℝ) - 1)) * ∑ t ∈ Ω.filter P, u t ≤ 500 / 487 * W →
      ∑ t ∈ Ω.filter P, u t ≤ qe6 * W := by
    intro P _ h; unfold qe6; norm_num at h ⊢; linarith
  have pm : ∀ (P : T4 → Prop) [DecidablePred P],
      (500 / 487 + (((6 - 3 : ℕ) : ℝ) - 1)) * ∑ t ∈ Ω.filter P, u t ≤ 500 / 487 * W →
      ∑ t ∈ Ω.filter P, u t ≤ qm6 * W := by
    intro P _ h; unfold qm6; norm_num at h ⊢; linarith
  have f1 : ∀ c, ∑ t ∈ Ω.filter (fun t => r1 t = c), u t ≤ qe6 * W := fun c =>
    pe _ (fibre_sts1_sharp u hu0 (fun t => r1 t = c) (by norm_num) hX₁ (by norm_num) hR
      (fun _ => c) (fun _ _ => rfl) (fun _ h => h))
  have f2 : ∀ c, ∑ t ∈ Ω.filter (fun t => r2 t = c), u t ≤ qm6 * W := fun c =>
    pm _ (fibre_sts2_sharp u hu0 (fun t => r2 t = c) (by norm_num) hX₂ (by norm_num) hR
      (fun _ => c) (fun _ _ => rfl) (fun _ h => h))
  have f3 : ∀ c, ∑ t ∈ Ω.filter (fun t => r3 t = c), u t ≤ qm6 * W := fun c =>
    pm _ (fibre_sts3_sharp u hu0 (fun t => r3 t = c) (by norm_num) hX₃ (by norm_num) hR
      (fun _ => c) (fun _ _ => rfl) (fun _ h => h))
  have f4 : ∀ c, ∑ t ∈ Ω.filter (fun t => r4 t = c), u t ≤ qe6 * W := fun c =>
    pe _ (fibre_sts4_sharp u hu0 (fun t => r4 t = c) (by norm_num) hX₄ (by norm_num) hR
      (fun _ => c) (fun _ _ => rfl) (fun _ h => h))
  have f2m : ∀ c, ∑ t ∈ Ω.filter (fun t => r2 t = c), u t ≤ qm6 * W := f2
  -- summing the bound for one state
  have hsum : ∑ s ∈ Ω, u s * (1 + Lamc6 B₁ B₂ B₃ B₄ s) ≤ ∑ s ∈ Ω, GB w B₁ B₂ B₃ B₄ s :=
    Finset.sum_le_sum (fun s hs => state_bound6 hw hB₁ hB₂ hB₃ hB₄ (proper_of_mem_sts hs))
  suffices h : 0 ≤ ∑ s ∈ Ω, u s * Lamc6 B₁ B₂ B₃ B₄ s by
    have e : ∑ s ∈ Ω, u s * (1 + Lamc6 B₁ B₂ B₃ B₄ s)
        = ∑ s ∈ Ω, u s + ∑ s ∈ Ω, u s * Lamc6 B₁ B₂ B₃ B₄ s := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun s _ => by ring)
    linarith
  -- names for the constants
  set M2 := mu 6 B₁ B₂ with hM2
  set M3 := mu 6 B₂ B₃ with hM3
  set M4 := mu 6 B₃ B₄ with hM4
  have hM20 : 0 ≤ M2 := mu_nonneg hB₁
  have hM30 : 0 ≤ M3 := mu_nonneg hB₂
  have hM40 : 0 ≤ M4 := mu_nonneg hB₃
  set n : ℝ := ((6 : ℕ) : ℝ) - 1 with hn
  have hn5 : n = 5 := by rw [hn]; norm_num
  set K0 := log (1 + M2 / kA n) + log (1 + M3 / kA n) + log (1 + M4 / kA n)
      - J3 M2 M3 * ((M2 + 1) * min (M3 + 1) (n + 3 - M2) / (n ^ 2 * (n - 1) ^ 2))
      - J4 M2 M3 M4 * ((min ((M3 + 1) * (M4 + 1)) ((n + 3 - M3) * (n + 3 - M4)) + (M4 + 1))
          / (n * (n - 1) ^ 3) + ku4b n) with hK0
  set s2 := zslope n M2 with hs2
  set s3 := zslope n M3 with hs3
  set s4 := zslope n M4 with hs4
  have hs20 : 0 ≤ s2 := zslope_nonneg (by rw [hn5]; norm_num) hM20
  have hs30 : 0 ≤ s3 := zslope_nonneg (by rw [hn5]; norm_num) hM30
  have hs40 : 0 ≤ s4 := zslope_nonneg (by rw [hn5]; norm_num) hM40
  set g3 := J3 M2 M3 * ku3 n with hg3
  set g4 := J4 M2 M3 M4 * ku4e n with hg4
  set βc := kβ0 n - kb3 n - kb4 n with hβc
  set cap : ℝ := 209 / 14123 with hcap
  -- the bit sums
  set Z2 := ∑ s ∈ Ω, u s * zz B₁ B₂ (r1 s) (r2 s) with hZ2
  set Z3 := ∑ s ∈ Ω, u s * zz B₂ B₃ (r2 s) (r3 s) with hZ3
  set Z4 := ∑ s ∈ Ω, u s * zz B₃ B₄ (r3 s) (r4 s) with hZ4
  set C13 := ∑ s ∈ Ω, u s * c13 s with hC13
  set C24 := ∑ s ∈ Ω, u s * c24 s with hC24
  set HH := ∑ s ∈ Ω, u s * (hb B₁ (r1 s) + hb B₂ (r2 s) + hb B₃ (r3 s) + hb B₄ (r4 s)) with hHH
  set XX := ∑ s ∈ Ω, u s * (xin B₁ B₂ (r1 s) + xin B₃ B₂ (r3 s) + xin B₄ B₂ (r4 s)) with hXX
  set MM := ∑ s ∈ Ω, u s * min (eta 6 * PS 6 B₁ B₂ B₃ B₄ s) cap with hMM
  have e : ∑ s ∈ Ω, u s * Lamc6 B₁ B₂ B₃ B₄ s
      = K0 * W - (s2 * Z2 + s3 * Z3 + s4 * Z4) - g3 * C13 - g4 * C24 + βc * HH - MM := by
    rw [hW, hZ2, hZ3, hZ4, hC13, hC24, hHH, hMM]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [Lamc6_eq]; ring
  rw [e]
  -- the cap, both ways
  have hMMc : MM ≤ cap * W := by
    rw [hMM, hW, Finset.mul_sum]
    exact Finset.sum_le_sum (fun s _ => by
      rw [mul_comm cap]; exact mul_le_mul_of_nonneg_left (min_le_right _ _) (hu0 s))
  have hMMη : MM ≤ eta 6 * ((M2 + 2 * M3 + M4) * W + 4 * HH + 4 * XX) := by
    have : eta 6 * ((M2 + 2 * M3 + M4) * W + 4 * HH + 4 * XX)
        = ∑ s ∈ Ω, u s * (eta 6 * PS 6 B₁ B₂ B₃ B₄ s) := by
      rw [hW, hHH, hXX]
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      unfold PS; ring
    rw [this, hMM]
    exact Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (min_le_left _ _) (hu0 s))
  -- the pinned sums
  have card_d : ∀ {B C : Finset ℕ}, B.card = 6 → ((B \ C).card : ℝ) = mu 6 B C :=
    fun hB => card_sdiff_mu hB _
  have zsplit : ∀ (B C : Finset ℕ) (g g' : T4 → ℕ), ∑ s ∈ Ω, u s * zz B C (g s) (g' s)
      = ∑ s ∈ Ω, u s * (if g s ∈ B \ C then 1 else 0)
        + ∑ s ∈ Ω, u s * (if g' s ∈ C \ B then 1 else 0) := by
    intro B C g g'
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun s _ => by rw [zz_eq]; ring)
  have bZ2 : Z2 ≤ (min (qe6 * M2) 1 + min (qm6 * M2) 1) * W := by
    rw [hZ2, zsplit]
    have b1 := pin_min u hu0 r1 f1 (B₁ \ B₂)
    have b2 := pin_min u hu0 r2 f2 (B₂ \ B₁)
    rw [card_d hB₁] at b1
    rw [card_d hB₂, mu_comm 6 B₂ B₁] at b2
    linarith
  have bZ3 : Z3 ≤ (2 * min (qm6 * M3) 1) * W := by
    rw [hZ3, zsplit]
    have b1 := pin_min u hu0 r2 f2 (B₂ \ B₃)
    have b2 := pin_min u hu0 r3 f3 (B₃ \ B₂)
    rw [card_d hB₂] at b1
    rw [card_d hB₃, mu_comm 6 B₃ B₂] at b2
    linarith
  have bZ4 : Z4 ≤ (min (qm6 * M4) 1 + min (qe6 * M4) 1) * W := by
    rw [hZ4, zsplit]
    have b1 := pin_min u hu0 r3 f3 (B₃ \ B₄)
    have b2 := pin_min u hu0 r4 f4 (B₄ \ B₃)
    rw [card_d hB₃] at b1
    rw [card_d hB₄, mu_comm 6 B₄ B₃] at b2
    linarith
  have bC13 : C13 ≤ qe6 * W := by
    rw [hC13]
    have : ∑ s ∈ Ω, u s * c13 s = ∑ s ∈ Ω.filter (fun t => r1 t = r3 t), u s := by
      rw [← sum_mul_ite]; rfl
    rw [this]
    exact pe _ (fibre_sts1_sharp u hu0 (fun t => r1 t = r3 t) (by norm_num) hX₁ (by norm_num) hR
      r3 (fun _ _ => rfl) (fun _ h => h))
  have bC24 : C24 ≤ qe6 * W := by
    rw [hC24]
    have : ∑ s ∈ Ω, u s * c24 s = ∑ s ∈ Ω.filter (fun t => r4 t = r2 t), u s := by
      rw [← sum_mul_ite]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      unfold c24; split_ifs <;> first | rfl | omega
    rw [this]
    exact pe _ (fibre_sts4_sharp u hu0 (fun t => r4 t = r2 t) (by norm_num) hX₄ (by norm_num) hR
      r2 (fun _ _ => rfl) (fun _ h => h))
  have bXX : XX ≤ qm6 * (M2 + 2 * M3 + M4) * W := by
    have e1 : XX = ∑ s ∈ Ω, u s * (if r1 s ∈ B₁ \ B₂ then 1 else 0)
        + ∑ s ∈ Ω, u s * (if r3 s ∈ B₃ \ B₂ then 1 else 0)
        + ∑ s ∈ Ω, u s * (if r4 s ∈ B₄ \ B₂ then 1 else 0) := by
      rw [hXX, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun s _ => by rw [xin_eq, xin_eq, xin_eq]; ring)
    have hqq : qe6 * W ≤ qm6 * W :=
      mul_le_mul_of_nonneg_right (by unfold qe6 qm6; norm_num) hW0
    have f1m : ∀ c, 1 * ∑ t ∈ Ω.filter (fun t => r1 t = c), u t ≤ qm6 * W := fun c => by
      rw [one_mul]; exact (f1 c).trans hqq
    have f4m : ∀ c, 1 * ∑ t ∈ Ω.filter (fun t => r4 t = c), u t ≤ qm6 * W := fun c => by
      rw [one_mul]; exact (f4 c).trans hqq
    have f3m : ∀ c, 1 * ∑ t ∈ Ω.filter (fun t => r3 t = c), u t ≤ qm6 * W := fun c => by
      rw [one_mul]; exact f3 c
    have b1 := fibre_mem u r1 f1m (B₁ \ B₂)
    have b3 := fibre_mem u r3 f3m (B₃ \ B₂)
    have b4 := fibre_mem u r4 f4m (B₄ \ B₂)
    rw [one_mul] at b1 b3 b4
    have t4 := card_sdiff_tri B₄ B₃ B₂
    rw [card_d hB₁] at b1
    rw [card_d hB₃, mu_comm 6 B₃ B₂] at b3
    rw [card_sdiff_mu hB₄ B₃, card_sdiff_mu hB₃ B₂, mu_comm 6 B₄ B₃, mu_comm 6 B₃ B₂] at t4
    have hq0 : (0 : ℝ) ≤ qm6 := by unfold qm6; norm_num
    have b4' : qm6 * ((B₄ \ B₂).card : ℝ) * W ≤ qm6 * (M4 + M3) * W :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left t4 hq0) hW0
    have ex : qm6 * (M2 + 2 * M3 + M4) * W
        = qm6 * M2 * W + qm6 * M3 * W + qm6 * (M4 + M3) * W := by ring
    rw [e1, ex]
    linarith
  have hbn : ∀ (B : Finset ℕ) (c : ℕ), 0 ≤ hb B c := fun B c => by
    unfold hb; split_ifs <;> norm_num
  have bHH : 0 ≤ HH := Finset.sum_nonneg (fun s _ => mul_nonneg (hu0 s)
    (add_nonneg (add_nonneg (add_nonneg (hbn _ _) (hbn _ _)) (hbn _ _)) (hbn _ _)))
  have hJ3 : 0 ≤ J3 M2 M3 := by unfold J3; split_ifs <;> norm_num
  have hJ4 : 0 ≤ J4 M2 M3 M4 := by unfold J4; split_ifs <;> norm_num
  have hku3 : 0 ≤ ku3 n := by rw [hn5]; norm_num [ku3, kt, kA]
  have hku4e : 0 ≤ ku4e n := by rw [hn5]; norm_num [ku4e, kt, kA]
  have hg30 : 0 ≤ g3 := mul_nonneg hJ3 hku3
  have hg40 : 0 ≤ g4 := mul_nonneg hJ4 hku4e
  obtain ⟨hβη, hβ⟩ := bonus_coef6
  have i1 := mul_le_mul_of_nonneg_left bZ2 hs20
  have i2 := mul_le_mul_of_nonneg_left bZ3 hs30
  have i3 := mul_le_mul_of_nonneg_left bZ4 hs40
  have i4 := mul_le_mul_of_nonneg_left bC13 hg30
  have i5 := mul_le_mul_of_nonneg_left bC24 hg40
  have hcore : W * F6core M2 M3 M4 = K0 * W - s2 * ((min (qe6 * M2) 1 + min (qm6 * M2) 1) * W)
      - s3 * ((2 * min (qm6 * M3) 1) * W) - s4 * ((min (qm6 * M4) 1 + min (qe6 * M4) 1) * W)
      - g3 * (qe6 * W) - g4 * (qe6 * W) := by
    rw [hK0, hg3, hg4, hs2, hs3, hs4, hn]; unfold F6core; ring
  rcases hcert with hF | hF
  · -- the uncapped certificate
    have hη0 : 0 ≤ eta 6 := by unfold eta; rw [hρ6]; norm_num
    have i6 := mul_le_mul_of_nonneg_left bXX (by linarith : (0 : ℝ) ≤ 4 * eta 6)
    have i7 : 0 ≤ (βc - 4 * eta 6) * HH := mul_nonneg (by rw [hβc, hn]; linarith) bHH
    have hFW : 0 ≤ W * F6val M2 M3 M4 := mul_nonneg hW0 hF
    have eF : W * F6val M2 M3 M4 = W * F6core M2 M3 M4
        - eta 6 * (1 + 4 * qm6) * (M2 + 2 * M3 + M4) * W := by unfold F6val; ring
    have e6 : 4 * eta 6 * (qm6 * (M2 + 2 * M3 + M4) * W)
        = eta 6 * (1 + 4 * qm6) * (M2 + 2 * M3 + M4) * W
          - eta 6 * ((M2 + 2 * M3 + M4) * W) := by ring
    have e7 : βc * HH - eta 6 * ((M2 + 2 * M3 + M4) * W + 4 * HH + 4 * XX)
        = (βc - 4 * eta 6) * HH - eta 6 * ((M2 + 2 * M3 + M4) * W) - 4 * eta 6 * XX := by ring
    linarith only [i1, i2, i3, i4, i5, i6, i7, hFW, eF, hcore, hMMη, e6, e7]
  · -- the capped certificate
    have i7 : 0 ≤ βc * HH := mul_nonneg (by rw [hβc, hn]; linarith) bHH
    have hFW : 0 ≤ W * F6cap M2 M3 M4 := mul_nonneg hW0 hF
    have eF : W * F6cap M2 M3 M4 = W * F6core M2 M3 M4 - cap * W := by
      unfold F6cap; rw [hcap]; ring
    linarith only [i1, i2, i3, i4, i5, i7, hFW, eF, hcore, hMMc]

end GridGen.Four
