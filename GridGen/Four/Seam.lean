/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.Cert

/-!
# Height four: the seam inequality at `k = 8`

Summing `state_bound` over the previous column `s ∈ sts X` with the uniform weights `GU`,
`Σ GB ≥ Σ GU + Σ GU·Λ`. The gain `Λ` is a constant (in `s`) plus multiples of the state bits
`zᵢ`, `[s₁ = s₃]`, `[s₂ = s₄]`, `hᵢ` and `[sᵢ ∈ Bᵢ ∖ B₂]`. The bonus bits `hᵢ` have a nonnegative
coefficient; every other bit pins one row of `s` to a colour set `D` fixed by the others, which the
fibre bound weighs at most `q |D|`, `q = 1/(ρ(k-3))`, because the weights `GU` of any two states
are within the factor `1/ρ` (`GU_eq`). So `Σ GU·Λ ≥ (Σ GU) · Fval k μ₂ μ₃ μ₄ ≥ 0`.
-/

namespace GridGen.Four

open Finset Real

/-- A sum against an indicator is a filtered sum. -/
theorem sum_mul_ite {Ω : Finset T4} (w : T4 → ℝ) (p : T4 → Prop) [DecidablePred p] :
    ∑ t ∈ Ω, w t * (if p t then 1 else 0) = ∑ t ∈ Ω.filter p, w t := by
  rw [Finset.sum_filter]; refine Finset.sum_congr rfl (fun t _ => ?_); split_ifs <;> simp

/-- **Fibre bound for a set of colours.** -/
theorem fibre_mem {Ω : Finset T4} (w : T4 → ℝ) (g : T4 → ℕ) {m R : ℝ}
    (hc : ∀ c, m * ∑ t ∈ Ω.filter (fun t => g t = c), w t ≤ R * ∑ t ∈ Ω, w t)
    (D : Finset ℕ) :
    m * ∑ t ∈ Ω, w t * (if g t ∈ D then 1 else 0) ≤ R * D.card * ∑ t ∈ Ω, w t := by
  rw [sum_mul_ite]
  have e : ∑ t ∈ Ω.filter (fun t => g t ∈ D), w t
      = ∑ c ∈ D, ∑ t ∈ Ω.filter (fun t => g t = c), w t := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := g) (t := D) (fun x hx => (Finset.mem_filter.mp hx).2)]
    refine Finset.sum_congr rfl (fun c hc => ?_)
    rw [Finset.filter_filter]
    congr 1
    ext t; simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨h1, h3 ▸ hc, h3⟩
  rw [e, Finset.mul_sum]
  calc ∑ c ∈ D, m * ∑ t ∈ Ω.filter (fun t => g t = c), w t
      ≤ ∑ c ∈ D, R * ∑ t ∈ Ω, w t := Finset.sum_le_sum (fun c _ => hc c)
    _ = R * D.card * ∑ t ∈ Ω, w t := by rw [Finset.sum_const, nsmul_eq_mul]; ring

theorem zz_eq (B C : Finset ℕ) (a b : ℕ) :
    zz B C a b = (if a ∈ B \ C then 1 else 0) + (if b ∈ C \ B then 1 else 0) := by
  unfold zz; simp only [Finset.mem_sdiff]

theorem xin_eq (B C : Finset ℕ) (c : ℕ) : xin B C c = if c ∈ B \ C then 1 else 0 := by
  unfold xin; simp only [Finset.mem_sdiff]

/-- The uniform weights of two proper states are within the factor `1/ρ`. -/
theorem GU_ratio {k : ℕ} (hk : 5 ≤ k) {w : Wt} (hw : InBox k w) {t t' : T4} (ht : Proper t)
    (ht' : Proper t') : GU k w t ≤ (1 / rho k) * GU k w t' := by
  have hA := vA_pos_of_inBox hk hw
  have hρ := rho_pos' hk
  rw [GU_eq (by omega) w hA.ne' ht, GU_eq (by omega) w hA.ne' ht']
  have g1 := (gw_mem (nextW_inBox hk hw) t).2
  have g2 := (gw_mem (nextW_inBox hk hw) t').1
  rw [one_div_mul_eq_div, le_div_iff₀ hρ]
  calc vA ((k : ℝ) - 2) w * gw (nextW k w) t * rho k ≤ vA ((k : ℝ) - 2) w * 1 * rho k := by
        gcongr
    _ ≤ vA ((k : ℝ) - 2) w * gw (nextW k w) t' := by rw [mul_one]; gcongr

theorem GU_nonneg {k : ℕ} (hk : 5 ≤ k) {w : Wt} (hw : InBox k w) (t : T4) : 0 ≤ GU k w t := by
  have u : ∀ i, 3 ≤ ((range k).erase i).card := fun i => by
    have := card_ge_of_erase (card_range k) i; omega
  exact (G_pos hk hw (u _) (u _) (u _) (u _)).le

/-- The decomposition of the capped gain into a constant and the state bits. -/
theorem Lamc_eq (k : ℕ) (B₁ B₂ B₃ B₄ : Finset ℕ) (s : T4) :
    Lamc k B₁ B₂ B₃ B₄ s =
      (log (1 + mu k B₁ B₂ / kA ((k : ℝ) - 1)) + log (1 + mu k B₂ B₃ / kA ((k : ℝ) - 1))
        + log (1 + mu k B₃ B₄ / kA ((k : ℝ) - 1))
        - J3 (mu k B₁ B₂) (mu k B₂ B₃) * ((mu k B₁ B₂ + 1) * (mu k B₂ B₃ + 1)
            / (((k : ℝ) - 1) ^ 2 * ((k : ℝ) - 1 - 1) ^ 2))
        - J4 (mu k B₁ B₂) (mu k B₂ B₃) (mu k B₃ B₄) * ((mu k B₂ B₃ + 2) * (mu k B₃ B₄ + 1)
            / (((k : ℝ) - 1) * ((k : ℝ) - 1 - 1) ^ 3) + ku4b ((k : ℝ) - 1)))
      - 1 / (((k : ℝ) - 1) * ((k : ℝ) - 1 - 1)) * (zz B₁ B₂ (r1 s) (r2 s) + zz B₂ B₃ (r2 s) (r3 s)
          + zz B₃ B₄ (r3 s) (r4 s))
      - J3 (mu k B₁ B₂) (mu k B₂ B₃) * ku3 ((k : ℝ) - 1) * c13 s
      - J4 (mu k B₁ B₂) (mu k B₂ B₃) (mu k B₃ B₄) * ku4e ((k : ℝ) - 1) * c24 s
      + (kβ0 ((k : ℝ) - 1) - kb3 ((k : ℝ) - 1) - kb4 ((k : ℝ) - 1))
          * (hb B₁ (r1 s) + hb B₂ (r2 s) + hb B₃ (r3 s) + hb B₄ (r4 s))
      - min (eta k * PS k B₁ B₂ B₃ B₄ s) ((1 - rho k) / rho k) := by
  unfold Lamc CB countBound
  ring

/-- The bonus coefficient is nonnegative. -/
theorem bonus_coef {k : ℕ} (hk7 : 7 ≤ k) (hk8 : k ≤ 8) :
    0 ≤ kβ0 ((k : ℝ) - 1) - kb3 ((k : ℝ) - 1) - kb4 ((k : ℝ) - 1) - 4 * eta k := by
  interval_cases k <;> norm_num [kβ0, kb3, kb4, ku3, ku4e, ku4b, kt, kA, eta, rho]

/-- Signs of the constants. -/
theorem consts_sign {k : ℕ} (hk7 : 7 ≤ k) :
    0 ≤ 1 / (((k : ℝ) - 1) * ((k : ℝ) - 1 - 1)) ∧ 0 ≤ ku3 ((k : ℝ) - 1) ∧
      0 ≤ ku4e ((k : ℝ) - 1) ∧ 0 ≤ eta k ∧ 0 < qk k ∧
      1 / rho k = ((k - 3 : ℕ) : ℝ) * qk k ∧ 0 ≤ (1 - rho k) / rho k := by
  have hk7' : (7 : ℝ) ≤ k := by exact_mod_cast hk7
  have hk5 : 5 ≤ k := by omega
  have hρ := rho_pos' hk5
  have hm : (0 : ℝ) < ((k - 3 : ℕ) : ℝ) := by
    have : 0 < k - 3 := by omega
    exact_mod_cast this
  have ht0 : 0 < kt ((k : ℝ) - 1) := by unfold kt kA; apply div_pos <;> nlinarith
  have hc : 0 ≤ (1 - rho k) / rho k := div_nonneg (by linarith [rho_le_one k hk5]) hρ.le
  refine ⟨div_nonneg zero_le_one (mul_nonneg (by linarith) (by linarith)), ?_, ?_, ?_, ?_, ?_, hc⟩
  · unfold ku3; apply div_nonneg (by linarith); positivity
  · unfold ku4e; apply div_nonneg zero_le_one; positivity
  · unfold eta; exact div_nonneg hc hm.le
  · unfold qk; positivity
  · unfold qk; field_simp

/-- **The seam inequality from either certificate**, for one system of lists. -/
theorem seam_of_cert {k : ℕ} (hk7 : 7 ≤ k) (hk8 : k ≤ 8) {w : Wt} (hw : InBox k w)
    {X₁ X₂ X₃ X₄ B₁ B₂ B₃ B₄ : Finset ℕ}
    (hX₁ : k - 1 ≤ X₁.card) (hX₂ : k - 1 ≤ X₂.card) (hX₃ : k - 1 ≤ X₃.card)
    (hX₄ : k - 1 ≤ X₄.card)
    (hB₁ : B₁.card = k) (hB₂ : B₂.card = k) (hB₃ : B₃.card = k) (hB₄ : B₄.card = k)
    (hcert : 0 ≤ Fval k (mu k B₁ B₂) (mu k B₂ B₃) (mu k B₃ B₄)
      ∨ 0 ≤ Fcap k (mu k B₁ B₂) (mu k B₂ B₃) (mu k B₃ B₄)) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄, GU k w s ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄, GB w B₁ B₂ B₃ B₄ s := by
  have hk5 : 5 ≤ k := by omega
  have hρ := rho_pos' hk5
  have hm : (0 : ℝ) < ((k - 3 : ℕ) : ℝ) := by
    have : 0 < k - 3 := by omega
    exact_mod_cast this
  obtain ⟨ha0, hku3, hku4e, hη0, hq0, hRq, hc0⟩ := consts_sign hk7
  have hβ := bonus_coef hk7 hk8
  set m : ℝ := ((k - 3 : ℕ) : ℝ) with hm_def
  set Ω := sts X₁ X₂ X₃ X₄ with hΩ
  set u : T4 → ℝ := GU k w with hu
  have hu0 : ∀ t, 0 ≤ u t := GU_nonneg hk5 hw
  set q := qk k with hq
  have hR0 : 0 ≤ m * q := (mul_pos hm hq0).le
  have hR : ∀ t ∈ Ω, ∀ t' ∈ Ω, u t ≤ (m * q) * u t' := fun t ht t' ht' => by
    rw [← hRq]; exact GU_ratio hk5 hw (proper_of_mem_sts ht) (proper_of_mem_sts ht')
  -- the per-colour fibres
  have f1 : ∀ c, m * ∑ t ∈ Ω.filter (fun t => r1 t = c), u t ≤ (m * q) * ∑ t ∈ Ω, u t :=
    fun c => fibre_sts1 u hu0 (fun t => r1 t = c) hX₁ hX₂ hX₃ hX₄ hR0 hR (fun _ => c)
      (fun _ _ => rfl) (fun _ h => h)
  have f2 : ∀ c, m * ∑ t ∈ Ω.filter (fun t => r2 t = c), u t ≤ (m * q) * ∑ t ∈ Ω, u t :=
    fun c => fibre_sts2 u hu0 (fun t => r2 t = c) hX₁ hX₂ hX₃ hX₄ hR0 hR (fun _ => c)
      (fun _ _ => rfl) (fun _ h => h)
  have f3 : ∀ c, m * ∑ t ∈ Ω.filter (fun t => r3 t = c), u t ≤ (m * q) * ∑ t ∈ Ω, u t :=
    fun c => fibre_sts3 u hu0 (fun t => r3 t = c) hX₁ hX₂ hX₃ hX₄ hR0 hR (fun _ => c)
      (fun _ _ => rfl) (fun _ h => h)
  have f4 : ∀ c, m * ∑ t ∈ Ω.filter (fun t => r4 t = c), u t ≤ (m * q) * ∑ t ∈ Ω, u t :=
    fun c => fibre_sts4 u hu0 (fun t => r4 t = c) hX₁ hX₂ hX₃ hX₄ hR0 hR (fun _ => c)
      (fun _ _ => rfl) (fun _ h => h)
  -- summing the bound for one state
  have hsum : ∑ s ∈ Ω, u s * (1 + Lamc k B₁ B₂ B₃ B₄ s) ≤ ∑ s ∈ Ω, GB w B₁ B₂ B₃ B₄ s :=
    Finset.sum_le_sum (fun s hs => state_bound_cap hk7 hk8 hw hB₁ hB₂ hB₃ hB₄
      (proper_of_mem_sts hs))
  suffices h : 0 ≤ ∑ s ∈ Ω, u s * Lamc k B₁ B₂ B₃ B₄ s by
    have e : ∑ s ∈ Ω, u s * (1 + Lamc k B₁ B₂ B₃ B₄ s)
        = ∑ s ∈ Ω, u s + ∑ s ∈ Ω, u s * Lamc k B₁ B₂ B₃ B₄ s := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun s _ => by ring)
    linarith
  -- names for the constants
  set M2 := mu k B₁ B₂ with hM2
  set M3 := mu k B₂ B₃ with hM3
  set M4 := mu k B₃ B₄ with hM4
  set K0 := log (1 + M2 / kA ((k : ℝ) - 1)) + log (1 + M3 / kA ((k : ℝ) - 1))
        + log (1 + M4 / kA ((k : ℝ) - 1))
        - J3 M2 M3 * ((M2 + 1) * (M3 + 1) / (((k : ℝ) - 1) ^ 2 * ((k : ℝ) - 1 - 1) ^ 2))
        - J4 M2 M3 M4 * ((M3 + 2) * (M4 + 1) / (((k : ℝ) - 1) * ((k : ℝ) - 1 - 1) ^ 3)
            + ku4b ((k : ℝ) - 1)) with hK0
  set a := 1 / (((k : ℝ) - 1) * ((k : ℝ) - 1 - 1)) with ha
  set g3 := J3 M2 M3 * ku3 ((k : ℝ) - 1) with hg3
  set g4 := J4 M2 M3 M4 * ku4e ((k : ℝ) - 1) with hg4
  set βc := kβ0 ((k : ℝ) - 1) - kb3 ((k : ℝ) - 1) - kb4 ((k : ℝ) - 1) with hβc
  set cap := (1 - rho k) / rho k with hcap
  set W := ∑ s ∈ Ω, u s with hW
  -- the bit sums
  set Z2 := ∑ s ∈ Ω, u s * zz B₁ B₂ (r1 s) (r2 s) with hZ2
  set Z3 := ∑ s ∈ Ω, u s * zz B₂ B₃ (r2 s) (r3 s) with hZ3
  set Z4 := ∑ s ∈ Ω, u s * zz B₃ B₄ (r3 s) (r4 s) with hZ4
  set C13 := ∑ s ∈ Ω, u s * c13 s with hC13
  set C24 := ∑ s ∈ Ω, u s * c24 s with hC24
  set HH := ∑ s ∈ Ω, u s * (hb B₁ (r1 s) + hb B₂ (r2 s) + hb B₃ (r3 s) + hb B₄ (r4 s)) with hHH
  set XX := ∑ s ∈ Ω, u s * (xin B₁ B₂ (r1 s) + xin B₃ B₂ (r3 s) + xin B₄ B₂ (r4 s)) with hXX
  set MM := ∑ s ∈ Ω, u s * min (eta k * PS k B₁ B₂ B₃ B₄ s) cap with hMM
  have e : ∑ s ∈ Ω, u s * Lamc k B₁ B₂ B₃ B₄ s
      = K0 * W - a * Z2 - a * Z3 - a * Z4 - g3 * C13 - g4 * C24 + βc * HH - MM := by
    rw [hW, hZ2, hZ3, hZ4, hC13, hC24, hHH, hMM]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [Lamc_eq]; ring
  rw [e]
  have hW0 : 0 ≤ W := Finset.sum_nonneg (fun s _ => hu0 s)
  -- the cap, both ways
  have hMMc : MM ≤ cap * W := by
    rw [hMM, hW, Finset.mul_sum]
    exact Finset.sum_le_sum (fun s _ => by
      rw [mul_comm cap]; exact mul_le_mul_of_nonneg_left (min_le_right _ _) (hu0 s))
  have hMMη : MM ≤ eta k * ((M2 + 2 * M3 + M4) * W + 4 * HH + 4 * XX) := by
    have : eta k * ((M2 + 2 * M3 + M4) * W + 4 * HH + 4 * XX)
        = ∑ s ∈ Ω, u s * (eta k * PS k B₁ B₂ B₃ B₄ s) := by
      rw [hW, hHH, hXX]
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      unfold PS; ring
    rw [this, hMM]
    exact Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (min_le_left _ _) (hu0 s))
  -- bounds on the bit sums
  have card_d : ∀ {B C : Finset ℕ}, B.card = k → ((B \ C).card : ℝ) = mu k B C :=
    fun hB => card_sdiff_mu hB _
  have pair : ∀ (B C : Finset ℕ) (g g' : T4 → ℕ),
      (∀ c, m * ∑ t ∈ Ω.filter (fun t => g t = c), u t ≤ (m * q) * W) →
      (∀ c, m * ∑ t ∈ Ω.filter (fun t => g' t = c), u t ≤ (m * q) * W) →
      B.card = k → C.card = k →
      m * ∑ s ∈ Ω, u s * zz B C (g s) (g' s) ≤ (m * q) * (2 * mu k B C) * W := by
    intro B C g g' hg hg' hB hC
    have e1 : ∑ s ∈ Ω, u s * zz B C (g s) (g' s)
        = ∑ s ∈ Ω, u s * (if g s ∈ B \ C then 1 else 0)
          + ∑ s ∈ Ω, u s * (if g' s ∈ C \ B then 1 else 0) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun s _ => by rw [zz_eq]; ring)
    have b1 := fibre_mem u g hg (B \ C)
    have b2 := fibre_mem u g' hg' (C \ B)
    rw [card_d hB] at b1
    rw [card_d hC, mu_comm k C B] at b2
    rw [e1, mul_add]
    linarith
  have bZ2 := pair B₁ B₂ r1 r2 f1 f2 hB₁ hB₂
  have bZ3 := pair B₂ B₃ r2 r3 f2 f3 hB₂ hB₃
  have bZ4 := pair B₃ B₄ r3 r4 f3 f4 hB₃ hB₄
  have bC13 : m * C13 ≤ (m * q) * W := by
    rw [hC13]
    have : ∑ s ∈ Ω, u s * c13 s = ∑ s ∈ Ω.filter (fun t => r1 t = r3 t), u s := by
      rw [← sum_mul_ite]; rfl
    rw [this]
    exact fibre_sts1 u hu0 (fun t => r1 t = r3 t) hX₁ hX₂ hX₃ hX₄ hR0 hR r3
      (fun _ _ => rfl) (fun _ h => h)
  have bC24 : m * C24 ≤ (m * q) * W := by
    rw [hC24]
    have : ∑ s ∈ Ω, u s * c24 s = ∑ s ∈ Ω.filter (fun t => r2 t = r4 t), u s := by
      rw [← sum_mul_ite]; rfl
    rw [this]
    exact fibre_sts2 u hu0 (fun t => r2 t = r4 t) hX₁ hX₂ hX₃ hX₄ hR0 hR r4
      (fun _ _ => rfl) (fun _ h => h)
  have bXX : m * XX ≤ (m * q) * (M2 + 2 * M3 + M4) * W := by
    have e1 : XX = ∑ s ∈ Ω, u s * (if r1 s ∈ B₁ \ B₂ then 1 else 0)
        + ∑ s ∈ Ω, u s * (if r3 s ∈ B₃ \ B₂ then 1 else 0)
        + ∑ s ∈ Ω, u s * (if r4 s ∈ B₄ \ B₂ then 1 else 0) := by
      rw [hXX, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun s _ => by rw [xin_eq, xin_eq, xin_eq]; ring)
    have b1 := fibre_mem u r1 f1 (B₁ \ B₂)
    have b3 := fibre_mem u r3 f3 (B₃ \ B₂)
    have b4 := fibre_mem u r4 f4 (B₄ \ B₂)
    have t4 := card_sdiff_tri B₄ B₃ B₂
    rw [card_d hB₁] at b1
    rw [card_d hB₃, mu_comm k B₃ B₂] at b3
    rw [card_sdiff_mu hB₄ B₃, card_sdiff_mu hB₃ B₂, mu_comm k B₄ B₃, mu_comm k B₃ B₂] at t4
    have b4' : (m * q) * ((B₄ \ B₂).card : ℝ) * W ≤ (m * q) * (M4 + M3) * W :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left t4 hR0) hW0
    have ex : (m * q) * (M2 + 2 * M3 + M4) * W
        = (m * q) * M2 * W + (m * q) * M3 * W + (m * q) * (M4 + M3) * W := by ring
    rw [e1, ex, mul_add, mul_add]
    linarith
  have hbn : ∀ (B : Finset ℕ) (c : ℕ), 0 ≤ hb B c := fun B c => by
    unfold hb; split_ifs <;> norm_num
  have bHH : 0 ≤ HH := Finset.sum_nonneg (fun s _ => mul_nonneg (hu0 s)
    (add_nonneg (add_nonneg (add_nonneg (hbn _ _) (hbn _ _)) (hbn _ _)) (hbn _ _)))
  have hJ3 : 0 ≤ J3 M2 M3 := by unfold J3; split_ifs <;> norm_num
  have hJ4 : 0 ≤ J4 M2 M3 M4 := by unfold J4; split_ifs <;> norm_num
  have hg30 : 0 ≤ g3 := mul_nonneg hJ3 hku3
  have hg40 : 0 ≤ g4 := mul_nonneg hJ4 hku4e
  have i1 := mul_le_mul_of_nonneg_left bZ2 ha0
  have i2 := mul_le_mul_of_nonneg_left bZ3 ha0
  have i3 := mul_le_mul_of_nonneg_left bZ4 ha0
  have i4 := mul_le_mul_of_nonneg_left bC13 hg30
  have i5 := mul_le_mul_of_nonneg_left bC24 hg40
  have eS : m * (K0 * W - a * Z2 - a * Z3 - a * Z4 - g3 * C13 - g4 * C24 + βc * HH - MM)
      = m * K0 * W - a * (m * Z2) - a * (m * Z3) - a * (m * Z4)
        - g3 * (m * C13) - g4 * (m * C24) + m * (βc * HH) - m * MM := by ring
  suffices key : 0 ≤ m * (K0 * W - a * Z2 - a * Z3 - a * Z4 - g3 * C13 - g4 * C24 + βc * HH - MM)
    from (mul_nonneg_iff_of_pos_left hm).mp key
  rw [eS]
  rcases hcert with hF | hF
  · -- the uncapped certificate
    have i6 := mul_le_mul_of_nonneg_left bXX (by linarith : (0 : ℝ) ≤ 4 * eta k)
    have i7 : 0 ≤ m * ((βc - 4 * eta k) * HH) := mul_nonneg hm.le (mul_nonneg hβ bHH)
    have i8 := mul_le_mul_of_nonneg_left hMMη hm.le
    have hFW : 0 ≤ m * (W * Fval k M2 M3 M4) := mul_nonneg hm.le (mul_nonneg hW0 hF)
    have eF : m * (W * Fval k M2 M3 M4) = m * K0 * W - a * ((m * q) * (2 * M2) * W)
        - a * ((m * q) * (2 * M3) * W) - a * ((m * q) * (2 * M4) * W) - g3 * ((m * q) * W)
        - g4 * ((m * q) * W) - m * (eta k * ((M2 + 2 * M3 + M4) * W))
        - 4 * eta k * ((m * q) * (M2 + 2 * M3 + M4) * W) := by
      rw [hK0, ha, hg3, hg4, hq]; unfold Fval; ring
    have e7 : m * (βc * HH) - m * (eta k * ((M2 + 2 * M3 + M4) * W + 4 * HH + 4 * XX))
        = m * ((βc - 4 * eta k) * HH) - m * (eta k * ((M2 + 2 * M3 + M4) * W))
          - 4 * eta k * (m * XX) := by ring
    linarith only [i1, i2, i3, i4, i5, i6, i7, i8, hFW, eF, e7]
  · -- the capped certificate
    have i7 : 0 ≤ m * (βc * HH) := mul_nonneg hm.le (mul_nonneg (by linarith) bHH)
    have i8 := mul_le_mul_of_nonneg_left hMMc hm.le
    have hFW : 0 ≤ m * (W * Fcap k M2 M3 M4) := mul_nonneg hm.le (mul_nonneg hW0 hF)
    have eF : m * (W * Fcap k M2 M3 M4) = m * K0 * W - a * ((m * q) * (2 * M2) * W)
        - a * ((m * q) * (2 * M3) * W) - a * ((m * q) * (2 * M4) * W) - g3 * ((m * q) * W)
        - g4 * ((m * q) * W) - m * (cap * W) := by
      rw [hK0, ha, hg3, hg4, hq, hcap]; unfold Fcap; ring
    linarith only [i1, i2, i3, i4, i5, i7, i8, hFW, eF]

/-- **The height-four seam inequality at `k = 8`.** -/
theorem seam4Holds_eight : Seam4Holds 8 := by
  intro w hw X₁ X₂ X₃ X₄ B₁ B₂ B₃ B₄ hX₁ hX₂ hX₃ hX₄ hB₁ hB₂ hB₃ hB₄
  exact seam_of_cert (by norm_num) le_rfl hw hX₁.1 hX₂.1 hX₃.1 hX₄.1 hB₁ hB₂ hB₃ hB₄
    (Or.inl (Fval_nonneg rfl (mu_cases hB₁) (mu_cases hB₂) (mu_cases hB₃)
      (mu_le B₁ B₂) (mu_le B₂ B₃) (mu_le B₃ B₄)))

end GridGen.Four
