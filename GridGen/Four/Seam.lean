/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.Cert

/-!
# Height four: averaging lemmas for the seam inequality

Summing a one-state bound `GB ≥ GU · (1 + Λ)` over the previous column `s ∈ sts X` with the
uniform weights `GU` gives `Σ GB ≥ Σ GU + Σ GU·Λ`. Every bit of `Λ` that pins one row of `s` to a
colour set `D` fixed by the others is weighed by the fibre bound (`fibre_mem`), because the weights
`GU` of any two states are within the factor `1/ρ` (`GU_ratio`). The seam inequality itself is
`seam_of_cert6` (`Seam6.lean`) at `k = 6`.
-/

namespace GridGen.Four

open Finset Real GridGen.Lookback

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

end GridGen.Four
