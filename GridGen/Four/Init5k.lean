/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.State5
import GridGen.Four.Init

/-!
# Height four, `k = 5`: the initial inequality

`ai_research_notes/H4_K5_ANALYTIC_2026-10-24.md` §5. For `5`-lists `X₁, …, X₄` with
`S = |X₁ ∖ X₂| + |X₂ ∖ X₃| + |X₃ ∖ X₄|`:

* if `S = 0` the lists are equal and the column weighs as much as the uniform one
  (`G_range_eq`);
* otherwise `|sts X| ≥ 320 + 15 = 335` (`card_sts_gain`), and with lists of five colours a free
  end row has four values, so the shares of `s₁ = s₃`, `s₂ = s₄`, `s₁ = s₄` are at most `1/4`
  (`fibre_sts1_sharp`, `fibre_sts4_sharp`). Against the uniform column
  `20 + 120 a + 60 b + 120 c` (its class counts) this is checked at the eight corners of the
  box (`init_corner5`): the average weight is at least `0.9642` of the uniform one, and
  `0.9642 · 335/320 > 1`.
-/

namespace GridGen.Four

open Finset GridGen.Lookback

/-- The class counts of the uniform column `sts (range 5)⁴`. -/
theorem range5_counts :
    (sts (range 5) (range 5) (range 5) (range 5)).card = 320 ∧
    ((sts (range 5) (range 5) (range 5) (range 5)).filter (fun t => r1 t = r3 t)).card = 80 ∧
    ((sts (range 5) (range 5) (range 5) (range 5)).filter (fun t => r2 t = r4 t)).card = 80 ∧
    ((sts (range 5) (range 5) (range 5) (range 5)).filter
      (fun t => r1 t = r3 t ∧ r2 t = r4 t)).card = 20 ∧
    ((sts (range 5) (range 5) (range 5) (range 5)).filter (fun t => r1 t = r4 t)).card = 60 := by
  decide +kernel

/-- The uniform column weighs `20 + 120 a + 60 b + 120 c`. -/
theorem G_range5 (w : Wt) :
    G w (range 5) (range 5) (range 5) (range 5) = 20 + 120 * w.a + 60 * w.b + 120 * w.c := by
  rw [G_split]
  obtain ⟨h0, h1, h2, h3, h4⟩ := range5_counts
  simp only [h0, h1, h2, h3, h4]
  push_cast; ring

/-- The counts of a column system with lists of five colours. -/
theorem init_counts5 {X₁ X₂ X₃ X₄ : Finset ℕ} (h₁ : X₁.card = 5) (h₂ : X₂.card = 5)
    (h₃ : X₃.card = 5) (h₄ : X₄.card = 5) :
    let Ω := sts X₁ X₂ X₃ X₄
    4 * ((Ω.filter (fun t => r1 t = r3 t)).card : ℝ) ≤ Ω.card ∧
    4 * ((Ω.filter (fun t => r2 t = r4 t)).card : ℝ) ≤ Ω.card ∧
    4 * ((Ω.filter (fun t => r1 t = r4 t)).card : ℝ) ≤ Ω.card := by
  intro Ω
  have hR : ∀ t ∈ Ω, ∀ t' ∈ Ω, (fun _ : T4 => (1 : ℝ)) t ≤ 1 * (fun _ : T4 => (1 : ℝ)) t' :=
    fun _ _ _ _ => by norm_num
  have one : ∀ (P : T4 → Prop) [DecidablePred P], ∑ t ∈ Ω.filter P, (fun _ : T4 => (1 : ℝ)) t
      = ((Ω.filter P).card : ℝ) := fun P _ => by simp
  have oneΩ : ∑ t ∈ Ω, (fun _ : T4 => (1 : ℝ)) t = (Ω.card : ℝ) := by simp
  have f13 := fibre_sts1_sharp (k := 6) (A₂ := X₂) (A₃ := X₃) (A₄ := X₄) (fun _ => (1 : ℝ))
    (fun _ => zero_le_one) (fun t => r1 t = r3 t) (by norm_num) (by omega) one_pos hR r3
    (fun _ _ => rfl) (fun _ h => h)
  have f24 := fibre_sts4_sharp (k := 6) (A₁ := X₁) (A₂ := X₂) (A₃ := X₃) (fun _ => (1 : ℝ))
    (fun _ => zero_le_one) (fun t => r4 t = r2 t) (by norm_num) (by omega) one_pos hR r2
    (fun _ _ => rfl) (fun _ h => h)
  have f14 := fibre_sts1_sharp (k := 6) (A₂ := X₂) (A₃ := X₃) (A₄ := X₄) (fun _ => (1 : ℝ))
    (fun _ => zero_le_one) (fun t => r1 t = r4 t) (by norm_num) (by omega) one_pos hR r4
    (fun _ _ => rfl) (fun _ h => h)
  rw [one, oneΩ] at f13 f24 f14
  have e24 : Ω.filter (fun t => r4 t = r2 t) = Ω.filter (fun t => r2 t = r4 t) :=
    Finset.filter_congr (fun t _ => eq_comm)
  rw [e24] at f24
  norm_num at f13 f24 f14
  exact ⟨by linarith, by linarith, by linarith⟩

/-- **The corner inequalities** of the initial inequality. -/
theorem init_corner5 : ∀ x y z : ℝ, (x = 118 / 125 ∨ x = 1) → (y = 118 / 125 ∨ y = 1) →
    (z = 118 / 125 ∨ z = 1) → ∀ N n13 n24 m n14 : ℝ, 335 ≤ N → 4 * n13 ≤ N → 4 * n24 ≤ N →
      4 * n14 ≤ N → 0 ≤ m → m ≤ n13 → m ≤ n24 → 0 ≤ n14 → n13 + n24 - m + n14 ≤ N →
      20 + 120 * x + 60 * y + 120 * z
        ≤ z * N + (x - z) * (n13 + n24) + (1 - 2 * x + z) * m + (y - z) * n14 := by
  rintro x y z (rfl | rfl) (rfl | rfl) (rfl | rfl) N n13 n24 m n14 hN h13 h24 h14 hm0 hm13 hm24
    h140 hcov <;> linarith

/-- **The height-four initial inequality at `k = 5`.** -/
theorem init4Holds_five : Init4Holds 5 := by
  intro w hw X₁ X₂ X₃ X₄ h₁ h₂ h₃ h₄
  have hb : BoxR (118 / 125) w := by rw [← rho_five]; exact hw
  change G w (range 5) (range 5) (range 5) (range 5) ≤ G w X₁ X₂ X₃ X₄
  by_cases hS : (X₁ \ X₂).card + (X₂ \ X₃).card + (X₃ \ X₄).card = 0
  · -- equal lists
    have s12 : X₁ \ X₂ = ∅ := Finset.card_eq_zero.mp (by omega)
    have s23 : X₂ \ X₃ = ∅ := Finset.card_eq_zero.mp (by omega)
    have s34 : X₃ \ X₄ = ∅ := Finset.card_eq_zero.mp (by omega)
    have e12 : X₁ = X₂ := Finset.eq_of_subset_of_card_le (Finset.sdiff_eq_empty_iff_subset.mp s12)
      (by omega)
    have e23 : X₂ = X₃ := Finset.eq_of_subset_of_card_le (Finset.sdiff_eq_empty_iff_subset.mp s23)
      (by omega)
    have e34 : X₃ = X₄ := Finset.eq_of_subset_of_card_le (Finset.sdiff_eq_empty_iff_subset.mp s34)
      (by omega)
    subst e12 e23 e34
    exact (G_range_eq w h₁).le
  · have hgain := card_sts_gain h₁ h₂ h₃ h₄ (by norm_num)
    have hN : (335 : ℝ) ≤ (sts X₁ X₂ X₃ X₄).card := by
      have : (335 : ℤ) ≤ (sts X₁ X₂ X₃ X₄).card := by push_cast at hgain; omega
      exact_mod_cast this
    obtain ⟨c13, c24, c14⟩ := init_counts5 h₁ h₂ h₃ h₄
    obtain ⟨-, -, -, -, m13, m24, cov⟩ := pat_counts5 (A₁ := X₁) (A₂ := X₂) (A₃ := X₃)
      (A₄ := X₄) (by omega) (by omega) (by omega) (by omega)
    rw [G_range5, G_split]
    simp only [Int.cast_natCast]
    obtain ⟨ha, ha', hb', hb'', hc, hc'⟩ := hb
    rw [← sub_nonneg]
    set N : ℝ := ((sts X₁ X₂ X₃ X₄).card : ℝ)
    set n13 : ℝ := (((sts X₁ X₂ X₃ X₄).filter (fun t => r1 t = r3 t)).card : ℝ)
    set n24 : ℝ := (((sts X₁ X₂ X₃ X₄).filter (fun t => r2 t = r4 t)).card : ℝ)
    set m : ℝ := (((sts X₁ X₂ X₃ X₄).filter (fun t => r1 t = r3 t ∧ r2 t = r4 t)).card : ℝ)
    set n14 : ℝ := (((sts X₁ X₂ X₃ X₄).filter (fun t => r1 t = r4 t)).card : ℝ)
    have e : w.c * N + (w.a - w.c) * (n13 + n24) + (1 - 2 * w.a + w.c) * m + (w.b - w.c) * n14
        - (20 + 120 * w.a + 60 * w.b + 120 * w.c)
        = aff (m - 20) (n13 + n24 - 2 * m - 120) (n14 - 60) (N - n13 - n24 + m - n14 - 120) w := by
      unfold aff; ring
    rw [e]
    refine aff_nonneg ha ha' hb' hb'' hc hc' (fun x y z hx hy hz => ?_)
    have := init_corner5 x y z hx hy hz N n13 n24 m n14 hN c13 c24 c14 (Nat.cast_nonneg _) m13
      m24 (Nat.cast_nonneg _) cov
    unfold aff
    linarith

end GridGen.Four
