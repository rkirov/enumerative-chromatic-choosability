/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.State5
import GridGen.Four.K4.Classify

/-!
# Height four at `k = 4`: the initial inequality

A column of four-lists has class counts `cnt X` that dominate the uniform column's
`(12, 48, 24, 24)` on the cone `K` (`init_cnt`). Codex checked this by enumerating the `4,079`
Venn shapes (`ai_research_notes/cx/h4k4b/NOTE.md`, "Init, horizons, and short chains"; review
Part 1(e)); here it is analytic, as for `k = 5` (`GridGen/Four/Init5k.lean`):

* if the four lists are equal the column is a renamed uniform column (`cnt_const`);
* otherwise `|sts X| ≥ 4·3³ + 4·2 = 116` (`card_sts_gain`), and with lists of four colours a free
  end row has three values, so at most a third of the states have `s₁ = s₄`, and
  `#(s₁ = s₃ ∧ s₂ = s₄) ≤ #(s₁ = s₃), #(s₂ = s₄)` (`pat_counts5`). At each ray `r` of `K` the class
  weights satisfy `r_B ≥ r_D`, `r_A ≥ r_D`, `r_C ≤ r_D`, and the worst case is
  `|sts X| (2 r_D + r_C)/3`, which beats the uniform value by about `2.7%` at every ray.
-/

namespace GridGen.Four.K4

open Finset GridGen.Lookback

/-- The weight of a proper column through the indicators of `r1 = r3`, `r2 = r4`, both, and
`r1 = r4`. -/
theorem cw_split (w : Q) {t : T4} (ht : Proper t) :
    cw w t = w.2.2.2 + (w.2.1 - w.2.2.2) * ((if r1 t = r3 t then 1 else 0)
      + (if r2 t = r4 t then 1 else 0))
      + (w.1 - 2 * w.2.1 + w.2.2.2) * (if r1 t = r3 t ∧ r2 t = r4 t then 1 else 0)
      + (w.2.2.1 - w.2.2.2) * (if r1 t = r4 t then 1 else 0) := by
  obtain ⟨p1, p2, p3⟩ := ht
  unfold cw ce
  by_cases h13 : r1 t = r3 t
  · have h14 : r1 t ≠ r4 t := fun h => p3 (h13 ▸ h)
    by_cases h24 : r2 t = r4 t
    · simp [eq_true h13, eq_true h24, eq_false h14, dot]; try ring
    · simp [eq_true h13, eq_false h24, eq_false h14, dot]
  · by_cases h24 : r2 t = r4 t
    · have h14 : r1 t ≠ r4 t := fun h => p1 (h ▸ h24.symm ▸ rfl)
      simp [eq_false h13, eq_true h24, eq_false h14, dot]
    · by_cases h14 : r1 t = r4 t
      · simp [eq_false h13, eq_false h24, eq_true h14, dot]
      · simp [eq_false h13, eq_false h24, eq_false h14, dot]

/-- **The class counts through four counts.** -/
theorem dot_cnt_split (w : Q) (Y : Col) :
    dot (cnt Y) w = w.2.2.2 * ((stsC Y).card : ℤ)
      + (w.2.1 - w.2.2.2) * ((((stsC Y).filter (fun t => r1 t = r3 t)).card : ℤ)
          + (((stsC Y).filter (fun t => r2 t = r4 t)).card : ℤ))
      + (w.1 - 2 * w.2.1 + w.2.2.2)
          * (((stsC Y).filter (fun t => r1 t = r3 t ∧ r2 t = r4 t)).card : ℤ)
      + (w.2.2.1 - w.2.2.2) * (((stsC Y).filter (fun t => r1 t = r4 t)).card : ℤ) := by
  rw [dot_cnt, Finset.sum_congr rfl (fun t (ht : t ∈ stsC Y) => cw_split w (proper_of_mem_sts ht))]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
    Finset.sum_boole]
  ring

/-- The uniform column: class counts `(12, 48, 24, 24)`. -/
theorem cnt_range4 : cnt (range 4, range 4, range 4, range 4) = (12, 48, 24, 24) := by
  decide +kernel

/-- A constant column of a four-set is a renamed uniform column. -/
theorem cnt_const {P : Finset ℕ} (hP : P.card = 4) :
    cnt (P, P, P, P) = cnt (range 4, range 4, range 4, range 4) := by
  set e := P.orderEmbOfFin hP
  let f : ℕ → ℕ := fun i => if h : i < 4 then e ⟨i, h⟩ else 0
  have hinj : Set.InjOn f ↑(range 4) := by
    intro i hi j hj hij
    simp only [coe_range, Set.mem_Iio] at hi hj
    simp only [f, hi, hj, dite_true] at hij
    exact congrArg Fin.val (e.injective hij)
  have himg : (range 4).image f = P := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro x hx
      have hx' : x ∈ Set.range e := by rw [Finset.range_orderEmbOfFin]; exact hx
      obtain ⟨i, rfl⟩ := hx'
      refine Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr i.2, ?_⟩
      simp [f, i.2]
    · rw [Finset.card_image_of_injOn hinj, card_range, hP]
  have hU : uni (range 4, range 4, range 4, range 4) = range 4 := by simp [uni]
  rw [← cnt_image (f := f) (Y := (range 4, range 4, range 4, range 4)) (by rw [hU]; exact hinj)]
  simp [imgC, himg]

/-- **The initial inequality at `k = 4`**, on the cone `K`. -/
theorem init_cnt {X : Col} (hX : CardsIn 4 4 X) : RaysOK (cnt X - (12, 48, 24, 24)) := by
  obtain ⟨X₁, X₂, X₃, X₄⟩ := X
  obtain ⟨⟨a1, a1'⟩, ⟨a2, a2'⟩, ⟨a3, a3'⟩, ⟨a4, a4'⟩⟩ := hX
  simp only at a1 a1' a2 a2' a3 a3' a4 a4'
  have h₁ : X₁.card = 4 := le_antisymm a1' a1
  have h₂ : X₂.card = 4 := le_antisymm a2' a2
  have h₃ : X₃.card = 4 := le_antisymm a3' a3
  have h₄ : X₄.card = 4 := le_antisymm a4' a4
  by_cases hS : (X₁ \ X₂).card + (X₂ \ X₃).card + (X₃ \ X₄).card = 0
  · have s12 : X₁ \ X₂ = ∅ := Finset.card_eq_zero.mp (by omega)
    have s23 : X₂ \ X₃ = ∅ := Finset.card_eq_zero.mp (by omega)
    have s34 : X₃ \ X₄ = ∅ := Finset.card_eq_zero.mp (by omega)
    have e12 : X₁ = X₂ := Finset.eq_of_subset_of_card_le (Finset.sdiff_eq_empty_iff_subset.mp s12)
      (by omega)
    have e23 : X₂ = X₃ := Finset.eq_of_subset_of_card_le (Finset.sdiff_eq_empty_iff_subset.mp s23)
      (by omega)
    have e34 : X₃ = X₄ := Finset.eq_of_subset_of_card_le (Finset.sdiff_eq_empty_iff_subset.mp s34)
      (by omega)
    subst e12 e23 e34
    rw [cnt_const h₁, cnt_range4, sub_self]
    intro r _
    rw [dot_zero]
  · have hgain := card_sts_gain h₁ h₂ h₃ h₄ (by norm_num)
    have hS' : (1 : ℤ) ≤ ((X₁ \ X₂).card : ℤ) + (X₂ \ X₃).card + (X₃ \ X₄).card := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hS
    have hN : (116 : ℤ) ≤ (sts X₁ X₂ X₃ X₄).card := by
      push_cast at hgain; nlinarith
    obtain ⟨-, -, c14, -, m13, m24, cov⟩ := pat_counts5 (A₁ := X₁) (A₂ := X₂) (A₃ := X₃)
      (A₄ := X₄) (by omega) (by omega) (by omega) (by omega)
    have c14' : 3 * (((sts X₁ X₂ X₃ X₄).filter (fun t => r1 t = r4 t)).card : ℤ)
        ≤ (sts X₁ X₂ X₃ X₄).card := by exact_mod_cast c14
    have m13' : (((sts X₁ X₂ X₃ X₄).filter (fun t => r1 t = r3 t ∧ r2 t = r4 t)).card : ℤ)
        ≤ ((sts X₁ X₂ X₃ X₄).filter (fun t => r1 t = r3 t)).card := by exact_mod_cast m13
    have m24' : (((sts X₁ X₂ X₃ X₄).filter (fun t => r1 t = r3 t ∧ r2 t = r4 t)).card : ℤ)
        ≤ ((sts X₁ X₂ X₃ X₄).filter (fun t => r2 t = r4 t)).card := by exact_mod_cast m24
    have cov' : (((sts X₁ X₂ X₃ X₄).filter (fun t => r1 t = r3 t)).card : ℤ)
        + ((sts X₁ X₂ X₃ X₄).filter (fun t => r2 t = r4 t)).card
        - ((sts X₁ X₂ X₃ X₄).filter (fun t => r1 t = r3 t ∧ r2 t = r4 t)).card
        + ((sts X₁ X₂ X₃ X₄).filter (fun t => r1 t = r4 t)).card ≤ (sts X₁ X₂ X₃ X₄).card := by
      have h : (((((sts X₁ X₂ X₃ X₄).filter (fun t => r1 t = r3 t)).card : ℤ)
          + ((sts X₁ X₂ X₃ X₄).filter (fun t => r2 t = r4 t)).card
          - ((sts X₁ X₂ X₃ X₄).filter (fun t => r1 t = r3 t ∧ r2 t = r4 t)).card
          + ((sts X₁ X₂ X₃ X₄).filter (fun t => r1 t = r4 t)).card : ℤ) : ℝ)
          ≤ (((sts X₁ X₂ X₃ X₄).card : ℤ) : ℝ) := by push_cast; exact cov
      exact_mod_cast h
    have m0 : (0 : ℤ)
        ≤ (((sts X₁ X₂ X₃ X₄).filter (fun t => r1 t = r3 t ∧ r2 t = r4 t)).card : ℤ) := by
      positivity
    have n140 : (0 : ℤ) ≤ (((sts X₁ X₂ X₃ X₄).filter (fun t => r1 t = r4 t)).card : ℤ) := by
      positivity
    intro r hr
    rw [dot_sub, dot_cnt_split]
    simp only [stsC]
    simp only [rays, List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [dot] <;> linarith

end GridGen.Four.K4
