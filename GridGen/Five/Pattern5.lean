/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.PatCert5
import GridGen.Five.Init5

/-!
# Height five: the pattern lemma

`ai_research_notes/H5_K6_ANALYTIC_2026-10-23.md` Lemma 8. For a list system with lists of at
least five colours, every weight `w` in the box and every orbit `i`, the average pattern weight
of the proper columns is at least `c_P = 971038/10⁶` times the average weight of the uniform
successors of a column in orbit `i` (row `i` of the reduced transfer matrix):

`c_P · |sts A| · rowV i w ≤ (Σⱼ Vᵢⱼ) · G w A` (`pattern5`).

Both sides are linear in `w`, so the corner of the box fixed by the signs of the coefficients
suffices (`corner_pick`); there the chain linear programme with the certificate of
`GridGen/Five/PatCert5.lean` bounds the actual average (`lp_count`). The constant `c_P` is the
exact optimum `3083807/3175784` rounded down, so the pattern term costs `-log c_P ≈ 0.029390`.
-/

namespace GridGen.Five

open Finset

theorem rowsum_eq (i : Fin 11) :
    ((sum11 (fun o => (VL.getD i []).getD o 0) : ℕ) : ℝ) = ∑ j, (Vmat i j : ℝ) := by
  rw [sum11_eq]; push_cast
  exact Finset.sum_congr rfl fun j _ => by rw [VL_eq]

/-- **The pattern lemma at height five.** -/
theorem pattern5 {w : Wt5} (hw : InBox5 w) (i : Fin 11) {A₁ A₂ A₃ A₄ A₅ : Finset ℕ}
    (h₁ : 5 ≤ A₁.card) (h₂ : 5 ≤ A₂.card) (h₃ : 5 ≤ A₃.card) (h₄ : 5 ≤ A₄.card)
    (h₅ : 5 ≤ A₅.card) :
    (971038 / 1000000 : ℝ) * (sts A₁ A₂ A₃ A₄ A₅).card * rowV i w
      ≤ (∑ j, (Vmat i j : ℝ)) * G w A₁ A₂ A₃ A₄ A₅ := by
  set Ω := sts A₁ A₂ A₃ A₄ A₅ with hΩ
  set N : ℝ := (Ω.card : ℝ) with hN
  set R : ℝ := ∑ j, (Vmat i j : ℝ) with hR
  set F : Fin 11 → ℝ := fun o => ((Ω.filter (fun t => orb t = o)).card : ℝ) with hF
  have hG : G w A₁ A₂ A₃ A₄ A₅ = ∑ o, F o * w o := sum_gw_orb w Ω
  have hV : rowV i w = ∑ o, (Vmat i o : ℝ) * w o := rfl
  rw [hG, hV, ← sub_nonneg, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hlin : ∀ o, R * (F o * w o) - 971038 / 1000000 * N * ((Vmat i o : ℝ) * w o)
      = (R * F o - 971038 / 1000000 * N * Vmat i o) * w o := fun o => by ring
  simp only [hlin]
  obtain ⟨β, hβ, hpick⟩ := corner_pick hw (fun o => R * F o - 971038 / 1000000 * N * Vmat i o)
  refine le_trans ?_ hpick
  -- the certificate of this corner
  obtain ⟨c, hc⟩ := exists_mem_zip (l₂ := patCerts)
    (by rw [length_allBits, patCerts_length]; rfl) hβ
  have hok := List.all_eq_true.mp patCerts_ok _ hc
  simp only [patOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hpt, hZ⟩, r0⟩, r1⟩, r2⟩, r3⟩, r4⟩, r5⟩, r6⟩, r7⟩, r8⟩, r9⟩, r10⟩ := hok
  have hrow : patRowOK β c.1 c.2 i = true := by
    fin_cases i
    · exact r0
    · exact r1
    · exact r2
    · exact r3
    · exact r4
    · exact r5
    · exact r6
    · exact r7
    · exact r8
    · exact r9
    · exact r10
  simp only [patRowOK, decide_eq_true_eq] at hrow
  have hB : ∀ p < 14, chainB 5 p * (Ω.filter (fun t => evb p t = true)).card ≤ Ω.card :=
    fun p _ => chain_bound (L := 5) (by norm_num) h₁ h₂ h₃ h₄ h₅ p
  have hlp := lp_count (fun t ht => proper_of_mem_sts ht) (chainB 5) hB hpt
  rw [← zsum_eq] at hlp
  have hlpR : (c.1 : ℝ) * N ≤ 5000 * (2000 * ∑ o, F o * sigR β o) + (zsum c.2 : ℝ) * N := by
    rw [hN, hF, ← sum_sigN_orb]; exact_mod_cast hlp
  have hrowR : (1000000 : ℝ) * R * zsum c.2
      + 971038 * 5000 * ∑ o, (Vmat i o : ℝ) * (2000 * sigR β o) ≤ 1000000 * R * c.1 := by
    have h' : ((1000000 * sum11 (fun o => (VL.getD i []).getD o 0) * zsum c.2 : ℕ) : ℝ)
        + ((971038 * 5000 * sum11 (fun o => (VL.getD i []).getD o 0 * sigN β o) : ℕ) : ℝ)
        ≤ ((1000000 * sum11 (fun o => (VL.getD i []).getD o 0) * c.1 : ℕ) : ℝ) := by
      rw [← Nat.cast_add]; exact Nat.cast_le.mpr hrow
    simp only [sum11_eq] at h'
    push_cast at h'
    simp only [VL_eq, sigN_eq] at h'
    rw [hR]; linarith [h']
  have hZR : (zsum c.2 : ℝ) ≤ c.1 := by exact_mod_cast hZ
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun j _ => Nat.cast_nonneg _
  have e : ∑ o, (R * F o - 971038 / 1000000 * N * Vmat i o) * sigR β o
      = R * ∑ o, F o * sigR β o - 971038 / 1000000 * N * ∑ o, (Vmat i o : ℝ) * sigR β o := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun o _ => by ring
  have e2 : ∑ o, (Vmat i o : ℝ) * (2000 * sigR β o) = 2000 * ∑ o, (Vmat i o : ℝ) * sigR β o := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun o _ => by ring
  rw [e]
  rw [e2] at hrowR
  have k1 := mul_le_mul_of_nonneg_left hlpR hR0
  have k2 := mul_le_mul_of_nonneg_left hrowR hN0
  nlinarith

end GridGen.Five
