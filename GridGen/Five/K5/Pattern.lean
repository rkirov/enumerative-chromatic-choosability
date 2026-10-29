/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.K5.PatData

/-!
# Height five at `k = 5`: the pattern lemma on the cone

`ai_research_notes/cx/h5k5/NOTE.md` §2 (Codex), checked in `H5_K5_REVIEW_2026-10-28.md` (b).
For lists `A₁, …, A₅` of four or five colours, every weight `w` of the cone and every orbit `o`,
the average pattern weight of the proper columns is at least the average weight of the uniform
successors of a column in orbit `o`, divided by `R(n, o)` (`Rof`, over `10⁹`):

`10⁹ · |sts A| · rowV5 o w ≤ R(n, o) · NUo o · G w A` (`pattern55`).

At a ray the certificate of `GridGen/Five/K5/PatData.lean` bounds the actual average by weak
duality (`lp_count5`); on `Q` the certificate at the midpoint `c` applies with the slack
`ε = 5/(2·10⁶)`, since every coordinate of `Q` is within `ε` of `c`.
-/

namespace GridGen.Five.K5

open Finset GridGen.Five GridGen.Five.Ex5

/-- The index of a size vector in `patCerts`. -/
def nidx (a b c d e : ℕ) : ℕ := (a - 4) * 16 + (b - 4) * 8 + (c - 4) * 4 + (d - 4) * 2 + (e - 4)

/-- The number of uniform successors of a column in orbit `o`. -/
def NUo (o : Fin 11) : ℕ := ∑ j, Vmat5 o j

/-- `2·10⁶` times the uniform row at the midpoint of `Q`. -/
def gmidDot (o : Fin 11) : ℕ := ∑ j, Vmat5 o j * (qL j + qU j)

/-- **The check of a pattern certificate.** -/
def patOK (nv : List ℕ) (C : PatCert) : Bool :=
  C.ev.all peelOKB &&
  (List.range 6).all (fun k => ptOK nv C k) &&
  (List.range 5).all (fun k => (List.finRange 11).all (fun o =>
    decide (1000000000 * DP * Fv (k + 1) o + C.R.getD o 0 * NUo o * zsumL C.ev (C.zs.getD k [])
      ≤ C.R.getD o 0 * NUo o * C.lam.getD k 0))) &&
  (List.finRange 11).all (fun o =>
    decide (1000000000 * DP * (gmidDot o + 5 * NUo o)
        + C.R.getD o 0 * NUo o * (zsumL C.ev (C.zs.getD 5 []) + 5 * DP)
      ≤ C.R.getD o 0 * NUo o * C.lam.getD 5 0))

/-- All 32 certificates. -/
def allPat : Bool :=
  [4, 5].all fun a => [4, 5].all fun b => [4, 5].all fun c => [4, 5].all fun d =>
    [4, 5].all fun e => patOK [a, b, c, d, e] (patCerts.getD (nidx a b c d e) default)

theorem allPat_ok : allPat = true := by decide +kernel

/-- The ratio bound `R(n, o)`, times `10⁹`. -/
def Rof (a b c d e : ℕ) (o : Fin 11) : ℕ := (patCerts.getD (nidx a b c d e) default).R.getD o 0

theorem qU_le : ∀ j : Fin 11, qL j ≤ qU j ∧ qU j ≤ qL j + 5 := by decide

theorem mem45 {n : ℕ} (h : n = 4 ∨ n = 5) : n ∈ [4, 5] := by
  rcases h with rfl | rfl <;> simp

theorem G_eq_sum (w : Wt5) (A₁ A₂ A₃ A₄ A₅ : Finset ℕ) :
    G w A₁ A₂ A₃ A₄ A₅ = ∑ t ∈ sts A₁ A₂ A₃ A₄ A₅, w (orb t) := rfl

/-- **The pattern lemma on the cone.** -/
theorem pattern55 {w : Wt5} (hw : InCone5 w) (o : Fin 11) {A₁ A₂ A₃ A₄ A₅ : Finset ℕ}
    (h₁ : A₁.card = 4 ∨ A₁.card = 5) (h₂ : A₂.card = 4 ∨ A₂.card = 5)
    (h₃ : A₃.card = 4 ∨ A₃.card = 5) (h₄ : A₄.card = 4 ∨ A₄.card = 5)
    (h₅ : A₅.card = 4 ∨ A₅.card = 5) :
    (1000000000 : ℝ) * (sts A₁ A₂ A₃ A₄ A₅).card * rowV5 o w
      ≤ Rof A₁.card A₂.card A₃.card A₄.card A₅.card o * NUo o * G w A₁ A₂ A₃ A₄ A₅ := by
  set nv : List ℕ := [A₁.card, A₂.card, A₃.card, A₄.card, A₅.card] with hnv
  set C := patCerts.getD (nidx A₁.card A₂.card A₃.card A₄.card A₅.card) default with hC
  have hok : patOK nv C = true := by
    have h := allPat_ok
    simp only [allPat, List.all_eq_true] at h
    exact h _ (mem45 h₁) _ (mem45 h₂) _ (mem45 h₃) _ (mem45 h₄) _ (mem45 h₅)
  simp only [patOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    List.mem_finRange, true_implies] at hok
  obtain ⟨⟨⟨hev, hpt⟩, hray⟩, hmid⟩ := hok
  have hX : ∀ i < 5, nv.getD i 0 ≤ (bl A₁ A₂ A₃ A₄ A₅ i).card := by
    intro i hi; interval_cases i <;> exact le_rfl
  have hn : ∀ i < 5, 1 ≤ frcL nv i := by
    intro i hi
    interval_cases i <;> simp only [frcL, frc, hnv] <;> norm_num <;> omega
  have hB : ∀ ev ∈ C.ev, evB nv ev * ((sts A₁ A₂ A₃ A₄ A₅).filter
      (fun t => evHolds ev t = true)).card ≤ (sts A₁ A₂ A₃ A₄ A₅).card :=
    fun ev he => ev_count hX hn ev (hev ev he)
  have hRof : Rof A₁.card A₂.card A₃.card A₄.card A₅.card o = C.R.getD o 0 := rfl
  rw [hRof, G_eq_sum]
  have hD : 0 < DP := by decide
  have hE : ((1000000000 : ℕ) : ℝ) = 1000000000 := by norm_num
  rw [← hE]
  rcases hw with hq | ⟨k, hk, rfl⟩
  · -- the box `Q`
    have hl := lp_count5 (k := 5) hev hB (hpt 5 (by norm_num))
    have hm := hmid o
    have hG' : ∑ t ∈ sts A₁ A₂ A₃ A₄ A₅, ((gval 5 (orb t) : ℕ) : ℝ) - 5 * (sts A₁ A₂ A₃ A₄ A₅).card
        ≤ 2000000 * ∑ t ∈ sts A₁ A₂ A₃ A₄ A₅, w (orb t) := by
      rw [Finset.mul_sum, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_le_sum fun t _ => ?_
      have h2' : (qU (orb t) : ℝ) ≤ qL (orb t) + 5 := by exact_mod_cast (qU_le (orb t)).2
      have : (qL (orb t) : ℝ) ≤ 1000000 * w (orb t) := by
        have := (hq (orb t)).1; rw [div_le_iff₀ (by norm_num)] at this; linarith
      simp only [gval, show ¬ (5 < 5) from by norm_num, ite_false]
      push_cast
      linarith
    have hV : 2000000 * rowV5 o w ≤ (gmidDot o : ℝ) + 5 * NUo o := by
      unfold rowV5 gmidDot NUo
      push_cast
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun j _ => ?_
      have h1' : (qL j : ℝ) ≤ qU j := by exact_mod_cast (qU_le j).1
      have : 1000000 * w j ≤ (qU j : ℝ) := by
        have := (hq j).2; rw [le_div_iff₀ (by norm_num)] at this; linarith
      have h2' : (qU j : ℝ) ≤ qL j + 5 := by exact_mod_cast (qU_le j).2
      have hv : (0 : ℝ) ≤ Vmat5 o j := Nat.cast_nonneg _
      nlinarith
    rw [← Nat.cast_sum] at hG'
    generalize C.lam.getD 5 0 = Λ at hl hm
    generalize zsumL C.ev (C.zs.getD 5 []) = Z at hl hm
    generalize ∑ t ∈ sts A₁ A₂ A₃ A₄ A₅, gval 5 (orb t) = S at hl hG'
    generalize (sts A₁ A₂ A₃ A₄ A₅).card = N at hl hG' ⊢
    generalize C.R.getD o 0 = R at hm ⊢
    generalize DP = D at hl hm hD
    generalize (1000000000 : ℕ) = E at hm ⊢
    generalize ∑ t ∈ sts A₁ A₂ A₃ A₄ A₅, w (orb t) = G at hG' ⊢
    have hlR : (Λ : ℝ) * N ≤ D * S + Z * N := by exact_mod_cast hl
    have hmR : (E : ℝ) * D * (gmidDot o + 5 * NUo o) + R * NUo o * (Z + 5 * D)
        ≤ R * NUo o * Λ := by exact_mod_cast hm
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    have hRN : (0 : ℝ) ≤ R * NUo o := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hD' : (0 : ℝ) < D := by exact_mod_cast hD
    have hE0 : (0 : ℝ) ≤ E := Nat.cast_nonneg _
    have k1 := mul_le_mul_of_nonneg_left hV (mul_nonneg (mul_nonneg hE0 hD'.le) hN0)
    have k2 := mul_le_mul_of_nonneg_left hG' (mul_nonneg hRN hD'.le)
    have k3 := mul_le_mul_of_nonneg_left hlR hRN
    have k4 := mul_le_mul_of_nonneg_right hmR hN0
    have key : (E : ℝ) * N * rowV5 o w * (2000000 * D) ≤ R * NUo o * G * (2000000 * D) := by
      linarith
    exact le_of_mul_le_mul_right key (by positivity)
  · -- a ray
    have hl := lp_count5 (k := k) hev hB (hpt k (by omega))
    have hr := hray k hk o
    have hF0 : (0 : ℝ) < Fv k 0 := by exact_mod_cast Fv_pos k (by omega)
    have eS : ∑ t ∈ sts A₁ A₂ A₃ A₄ A₅, rayW k (orb t)
        = ((∑ t ∈ sts A₁ A₂ A₃ A₄ A₅, gval k (orb t) : ℕ) : ℝ) / Fv k 0 := by
      push_cast; rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [rayW, gval, hk, ite_true]
    rw [eS, rowV5_rayW hk]
    generalize C.lam.getD k 0 = Λ at hl hr
    generalize zsumL C.ev (C.zs.getD k []) = Z at hl hr
    generalize ∑ t ∈ sts A₁ A₂ A₃ A₄ A₅, gval k (orb t) = S at hl ⊢
    generalize (sts A₁ A₂ A₃ A₄ A₅).card = N at hl ⊢
    generalize C.R.getD o 0 = R at hr ⊢
    generalize DP = D at hl hr hD
    generalize (1000000000 : ℕ) = E at hr ⊢
    have hlR : (Λ : ℝ) * N ≤ D * S + Z * N := by exact_mod_cast hl
    have hrR : (E : ℝ) * D * Fv (k + 1) o + R * NUo o * Z ≤ R * NUo o * Λ := by
      exact_mod_cast hr
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    have hRN : (0 : ℝ) ≤ R * NUo o := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hD' : (0 : ℝ) < D := by exact_mod_cast hD
    have k1 := mul_le_mul_of_nonneg_right hrR hN0
    have k2 := mul_le_mul_of_nonneg_left hlR hRN
    have keyR : (E : ℝ) * N * Fv (k + 1) o * D ≤ R * NUo o * S * D := by linarith
    have keyR' := le_of_mul_le_mul_right keyR hD'
    rw [mul_div_assoc', mul_div_assoc', div_le_div_iff_of_pos_right hF0]
    linarith

end GridGen.Five.K5
