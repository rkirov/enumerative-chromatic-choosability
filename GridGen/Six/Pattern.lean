/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Six.PatData

/-!
# Height six at `k = 6`: the pattern lemma on the cone

`ai_research_notes/cx/h6k6/NOTE.md` (Codex, OpenAI), checked in `H6_K6_REVIEW_2026-10-29.md` §2;
`GridGen/Five/K5/Pattern.lean` with six rows. For lists `A₁, …, A₆` of five or six colours, every
weight `w` of the cone and every orbit `o`, the average pattern weight of the proper columns is
at least the average weight of the uniform successors of a column in orbit `o`, divided by
`R(n, o)` (`Rof`, over `10¹²`):

`10¹² · |sts A| · rowV6 o w ≤ R(n, o) · NUo o · G w A` (`pattern66`).

At a ray the certificate of `GridGen/Six/PatData.lean` bounds the actual average by weak duality
(`lp_count6`); on `Q` the certificate at the midpoint applies with the slack `7/(2·10⁷)`, since
every coordinate of `Q` is within that of the midpoint.
-/

namespace GridGen.Six

open Finset

/-- The index of a size vector in `patCerts`. -/
def nidx (a b c d e f : ℕ) : ℕ :=
  (a - 5) * 32 + (b - 5) * 16 + (c - 5) * 8 + (d - 5) * 4 + (e - 5) * 2 + (f - 5)

/-- The number of uniform successors of a column in orbit `o`. -/
def NUo (o : Fin 32) : ℕ := ∑ j, Vmat6 o j

/-- `2·10⁷` times the uniform row at the midpoint of `Q`. -/
def gmidDot (o : Fin 32) : ℕ := ∑ j, Vmat6 o j * (qL j + qU j)

/-- **The check of a pattern certificate.** -/
def patOK (nv : List ℕ) (C : PatCert) : Bool :=
  C.ev.all peelOKB &&
  (List.range 6).all (fun k => ptOK nv C k) &&
  (List.range 5).all (fun k => (List.finRange 32).all (fun o =>
    decide (1000000000000 * DP * Fv (k + 1) o + C.R.getD o 0 * NUo o * zsumL C.ev (C.zs.getD k [])
      ≤ C.R.getD o 0 * NUo o * C.lam.getD k 0))) &&
  (List.finRange 32).all (fun o =>
    decide (1000000000000 * DP * (gmidDot o + 7 * NUo o)
        + C.R.getD o 0 * NUo o * (zsumL C.ev (C.zs.getD 5 []) + 7 * DP)
      ≤ C.R.getD o 0 * NUo o * C.lam.getD 5 0))

/-- The certificates for the size vectors with first size `a`. -/
def allPatA (a : ℕ) : Bool :=
  [5, 6].all fun b => [5, 6].all fun c => [5, 6].all fun d => [5, 6].all fun e =>
    [5, 6].all fun f => patOK [a, b, c, d, e, f] (patCerts.getD (nidx a b c d e f) default)

theorem allPat5 : allPatA 5 = true := by decide +kernel
theorem allPat6 : allPatA 6 = true := by decide +kernel

/-- The ratio bound `R(n, o)`, times `10¹²`. -/
def Rof (a b c d e f : ℕ) (o : Fin 32) : ℕ :=
  (patCerts.getD (nidx a b c d e f) default).R.getD o 0

theorem qU_le : ∀ j : Fin 32, qL j ≤ qU j ∧ qU j ≤ qL j + 7 := by decide +kernel

theorem mem56 {n : ℕ} (h : n = 5 ∨ n = 6) : n ∈ [5, 6] := by
  rcases h with rfl | rfl <;> simp

theorem G_eq_sum (w : Wt6) (A₁ A₂ A₃ A₄ A₅ A₆ : Finset ℕ) :
    G w A₁ A₂ A₃ A₄ A₅ A₆ = ∑ t ∈ sts A₁ A₂ A₃ A₄ A₅ A₆, w (orb t) := rfl

theorem sum_gval5_le {w : Wt6} (hq : InQ6 w) (S : Finset T6) :
    (((∑ t ∈ S, gval 5 (orb t) : ℕ)) : ℝ) - 7 * S.card ≤ 20000000 * ∑ t ∈ S, w (orb t) := by
  push_cast
  rw [Finset.mul_sum, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun t _ => ?_
  have h2' : (qU (orb t) : ℝ) ≤ qL (orb t) + 7 := by exact_mod_cast (qU_le (orb t)).2
  have : (qL (orb t) : ℝ) ≤ 10000000 * w (orb t) := by
    have := (hq (orb t)).1; rw [div_le_iff₀ (by norm_num)] at this; linarith
  simp only [gval, show ¬ (5 < 5) from by norm_num, ite_false]
  push_cast
  generalize (qL (orb t) : ℝ) = a at h2' this ⊢
  generalize (qU (orb t) : ℝ) = b at h2' this ⊢
  linarith

theorem rowV6_mid {w : Wt6} (hq : InQ6 w) (o : Fin 32) :
    20000000 * rowV6 o w ≤ (gmidDot o : ℝ) + 7 * NUo o := by
  unfold rowV6 gmidDot NUo
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  have h1' : (qL j : ℝ) ≤ qU j := by exact_mod_cast (qU_le j).1
  have : 10000000 * w j ≤ (qU j : ℝ) := by
    have := (hq j).2; rw [le_div_iff₀ (by norm_num)] at this; linarith
  have h2' : (qU j : ℝ) ≤ qL j + 7 := by exact_mod_cast (qU_le j).2
  have hv : (0 : ℝ) ≤ Vmat6 o j := Nat.cast_nonneg _
  generalize (Vmat6 o j : ℝ) = v at hv ⊢
  generalize (qL j : ℝ) = a at h1' h2' this ⊢
  generalize (qU j : ℝ) = b at h1' h2' this ⊢
  generalize w j = x at this ⊢
  nlinarith

/-- The arithmetic of the `Q` case. -/
theorem coreQ {Λ Z S N R D E NU gm G V : ℝ} (hN : 0 ≤ N) (hR : 0 ≤ R) (hNU : 0 ≤ NU) (hD : 0 < D)
    (hE : 0 ≤ E) (hl : Λ * N ≤ D * S + Z * N) (hm : E * D * (gm + 7 * NU) + R * NU * (Z + 7 * D)
      ≤ R * NU * Λ) (hG : S - 7 * N ≤ 20000000 * G) (hV : 20000000 * V ≤ gm + 7 * NU) :
    E * N * V ≤ R * NU * G := by
  have hRN : 0 ≤ R * NU := mul_nonneg hR hNU
  have k1 := mul_le_mul_of_nonneg_left hV (mul_nonneg (mul_nonneg hE hD.le) hN)
  have k2 := mul_le_mul_of_nonneg_left hG (mul_nonneg hRN hD.le)
  have k3 := mul_le_mul_of_nonneg_left hl hRN
  have k4 := mul_le_mul_of_nonneg_right hm hN
  have key : E * N * V * (20000000 * D) ≤ R * NU * G * (20000000 * D) := by nlinarith
  exact le_of_mul_le_mul_right key (by positivity)

/-- **The pattern lemma on the cone.** -/
theorem pattern66 {w : Wt6} (hw : InCone6 w) (o : Fin 32) {A₁ A₂ A₃ A₄ A₅ A₆ : Finset ℕ}
    (h₁ : A₁.card = 5 ∨ A₁.card = 6) (h₂ : A₂.card = 5 ∨ A₂.card = 6)
    (h₃ : A₃.card = 5 ∨ A₃.card = 6) (h₄ : A₄.card = 5 ∨ A₄.card = 6)
    (h₅ : A₅.card = 5 ∨ A₅.card = 6) (h₆ : A₆.card = 5 ∨ A₆.card = 6) :
    (1000000000000 : ℝ) * (sts A₁ A₂ A₃ A₄ A₅ A₆).card * rowV6 o w
      ≤ Rof A₁.card A₂.card A₃.card A₄.card A₅.card A₆.card o * NUo o
        * G w A₁ A₂ A₃ A₄ A₅ A₆ := by
  set nv : List ℕ := [A₁.card, A₂.card, A₃.card, A₄.card, A₅.card, A₆.card] with hnv
  set C := patCerts.getD (nidx A₁.card A₂.card A₃.card A₄.card A₅.card A₆.card) default with hC
  have hok : patOK nv C = true := by
    have hA : allPatA A₁.card = true := by rcases h₁ with h | h <;> rw [h]; exacts [allPat5, allPat6]
    simp only [allPatA, List.all_eq_true] at hA
    exact hA _ (mem56 h₂) _ (mem56 h₃) _ (mem56 h₄) _ (mem56 h₅) _ (mem56 h₆)
  simp only [patOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    List.mem_finRange, true_implies] at hok
  obtain ⟨⟨⟨hev, hpt⟩, hray⟩, hmid⟩ := hok
  have hX : ∀ i < 6, nv.getD i 0 ≤ (bl A₁ A₂ A₃ A₄ A₅ A₆ i).card := by
    intro i hi; interval_cases i <;> exact le_rfl
  have hn : ∀ i < 6, 1 ≤ frcL nv i := by
    intro i hi
    interval_cases i <;> simp only [frcL, frc, hnv] <;> norm_num <;> omega
  have hB : ∀ ev ∈ C.ev, evB nv ev * ((sts A₁ A₂ A₃ A₄ A₅ A₆).filter
      (fun t => evHolds ev t = true)).card ≤ (sts A₁ A₂ A₃ A₄ A₅ A₆).card :=
    fun ev he => ev_count hX hn ev (hev ev he)
  have hRof : Rof A₁.card A₂.card A₃.card A₄.card A₅.card A₆.card o = C.R.getD o 0 := rfl
  rw [hRof, G_eq_sum]
  clear_value C nv
  have hD : 0 < DP := by decide
  have hE : ((1000000000000 : ℕ) : ℝ) = 1000000000000 := by norm_num
  rw [← hE]
  rcases hw with hq | ⟨k, hk, rfl⟩
  · -- the box `Q`
    have hl := lp_count6 (k := 5) hev hB (hpt 5 (by norm_num))
    have hm := hmid o
    have hG' := sum_gval5_le hq (sts A₁ A₂ A₃ A₄ A₅ A₆)
    have hV := rowV6_mid hq o
    generalize C.lam.getD 5 0 = Λ at hl hm
    generalize zsumL C.ev (C.zs.getD 5 []) = Z at hl hm
    generalize ∑ t ∈ sts A₁ A₂ A₃ A₄ A₅ A₆, gval 5 (orb t) = S at hl hG'
    generalize (sts A₁ A₂ A₃ A₄ A₅ A₆).card = N at hl hG' ⊢
    generalize C.R.getD o 0 = R at hm ⊢
    generalize DP = D at hl hm hD
    generalize (1000000000000 : ℕ) = E at hm ⊢
    generalize ∑ t ∈ sts A₁ A₂ A₃ A₄ A₅ A₆, w (orb t) = G at hG' ⊢
    generalize gmidDot o = gm at hm hV
    generalize NUo o = NU at hm hV ⊢
    have hlR : (Λ : ℝ) * N ≤ D * S + Z * N := by exact_mod_cast hl
    have hmR : (E : ℝ) * D * (gm + 7 * NU) + R * NU * (Z + 7 * D) ≤ R * NU * Λ := by
      exact_mod_cast hm
    exact coreQ (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (by exact_mod_cast hD) (Nat.cast_nonneg _) hlR hmR hG' hV
  · -- a ray
    have hl := lp_count6 (k := k) hev hB (hpt k (by omega))
    have hr := hray k hk o
    have hF0 : (0 : ℝ) < Fv k 0 := by exact_mod_cast Fv_pos k (by omega)
    have eS : ∑ t ∈ sts A₁ A₂ A₃ A₄ A₅ A₆, rayW k (orb t)
        = ((∑ t ∈ sts A₁ A₂ A₃ A₄ A₅ A₆, gval k (orb t) : ℕ) : ℝ) / Fv k 0 := by
      push_cast; rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [rayW, gval, hk, ite_true]
    rw [eS, rowV6_rayW hk]
    generalize C.lam.getD k 0 = Λ at hl hr
    generalize zsumL C.ev (C.zs.getD k []) = Z at hl hr
    generalize ∑ t ∈ sts A₁ A₂ A₃ A₄ A₅ A₆, gval k (orb t) = S at hl ⊢
    generalize (sts A₁ A₂ A₃ A₄ A₅ A₆).card = N at hl ⊢
    generalize C.R.getD o 0 = R at hr ⊢
    generalize DP = D at hl hr hD
    generalize (1000000000000 : ℕ) = E at hr ⊢
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

end GridGen.Six
