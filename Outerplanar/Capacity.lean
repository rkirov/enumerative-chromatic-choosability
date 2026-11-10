/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.Maximal
import Outerplanar.Rotate
import Outerplanar.FullCover

/-!
# The capacity lemma: the induction on the number of colours

`CL k n` is the capacity lemma for `k`-fold partial covers of the cycle of length `n`
(`ai_research_notes/OUTERPLANAR_PROOF_DRAFT_2026-11-09.md`, section 2). This file has the
induction step from `k - 1` to `k`, given a witness law, and the digon at `k = 4`.
-/

namespace Outerplanar

open Finset

/-- **The capacity lemma** for `k` colours on the cycle of length `n`. -/
def CL (k n : ℕ) [NeZero n] : Prop :=
  ∀ P : Cover n, (∀ i, (P.F i).card = k) → P.IsMatching → P.NoClosedThread →
    ∀ b, P.CapGE univ b (lam k n)

theorem lam_pos {k n : ℕ} (hk : 3 ≤ k) (hn : 1 ≤ n) : 0 < lam k n := by
  have hk' : (2 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have h1 : (2 : ℝ) ≤ ((k : ℝ) - 1) ^ n :=
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
      _ ≤ ((k : ℝ) - 1) ^ n := pow_le_pow_left₀ (by norm_num) hk' n
  have h2 : (-1 : ℝ) ^ n ≤ 1 := by
    rcases neg_one_pow_eq_or ℝ n with h | h <;> simp [h]
  rw [lam]
  linarith

theorem lam_pred {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    lam (k - 1) n = ((k : ℝ) - 2) ^ n - (-1) ^ n := by
  rw [lam, Nat.cast_sub hk]
  norm_num
  ring_nf

variable {n : ℕ} [NeZero n]

/-- **The induction step**: from `k - 1` colours to `k`, given the witness law. -/
theorem cl_step {k : ℕ} (hk : 4 ≤ k) (hn : 2 ≤ n) (hIH : CL (k - 1) n)
    (hW : Witness (n := n) k (-1) (lam (k - 1) n) (lam k n)) : CL k n := by
  refine Cover.capGE_of_maximal fun P hcard hM hno hmax b => ?_
  rcases Cover.full_or_cutSection hcard hM hno hmax with hfull | ⟨c, e, hc⟩
  · exact P.capGE_full hn hcard hM hfull hno b
  · exact P.capGE_of_witness (by omega) hcard hM hc (lam_pos (by omega) (by omega))
      (hIH _ (Cover.erase_card hcard hc.1) (Cover.erase_isMatching hM c)
        (Cover.erase_noClosedThread hno c) c) (hW.rotate e) b

namespace Cover

/-- A colour of a cut section is in conflict only with the section itself. -/
theorem IsCutSection.not_M_left {P : Cover n} (hM : P.IsMatching) {s : Fin n → ℕ} {e : Fin n}
    (hs : P.IsCutSection s e) (i : Fin n) {y : ℕ} (hy : y ∈ P.F (i + 1)) (hne : y ≠ s (i + 1)) :
    ¬ P.M i (s i) y := by
  intro h
  by_cases hie : i = e
  · subst hie
    exact hs.2.2.1 y hy h
  · exact hne ((hM i).1 (s i) (hs.1 i) y hy _ (hs.1 _) h (hs.2.1 i hie))

theorem IsCutSection.not_M_right {P : Cover n} (hM : P.IsMatching) {s : Fin n → ℕ} {e : Fin n}
    (hs : P.IsCutSection s e) (i : Fin n) {x : ℕ} (hx : x ∈ P.F i) (hne : x ≠ s i) :
    ¬ P.M i x (s (i + 1)) := by
  intro h
  by_cases hie : i = e
  · subst hie
    exact hs.2.2.2 x hx h
  · exact hne ((hM i).2 x hx (s i) (hs.1 i) _ (hs.1 _) h (hs.2.1 i hie))

end Cover

theorem sq_sum_two {F : Finset ℕ} (hF : F.card = 2) (v : ℕ → ℝ) :
    4 * ∏ c ∈ F, v c ≤ (∑ c ∈ F, v c) ^ 2 := by
  obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp hF
  rw [Finset.prod_pair hpq, Finset.sum_pair hpq]
  nlinarith [sq_nonneg (v p - v q)]

/-- The digon with four colours and two cut sections: eight colourings suffice. -/
theorem digon_two_sections (P : Cover 2) (hcard : ∀ i, (P.F i).card = 4) (hM : P.IsMatching)
    {s s' : Fin 2 → ℕ} {e e' : Fin 2} (hs : P.IsCutSection s e) (hs' : P.IsCutSection s' e')
    (hne : ∀ i, s' i ≠ s i) (b : Fin 2 → ℕ) : P.CapGE univ b 8 := by
  classical
  intro w hw
  have hwpos : ∀ i, ∀ c ∈ P.F i, 0 < w i c := fun i => (hw i (mem_univ i)).1
  -- the rest of each fibre
  set R : Fin 2 → Finset ℕ := fun i => ((P.F i).erase (s i)).erase (s' i) with hR
  have hs'mem : ∀ i, s' i ∈ (P.F i).erase (s i) := fun i =>
    Finset.mem_erase.mpr ⟨hne i, hs'.1 i⟩
  have hRcard : ∀ i, (R i).card = 2 := fun i => by
    rw [hR, Finset.card_erase_of_mem (hs'mem i), Finset.card_erase_of_mem (hs.1 i), hcard]
  have hRmem : ∀ i x, x ∈ R i → x ∈ P.F i ∧ x ≠ s i ∧ x ≠ s' i := fun i x hx => by
    have h1 := Finset.mem_erase.mp hx
    have h2 := Finset.mem_erase.mp h1.2
    exact ⟨h2.2, h2.1, h1.1⟩
  have hprod : ∀ i, w i (s i) * w i (s' i) * ∏ c ∈ R i, w i c = 1 := fun i => by
    rw [← (hw i (mem_univ i)).2, ← Finset.mul_prod_erase _ _ (hs.1 i),
      ← Finset.mul_prod_erase _ _ (hs'mem i)]
    ring
  -- the two blocks of colourings
  let T1 : Finset (ℕ × ℕ) := ({s 0, s' 0} : Finset ℕ) ×ˢ R 1
  let T2 : Finset (ℕ × ℕ) := R 0 ×ˢ ({s 1, s' 1} : Finset ℕ)
  let φ : ℕ × ℕ → Fin 2 → ℕ := fun xy => ![xy.1, xy.2]
  have hφinj : Function.Injective φ := fun a c h => by
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [φ, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    exact Prod.ext h0 h1
  have hdisj : Disjoint T1 T2 := by
    rw [Finset.disjoint_left]
    rintro ⟨x, y⟩ h1 h2
    simp only [T1, T2, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton] at h1 h2
    have := hRmem 0 x h2.1
    rcases h1.1 with h | h
    · exact this.2.1 h
    · exact this.2.2 h
  have hone : (1 : Fin 2) + 1 = 0 := by decide
  have hsub : (T1 ∪ T2).image φ ⊆ P.cols univ b := by
    intro f hf
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp hf
    rw [Cover.mem_cols]
    rw [Finset.mem_union] at hxy
    rcases hxy with h | h
    · simp only [T1, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton] at h
      obtain ⟨hx, hy⟩ := h
      have hy' := hRmem 1 y hy
      refine ⟨fun i => ⟨fun _ => ?_, fun hi => absurd (mem_univ i) hi⟩, fun i _ _ => ?_⟩
      · fin_cases i
        · rcases hx with rfl | rfl
          · exact hs.1 0
          · exact hs'.1 0
        · exact hy'.1
      · fin_cases i
        · show ¬ P.M 0 x y
          rcases hx with rfl | rfl
          · exact hs.not_M_left hM 0 hy'.1 hy'.2.1
          · exact hs'.not_M_left hM 0 hy'.1 hy'.2.2
        · show ¬ P.M 1 y (φ (x, y) (1 + 1))
          rw [hone]
          show ¬ P.M 1 y x
          rcases hx with rfl | rfl
          · have := hs.not_M_right hM 1 hy'.1 hy'.2.1
            rwa [hone] at this
          · have := hs'.not_M_right hM 1 hy'.1 hy'.2.2
            rwa [hone] at this
    · simp only [T2, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton] at h
      obtain ⟨hx, hy⟩ := h
      have hx' := hRmem 0 x hx
      refine ⟨fun i => ⟨fun _ => ?_, fun hi => absurd (mem_univ i) hi⟩, fun i _ _ => ?_⟩
      · fin_cases i
        · exact hx'.1
        · rcases hy with rfl | rfl
          · exact hs.1 1
          · exact hs'.1 1
      · fin_cases i
        · show ¬ P.M 0 x y
          rcases hy with rfl | rfl
          · exact hs.not_M_right hM 0 hx'.1 hx'.2.1
          · exact hs'.not_M_right hM 0 hx'.1 hx'.2.2
        · show ¬ P.M 1 y (φ (x, y) (1 + 1))
          rw [hone]
          show ¬ P.M 1 y x
          rcases hy with rfl | rfl
          · exact hs.not_M_left hM 1 (by rw [hone]; exact hx'.1) (by rw [hone]; exact hx'.2.1)
          · exact hs'.not_M_left hM 1 (by rw [hone]; exact hx'.1) (by rw [hone]; exact hx'.2.2)
  -- the sum over the two blocks
  set a := w 0 (s 0) with ha
  set a' := w 0 (s' 0) with ha'
  set c := w 1 (s 1) with hc
  set c' := w 1 (s' 1) with hc'
  set S0 := ∑ x ∈ R 0, w 0 x with hS0
  set S1 := ∑ y ∈ R 1, w 1 y with hS1
  have hapos : 0 < a := hwpos 0 _ (hs.1 0)
  have ha'pos : 0 < a' := hwpos 0 _ (hs'.1 0)
  have hcpos : 0 < c := hwpos 1 _ (hs.1 1)
  have hc'pos : 0 < c' := hwpos 1 _ (hs'.1 1)
  have hS0pos : 0 ≤ S0 := Finset.sum_nonneg fun x hx => (hwpos 0 x (hRmem 0 x hx).1).le
  have hS1pos : 0 ≤ S1 := Finset.sum_nonneg fun x hx => (hwpos 1 x (hRmem 1 x hx).1).le
  have hZ : (a + a') * S1 + S0 * (c + c') ≤ P.Z univ b w := by
    rw [Cover.Z]
    refine le_trans (le_of_eq ?_) (Finset.sum_le_sum_of_subset_of_nonneg hsub fun f hf _ =>
      Finset.prod_nonneg fun i _ => (hwpos i _ (((P.mem_cols.mp hf).1 i).1 (mem_univ i))).le)
    rw [Finset.sum_image (fun x _ y _ h => hφinj h), Finset.sum_union hdisj]
    have e1 : ∑ xy ∈ T1, ∏ i, w i (φ xy i) = (a + a') * S1 := by
      simp only [T1, φ, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [Finset.sum_product, Finset.sum_pair (hne 0).symm]
      dsimp only
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      ring
    have e2 : ∑ xy ∈ T2, ∏ i, w i (φ xy i) = S0 * (c + c') := by
      simp only [T2, φ, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [Finset.sum_product, hS0, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_pair (hne 1).symm]
      ring
    rw [e1, e2]
  refine le_trans ?_ hZ
  -- the inequality
  have h0 := sq_sum_two (hRcard 0) (w 0)
  have h1 := sq_sum_two (hRcard 1) (w 1)
  have hp0 := hprod 0
  have hp1 := hprod 1
  rw [← ha, ← ha'] at hp0
  rw [← hc, ← hc'] at hp1
  rw [← hS0] at h0
  rw [← hS1] at h1
  set p0 := ∏ x ∈ R 0, w 0 x
  set p1 := ∏ x ∈ R 1, w 1 x
  -- `(a + a') * S0 ≥ 4` and `(c + c') * S1 ≥ 4`
  have hA : 4 ≤ (a + a') * S0 := by
    have hsq : 16 ≤ ((a + a') * S0) ^ 2 := by
      have h4 : 4 * (a * a') ≤ (a + a') ^ 2 := by nlinarith [sq_nonneg (a - a')]
      have : 16 * (a * a' * p0) ≤ (a + a') ^ 2 * S0 ^ 2 := by
        have hp0pos : 0 ≤ p0 := Finset.prod_nonneg fun x hx => (hwpos 0 x (hRmem 0 x hx).1).le
        nlinarith [mul_le_mul h4 h0 (by positivity) (by positivity)]
      rw [hp0] at this
      nlinarith
    nlinarith [mul_nonneg (add_pos hapos ha'pos).le hS0pos]
  have hC : 4 ≤ (c + c') * S1 := by
    have hsq : 16 ≤ ((c + c') * S1) ^ 2 := by
      have h4 : 4 * (c * c') ≤ (c + c') ^ 2 := by nlinarith [sq_nonneg (c - c')]
      have : 16 * (c * c' * p1) ≤ (c + c') ^ 2 * S1 ^ 2 := by
        have hp1pos : 0 ≤ p1 := Finset.prod_nonneg fun x hx => (hwpos 1 x (hRmem 1 x hx).1).le
        nlinarith [mul_le_mul h4 h1 (by positivity) (by positivity)]
      rw [hp1] at this
      nlinarith
    nlinarith [mul_nonneg (add_pos hcpos hc'pos).le hS1pos]
  set X := (a + a') * S1
  set Y := S0 * (c + c')
  have hX : 0 ≤ X := mul_nonneg (add_pos hapos ha'pos).le hS1pos
  have hY : 0 ≤ Y := mul_nonneg hS0pos (add_pos hcpos hc'pos).le
  have hXY : 16 ≤ X * Y := by
    have : X * Y = ((a + a') * S0) * ((c + c') * S1) := by simp only [X, Y]; ring
    rw [this]
    nlinarith
  nlinarith [sq_nonneg (X - Y)]

/-- **The capacity lemma on the digon with four colours.** -/
theorem cl_four_two : CL 4 2 := by
  refine Cover.capGE_of_maximal fun P hcard hM hno hmax b => ?_
  have hlam : lam 4 2 = 8 := by norm_num [lam]
  rw [hlam]
  rcases Cover.full_or_cutSection hcard hM hno hmax with hfull | ⟨c, e, hc⟩
  · have := P.capGE_full (le_refl 2) hcard hM hfull hno b
    rwa [hlam] at this
  · have hcard' := Cover.erase_card hcard hc.1
    have hM' := Cover.erase_isMatching hM c
    have hno' := Cover.erase_noClosedThread hno c
    have hmax' := Cover.maximal_erase hM hno hmax hc
    rcases Cover.full_or_cutSection hcard' hM' hno' hmax' with hfull' | ⟨c', e', hc'⟩
    · have h0 := (P.erase c).capGE_full (le_refl 2) hcard' hM' hfull' hno' c
      have hW := (witness_two (le_refl 4)).rotate e
      have hg : lam (4 - 1) 2 = (((4 : ℕ) : ℝ) - 2) ^ 2 - 1 := by norm_num [lam]
      rw [hg] at h0
      have := P.capGE_of_witness (le_of_lt (by norm_num : 3 < 4)) hcard hM hc
        (lam_pos (by norm_num) (by norm_num)) h0 hW b
      rwa [hlam] at this
    · exact digon_two_sections P hcard hM hc (Cover.isCutSection_of_erase hM hc hc')
        (fun i => (Finset.mem_erase.mp (hc'.1 i)).1) b

end Outerplanar
