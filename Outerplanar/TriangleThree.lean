/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.Cover

/-!
# The triangle with three cut threads, three colours

This is the case `k = 3`, `n = 3`, three cut threads, of Step 5 of
`ai_research_notes/OUTERPLANAR_PROOF_DRAFT_2026-11-09.md` (a result of this repository's 2026-11
AI research collaboration).

A 3-fold cover of the triangle whose fibres split into three sections `c 0`, `c 1`, `c 2`, the
section `c a` being matched along every edge except `a → a + 1`, has capacity at least
`9 = lam 3 3`.

A word `s : Fin 3 → Fin 3` names the colouring `i ↦ c (s i) i`; it is a colouring of the cover
as soon as `s i = s (i + 1)` only for `s i = i`. Ten of the twelve such words carry a law with
all marginals `1 / 3`: the word `1 2 0` has weight `3 / 12` and nine others weight `1 / 12`. The
Gibbs inequality then bounds the weighted number of colourings from below by
`4 ^ (3 / 12) * 12 ^ (9 / 12)`, which is at least `9` because `4 ^ 3 * 12 ^ 9 ≥ 9 ^ 12`.

* `Cover.capGE_three_sections` — the capacity bound.
-/

namespace Outerplanar

open Finset

/-- The ten words that carry the law. -/
def triWord : ℕ → Fin 3 → Fin 3
  | 0 => ![1, 2, 0]
  | 1 => ![0, 2, 1]
  | 2 => ![1, 0, 2]
  | 3 => ![2, 1, 0]
  | 4 => ![0, 0, 1]
  | 5 => ![0, 0, 2]
  | 6 => ![0, 1, 1]
  | 7 => ![2, 1, 1]
  | 8 => ![2, 0, 2]
  | _ => ![2, 1, 2]

theorem triWord_adm : ∀ j < 10, ∀ i : Fin 3, triWord j i = triWord j (i + 1) → triWord j i = i := by
  decide

theorem triWord_inj : ∀ j < 10, ∀ j' < 10, triWord j = triWord j' → j = j' := by
  decide

/-- `4 ^ 3 * 12 ^ 9 ≥ 9 ^ 12`, in logarithms. -/
theorem tri_log_num : 12 * Real.log 9 ≤ 3 * Real.log 4 + 9 * Real.log 12 := by
  have h : Real.log ((9 : ℝ) ^ 12) ≤ Real.log ((4 : ℝ) ^ 3 * (12 : ℝ) ^ 9) :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow, Real.log_pow] at h
  push_cast at h
  linarith

/-- A 3-fold cover of the triangle that splits into three sections, the section `c a` being cut
at the edge `a → a + 1`, has capacity at least `9 = lam 3 3`. -/
theorem Cover.capGE_three_sections (P : Cover 3) (hcard : ∀ i, (P.F i).card = 3)
    (hM : P.IsMatching) (c : Fin 3 → Fin 3 → ℕ) (hc : ∀ a, P.IsCutSection (c a) a)
    (hdist : ∀ a a' i, a ≠ a' → c a i ≠ c a' i) (b : Fin 3 → ℕ) :
    P.CapGE Finset.univ b (lam 3 3) := by
  intro w hw
  have hwpos : ∀ i, ∀ x ∈ P.F i, 0 < w i x := fun i => (hw i (mem_univ i)).1
  have hmem : ∀ a i, c a i ∈ P.F i := fun a i => (hc a).1 i
  have hinj : ∀ i, Function.Injective fun a => c a i := fun i a a' h => by
    by_contra hne
    exact hdist a a' i hne h
  -- the fibres
  have hF : ∀ i, P.F i = univ.image fun a => c a i := fun i => by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
      exact hmem a i
    · rw [Finset.card_image_of_injective _ (hinj i), hcard]
      simp
  have hprod : ∀ i, w i (c 0 i) * w i (c 1 i) * w i (c 2 i) = 1 := fun i => by
    have h := (hw i (mem_univ i)).2
    rw [hF i, Finset.prod_image fun a _ a' _ h => hinj i h, Fin.prod_univ_three] at h
    exact h
  set L : Fin 3 → Fin 3 → ℝ := fun a i => Real.log (w i (c a i)) with hLdef
  have hwc : ∀ a i, 0 < w i (c a i) := fun a i => hwpos i _ (hmem a i)
  have hL : ∀ i, L 0 i + L 1 i + L 2 i = 0 := fun i => by
    have h := congrArg Real.log (hprod i)
    rw [Real.log_mul (mul_pos (hwc 0 i) (hwc 1 i)).ne' (hwc 2 i).ne',
      Real.log_mul (hwc 0 i).ne' (hwc 1 i).ne', Real.log_one] at h
    exact h
  -- admissible words are colourings
  have key : ∀ a a' i, (a = a' → a = i) → ¬ P.M i (c a i) (c a' (i + 1)) := by
    intro a a' i h hMx
    by_cases hai : a = i
    · subst hai
      exact (hc a).2.2.1 _ (hmem a' _) hMx
    · have h2 := (hc a).2.1 i (Ne.symm hai)
      have h3 := (hM i).1 _ (hmem a i) _ (hmem a' _) _ (hmem a _) hMx h2
      by_cases haa : a = a'
      · exact hai (h haa)
      · exact hdist a a' (i + 1) haa h3.symm
  let f : (Fin 3 → Fin 3) → Fin 3 → ℕ := fun s i => c (s i) i
  have hcol : ∀ s : Fin 3 → Fin 3, (∀ i, s i = s (i + 1) → s i = i) → f s ∈ P.cols univ b := by
    intro s hs
    rw [P.mem_cols]
    exact ⟨fun i => ⟨fun _ => hmem _ i, fun h => absurd (mem_univ i) h⟩,
      fun i _ _ => key _ _ i (hs i)⟩
  have hfinj : Function.Injective f := fun s s' h => by
    funext i
    by_contra hne
    exact hdist _ _ i hne (congrFun h i)
  -- the weights of the ten words
  let T : ℕ → ℝ := fun j => ∏ i, w i (c (triWord j i) i)
  have hTpos : ∀ j, 0 < T j := fun j => Finset.prod_pos fun i _ => hwc _ i
  have hsumT : ∑ j ∈ range 10, T j ≤ P.Z univ b w := by
    have h1 : ∑ j ∈ range 10, T j
        = ∑ g ∈ (range 10).image (fun j => f (triWord j)), ∏ i, w i (g i) := by
      rw [Finset.sum_image]
      intro j hj j' hj' h
      exact triWord_inj j (Finset.mem_range.mp hj) j' (Finset.mem_range.mp hj') (hfinj h)
    rw [h1, Cover.Z]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun g hg _ =>
      Finset.prod_nonneg fun i _ => (hwpos i _ (((P.mem_cols.mp hg).1 i).1 (mem_univ i))).le
    intro g hg
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hg
    exact hcol _ (triWord_adm j (Finset.mem_range.mp hj))
  have hZpos : 0 < P.Z univ b w :=
    lt_of_lt_of_le (Finset.sum_pos (fun j _ => hTpos j) (by simp)) hsumT
  -- the law
  let p : ℕ → ℝ := fun j => if j = 0 then 3 / 12 else 1 / 12
  have hp0 : ∀ j, 0 < p j := fun j => by
    simp only [p]
    split_ifs <;> norm_num
  have hpsum : ∑ j ∈ range 10, p j = 1 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, p]
    norm_num
  have hg := gibbs (range 10) p T (fun j _ => (hp0 j).le) hpsum (fun j _ _ => hTpos j)
    (fun j _ => (hTpos j).le)
  have hterm : ∀ (j : ℕ) (q lq : ℝ) (a0 a1 a2 : Fin 3), p j = q → 0 < q → -Real.log q = lq →
      triWord j = ![a0, a1, a2] →
      p j * Real.log (T j / p j) = q * (L a0 0 + L a1 1 + L a2 2 + lq) := by
    intro j q lq a0 a1 a2 hq hqpos hlq hword
    have hTj : T j = w 0 (c a0 0) * w 1 (c a1 1) * w 2 (c a2 2) := by
      simp only [T, Fin.prod_univ_three, hword]
      rfl
    rw [hq, Real.log_div (hTpos j).ne' hqpos.ne', hTj,
      Real.log_mul (mul_pos (hwc a0 0) (hwc a1 1)).ne' (hwc a2 2).ne',
      Real.log_mul (hwc a0 0).ne' (hwc a1 1).ne', ← hlq]
    ring
  have hl4 : -Real.log (3 / 12 : ℝ) = Real.log 4 := by
    rw [show (3 / 12 : ℝ) = 4⁻¹ by norm_num, Real.log_inv, neg_neg]
  have hl12 : -Real.log (1 / 12 : ℝ) = Real.log 12 := by
    rw [show (1 / 12 : ℝ) = 12⁻¹ by norm_num, Real.log_inv, neg_neg]
  have hq : ∀ j : ℕ, j ≠ 0 → p j = 1 / 12 := fun j hj => by simp [p, hj]
  have e0 := hterm 0 _ _ 1 2 0 (by simp [p]) (by norm_num) hl4 rfl
  have e1 := hterm 1 _ _ 0 2 1 (hq 1 (by norm_num)) (by norm_num) hl12 rfl
  have e2 := hterm 2 _ _ 1 0 2 (hq 2 (by norm_num)) (by norm_num) hl12 rfl
  have e3 := hterm 3 _ _ 2 1 0 (hq 3 (by norm_num)) (by norm_num) hl12 rfl
  have e4 := hterm 4 _ _ 0 0 1 (hq 4 (by norm_num)) (by norm_num) hl12 rfl
  have e5 := hterm 5 _ _ 0 0 2 (hq 5 (by norm_num)) (by norm_num) hl12 rfl
  have e6 := hterm 6 _ _ 0 1 1 (hq 6 (by norm_num)) (by norm_num) hl12 rfl
  have e7 := hterm 7 _ _ 2 1 1 (hq 7 (by norm_num)) (by norm_num) hl12 rfl
  have e8 := hterm 8 _ _ 2 0 2 (hq 8 (by norm_num)) (by norm_num) hl12 rfl
  have e9 := hterm 9 _ _ 2 1 2 (hq 9 (by norm_num)) (by norm_num) hl12 rfl
  simp only [Finset.sum_range_succ (fun j => p j * Real.log (T j / p j)), Finset.sum_range_zero,
    zero_add, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9] at hg
  have hnum := tri_log_num
  have h0 := hL 0
  have h1 := hL 1
  have h2 := hL 2
  have hlogT : Real.log (∑ j ∈ range 10, T j) ≤ Real.log (P.Z univ b w) :=
    Real.log_le_log (Finset.sum_pos (fun j _ => hTpos j) (by simp)) hsumT
  have hfin : Real.log 9 ≤ Real.log (P.Z univ b w) := by linarith
  have hlam : lam 3 3 = 9 := by
    unfold lam
    norm_num
  rw [hlam]
  exact (Real.log_le_log_iff (by norm_num) hZpos).mp hfin

end Outerplanar
