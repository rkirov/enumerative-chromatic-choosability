/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.Analytic

/-!
# The invariant: domination by a rank-one matrix

A piece rooted at an edge `uv` has a pair profile `W c d` (the weighted number of colourings
with `u ↦ c`, `v ↦ d`). The invariant carried by the induction is `HasPot (L u) (L v) W A`:
off the diagonal, `W` dominates `A` times a rank-one matrix whose two factors have product one
over the lists. By Egerváry's theorem this is the same as the bijection invariant (B) of the
proof draft (`ai_research_notes/OUTERPLANAR_PROOF_DRAFT_2026-11-09.md`, sections 1 and 2).
-/

namespace Outerplanar

open Finset

/-- `W` dominates `A · a ⊗ b` on the pairs `c ≠ d` of `S × T`, with `∏ a = ∏ b = 1`. -/
def HasPot (S T : Finset ℕ) (W : ℕ → ℕ → ℝ) (A : ℝ) : Prop :=
  ∃ a b : ℕ → ℝ, (∀ c ∈ S, 0 < a c) ∧ (∀ d ∈ T, 0 < b d) ∧
    ∏ c ∈ S, a c = 1 ∧ ∏ d ∈ T, b d = 1 ∧ ∀ c ∈ S, ∀ d ∈ T, c ≠ d → A * (a c * b d) ≤ W c d

theorem HasPot.swap {S T : Finset ℕ} {W : ℕ → ℕ → ℝ} {A : ℝ} (h : HasPot S T W A) :
    HasPot T S (fun d c => W c d) A := by
  obtain ⟨a, b, ha, hb, hpa, hpb, hW⟩ := h
  exact ⟨b, a, hb, ha, hpb, hpa, fun d hd c hc hdc => by
    rw [mul_comm (b d)]; exact hW c hc d hd (Ne.symm hdc)⟩

theorem HasPot.mul {S T : Finset ℕ} {W W' : ℕ → ℕ → ℝ} {A A' : ℝ} (hA : 0 ≤ A) (hA' : 0 ≤ A')
    (h : HasPot S T W A) (h' : HasPot S T W' A') :
    HasPot S T (fun c d => W c d * W' c d) (A * A') := by
  obtain ⟨a, b, ha, hb, hpa, hpb, hW⟩ := h
  obtain ⟨a', b', ha', hb', hpa', hpb', hW'⟩ := h'
  refine ⟨fun c => a c * a' c, fun d => b d * b' d, fun c hc => mul_pos (ha c hc) (ha' c hc),
    fun d hd => mul_pos (hb d hd) (hb' d hd), by rw [Finset.prod_mul_distrib, hpa, hpa', one_mul],
    by rw [Finset.prod_mul_distrib, hpb, hpb', one_mul], fun c hc d hd hcd => ?_⟩
  have h1 := hW c hc d hd hcd
  have h2 := hW' c hc d hd hcd
  have p1 : 0 ≤ A * (a c * b d) := mul_nonneg hA (mul_pos (ha c hc) (hb d hd)).le
  have p2 : 0 ≤ A' * (a' c * b' d) := mul_nonneg hA' (mul_pos (ha' c hc) (hb' d hd)).le
  calc A * A' * (a c * a' c * (b d * b' d)) = (A * (a c * b d)) * (A' * (a' c * b' d)) := by ring
    _ ≤ W c d * W' c d := mul_le_mul h1 h2 p2 (p1.trans h1)

/-- The constraint of an ordinary edge. -/
theorem hasPot_ne (S T : Finset ℕ) : HasPot S T (fun c d => if c ≠ d then 1 else 0) 1 :=
  ⟨fun _ => 1, fun _ => 1, fun _ _ => one_pos, fun _ _ => one_pos, by simp, by simp,
    fun c _ d _ hcd => by simp [hcd]⟩

theorem HasPot.mono {S T : Finset ℕ} {W W' : ℕ → ℕ → ℝ} {A : ℝ} (h : HasPot S T W A)
    (hle : ∀ c ∈ S, ∀ d ∈ T, c ≠ d → W c d ≤ W' c d) : HasPot S T W' A := by
  obtain ⟨a, b, ha, hb, hpa, hpb, hW⟩ := h
  exact ⟨a, b, ha, hb, hpa, hpb, fun c hc d hd hcd => (hW c hc d hd hcd).trans (hle c hc d hd hcd)⟩

open Classical in
/-- **Root dominance**: a piece hanging at one vertex acts as a vertex weight whose geometric
mean is at least `(k - 1) A` times that of the weights at the far end. -/
theorem HasPot.gmean_le {k : ℕ} (hk : 2 ≤ k) {S T : Finset ℕ} (hS : S.card = k)
    (hT : T.card = k) {W : ℕ → ℕ → ℝ} {A : ℝ} (hA : 0 < A) (h : HasPot S T W A)
    (hW0 : ∀ c d, 0 ≤ W c d) {ω : ℕ → ℝ} (hω : ∀ d ∈ T, 0 < ω d) :
    ((k : ℝ) - 1) * A * gmean T ω ≤ gmean S fun c => ∑ d ∈ T, W c d * ω d := by
  obtain ⟨a, b, ha, hb, hpa, hpb, hW⟩ := h
  have hθ : ∀ d ∈ T, 0 < b d * ω d := fun d hd => mul_pos (hb d hd) (hω d hd)
  have hpend := pendant_gmean hk S T hS hT (fun c d => c = d) (fun x _ c _ c' _ h h' => h ▸ h')
    (fun x _ x' _ c _ h h' => h.trans h'.symm) (fun d => b d * ω d) hθ
  rw [gmean_mul hb hω, gmean_eq_one hb hpb, one_mul] at hpend
  have hspos : ∀ c ∈ S, 0 < ∑ d ∈ T with ¬ c = d, b d * ω d := fun c _ =>
    pendant_pos hk T hT (fun d => c = d) (fun d _ d' _ h h' => h ▸ h') _ hθ
  have hlow : ∀ c ∈ S, A * a c * ∑ d ∈ T with ¬ c = d, b d * ω d ≤ ∑ d ∈ T, W c d * ω d := by
    intro c hc
    rw [Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum fun d hd => ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ T) fun d hd _ =>
        mul_nonneg (hW0 c d) (hω d hd).le)
    obtain ⟨hdT, hcd⟩ := Finset.mem_filter.mp hd
    calc A * a c * (b d * ω d) = A * (a c * b d) * ω d := by ring
      _ ≤ W c d * ω d := mul_le_mul_of_nonneg_right (hW c hc d hdT hcd) (hω d hdT).le
  have hAa : ∀ c ∈ S, 0 < A * a c := fun c hc => mul_pos hA (ha c hc)
  have h1 : gmean S (fun c => A * a c * ∑ d ∈ T with ¬ c = d, b d * ω d)
      ≤ gmean S fun c => ∑ d ∈ T, W c d * ω d :=
    gmean_mono (fun c hc => mul_pos (hAa c hc) (hspos c hc)) hlow
  have hSne : S.Nonempty := by rw [← Finset.card_pos]; omega
  have hgA : gmean S (fun c => A * a c) = A := by
    have hc : (S.card : ℝ) ≠ 0 := by exact_mod_cast hSne.card_ne_zero
    have : gmean S (fun c => A * a c) = gmean S (fun _ => A) * gmean S a :=
      gmean_mul (fun _ _ => hA) ha
    rw [this, gmean_eq_one ha hpa, mul_one, gmean]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul, Real.exp_log hA]
  rw [gmean_mul hAa hspos, hgA] at h1
  refine le_trans ?_ h1
  calc ((k : ℝ) - 1) * A * gmean T ω = A * (((k : ℝ) - 1) * gmean T ω) := by ring
    _ ≤ A * gmean S fun c => ∑ d ∈ T with ¬ c = d, b d * ω d := by
        have := mul_le_mul_of_nonneg_left hpend hA.le
        convert this using 6

end Outerplanar
