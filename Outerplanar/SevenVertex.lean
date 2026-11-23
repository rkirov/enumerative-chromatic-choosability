/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.Lift
import Outerplanar.TagBuiltV

/-!
# Cut vertices in the seven-even-face tag system

The vertex rule `VCond t t₀ t₁` of the tags `STag` (`Outerplanar/SevenEven.lean`): a demand `t`
on an edge `vy` is met by a demand `t₀` on `vy` and a demand `t₁` on a pendant edge `vw` if

* one of the two is plain and `t` is the other one, or
* `t` asks only for what a product gives: the rank-one bound if `t₀` has it (the lifted side
  always has it, `lift_hasPot`), the product of the four-cell constants and of the floors, the
  ball class if both sides are ball sides, and neither the hull nor the gain class.

`vcond_sound` proves it from the lift lemmas of `Outerplanar/Lift.lean` and the product lemmas of
the classes. **`ecc_three_of_sevenBuiltV`**: graphs built by ears and pendant edges under these
rules are 3-ECC.

Part of the formalization of the seven-even-face theorem with cut vertices (research note
`ai_research_notes/OUTERPLANAR_SEVEN_AND_CUTS_2026-11-23.md`, another AI session of this
repository's collaboration); formalized by Claude.
-/

namespace Outerplanar

open Finset

variable {S T : Finset ℕ} {W W' : ℕ → ℕ → ℝ} {A : ℝ}

theorem scls_mono {t : STag} (h : scls t S T W A) (h0 : ∀ c d, 0 ≤ W c d)
    (hle : ∀ c ∈ S, ∀ d ∈ T, c ≠ d → W c d ≤ W' c d) : scls t S T W' A := by
  obtain ⟨⟨hx, hp, htb, hfl, hh⟩, hb, hg⟩ := h
  refine ⟨⟨hx.mono h0 hle, fun e => (hp e).mono hle, htb.mono h0 hle,
    fun c hc d hd hcd => (hfl c hc d hd hcd).trans (hle c hc d hd hcd), fun e => (hh e).mono hle⟩,
    fun e => (hb e).mono h0 hle, fun e => ?_⟩
  obtain ⟨τ, Z, h1, h2, h3, h4⟩ := hg e
  exact ⟨τ, Z, h1, h2, h3, fun c hc d hd hcd => (h4 c hc d hd hcd).trans (hle c hc d hd hcd)⟩

theorem scls_of_lift {t : STag} (h : scls t.lift S T W A) : scls t S T W A :=
  ⟨⟨h.1.1, fun _ => h.1.2.1 rfl, h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2⟩, h.2.1, h.2.2⟩

theorem STag.isBall_lift {t : STag} (h : t.isBall) : t.lift.isBall := by
  rcases h with h | rfl
  · exact Or.inl h
  · exact Or.inr rfl

/-- The vertex rule. -/
def VCond (t t₀ t₁ : STag) : Prop :=
  (t₁ = STag.plain ∧ t = t₀) ∨ (t₀ = STag.plain ∧ t = t₁) ∨
  ((t.base.mb = true → t₀.base.mb = true) ∧ t.base.tv ≤ t₀.base.tv * t₁.base.tv ∧
    t.base.fl ≤ t₀.base.fl * t₁.base.fl ∧ t.base.hull = false ∧
    (t.ball = true → t₀.isBall ∧ t₁.isBall) ∧ t.gain = false)

/-- The branch at `v` dominates `A₂` times the lift. -/
theorem branch_ge {Lv Lw : Finset ℕ} {X X' : ℕ → ℕ → ℝ} {A₂ : ℝ} (hX : ∀ c d, 0 ≤ X c d)
    (hX' : ∀ c d, 0 ≤ X' c d) (hD : Dominant Lw Lv X' A₂) {c : ℕ} (hc : c ∈ Lv) :
    A₂ * liftV Lw X c ≤ ∑ e ∈ Lw, X c e * X' e c := by
  unfold liftV
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun e he => ?_
  split_ifs with hce
  · rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (hD e he c hc (Ne.symm hce)) (hX _ _)
  · rw [mul_zero]
    exact mul_nonneg (hX _ _) (hX' _ _)

/-- **The vertex rule is sound.** -/
theorem vcond_sound {t t₀ t₁ : STag} (hcond : VCond t t₀ t₁) : sevenSys.VertexSound t t₀ t₁ := by
  intro Lv Ly Lw hv hy hw W X X' hW hX hX' A A₁ A₂ hA hA₁ hA₂ h₀ h₁ h₂
  change scls t₀ Lv Ly W A at h₀
  change scls t₁ Lv Lw X A₁ at h₁
  change scls t Lv Ly (fun c d => W c d * ∑ e ∈ Lw, X c e * X' e c) (A * (2 * A₁ * A₂))
  have hX'D : Dominant Lw Lv X' A₂ := scls_plain_dom h₂
  set F : ℕ → ℝ := fun c => ∑ e ∈ Lw, X c e * X' e c with hF
  have hF0 : ∀ c, 0 ≤ F c := fun c => Finset.sum_nonneg fun e _ =>
    mul_nonneg (hX _ _) (hX' _ _)
  set K := A₂ * (2 * A₁) with hK
  have hKpos : 0 < K := by positivity
  have hconst : A * (2 * A₁ * A₂) = A * K := by rw [hK]; ring
  rw [hconst]
  -- the branch table
  have hL := scls_lift (U := Ly) hv hw hy hX hA₁ h₁
  have hL' : scls t₁.lift Lv Ly (fun c _ => A₂ * liftV Lw X c) (A₂ * (2 * A₁)) :=
    sevenSys.mul_dom t₁.lift Lv Ly (fun c _ => liftV Lw X c) (fun _ _ => A₂) (2 * A₁) A₂
      (by positivity) hA₂.le (fun c _ => liftV_nonneg hX c) (fun _ _ => hA₂.le)
      (fun _ _ _ _ _ => le_refl _) hL
  have hB : scls t₁.lift Lv Ly (fun c _ => F c) K :=
    scls_mono hL' (fun c _ => mul_nonneg hA₂.le (liftV_nonneg hX c))
      fun c hc _ _ _ => branch_ge hX hX' hX'D hc
  rcases hcond with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hmb, htv, hfl, hhull, hball, hgain⟩
  · -- the branch is greedy
    have hXD : Dominant Lv Lw X A₁ := scls_plain_dom h₁
    have hFD : Dominant Lv Ly (fun c _ => F c) K := fun c hc d hd hcd => by
      have h1 := lift_dom (U := Ly) hA₁.le hw hXD c hc d hd hcd
      have h2 := branch_ge hX hX' hX'D hc
      simp only at h1 ⊢
      rw [hK]
      nlinarith
    have := sevenSys.mul_dom t Lv Ly W (fun c _ => F c) A K hA.le hKpos.le hW
      (fun c _ => hF0 c) hFD h₀
    have e : A * K = K * A := mul_comm _ _
    rw [e]
    refine (show scls t Lv Ly (fun c d => F c * W c d) (K * A) from this) |>
      fun h => scls_mono h (fun c d => mul_nonneg (hF0 c) (hW c d)) fun c _ d _ _ =>
        le_of_eq (mul_comm _ _)
  · -- the edge is greedy
    have hWD : Dominant Lv Ly W A := scls_plain_dom h₀
    exact sevenSys.mul_dom t Lv Ly (fun c _ => F c) W K A hKpos.le hA.le (fun c _ => hF0 c) hW
      hWD (scls_of_lift hB)
  · -- a product
    refine ⟨⟨Hex.mul hA.le hKpos.le h₀.1.1 hB.1.1, fun hm => HasPot.mul hA.le hKpos.le
      (h₀.1.2.1 (hmb hm)) (hB.1.2.1 rfl), (h₀.1.2.2.1.mul hB.1.2.2.1).anti t.base.tv0 htv, ?_,
      fun h => ?_⟩, fun hb => InBall.mul hA.le hKpos.le (scls_ball hA.le (hball hb).1 h₀)
        (scls_ball hKpos.le (STag.isBall_lift (hball hb).2) hB), fun h => ?_⟩
    · have hd := Dominant.mul (mul_nonneg t₀.base.fl0 hA.le) (mul_nonneg t₁.base.fl0 hKpos.le)
        h₀.1.2.2.2.1 hB.1.2.2.2.1
      refine hd.le ?_
      have : t.base.fl * (A * K) ≤ t₀.base.fl * t₁.base.fl * (A * K) :=
        mul_le_mul_of_nonneg_right hfl (by positivity)
      show t.base.fl * (A * K) ≤ t₀.base.fl * A * (t₁.base.fl * K)
      linarith
    · rw [hhull] at h; exact absurd h (by decide)
    · rw [hgain] at h; exact absurd h (by decide)

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Every graph built by ears and pendant edges under the seven-even-face rules is 3-ECC.** -/
theorem ecc_three_of_sevenBuiltV {tg : V → V → STag}
    (h : TagBuiltV G sevenSys sevenRule (fun _ _ => True) VCond univ tg) : G.ECCAt 3 :=
  ecc_three_of_tagBuiltV G (fun _ _ _ hr => sevenRule_sound hr) (fun t₁ t₂ _ => seven_glue t₁ t₂)
    (fun _ _ _ hr => vcond_sound hr) h

end Outerplanar
