/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.Chain

/-!
# The open-arm rule

A face whose first arm has a known chain matrix and whose second arm is only used through the
bound "at least as many colourings as walks in the triangle" (`dMat_le_chainM`).

Enumerate the two ends of the loaded edge by aligned enumerations and carry them outwards along
both arms (`Chain`). In these frames the profile of the face is at least
`genF B₁ El (dMat s) w`, where `B₁` is the transposed chain matrix of the first arm and `El` is
contained in the diagonal. The frames reached at the root are in general not the given ones: the
mismatch is a permutation `ρ`. `OpenOK ds s` says that for every `ρ`, after one more common
renumbering `τ`, the matrix `B₁` dominates a matrix `C` for which `GenOK C idPat (dMat s) noPat`
holds with the constant of the face. `faceOK_open` concludes `FaceOK`.
-/

namespace Outerplanar

open Finset

/-- The pattern of the diagonal. -/
def idPat : BMat := fun x y => decide (x = y)

/-- The empty pattern. -/
def noPat : BMat := fun _ _ => false

/-- The constant of a face with `m` interior vertices, as a natural number. -/
def faceN (m : ℕ) : ℕ := (2 ^ (m + 1) + 1) / 3

theorem faceN_add_two (m : ℕ) : faceN (m + 2) = faceN m + 2 ^ (m + 1) := by
  unfold faceN
  have e : 2 ^ (m + 2 + 1) + 1 = 2 ^ (m + 1) + 1 + 3 * 2 ^ (m + 1) := by
    rw [show m + 2 + 1 = (m + 1) + 2 from rfl, pow_add]
    ring
  rw [e, Nat.add_mul_div_left _ _ (by norm_num : 0 < 3)]

theorem faceN_cast : ∀ m : ℕ, ((faceN m : ℕ) : ℝ) = faceConst3 m
  | 0 => by norm_num [faceN, faceConst3]
  | 1 => by norm_num [faceN, faceConst3]
  | m + 2 => by
    rw [faceN_add_two, faceConst3_add_two, Nat.cast_add, faceN_cast m]
    push_cast
    ring

theorem IdxBallAt.weakenE {σ : Fin 3 → Fin 3} {E E' : BMat} {w : Fin 3 → Fin 3 → ℝ} {A : ℝ}
    (h : IdxBallAt σ E w A) (hE : ∀ c d, E' c d = false → E c d = false) : IdxBallAt σ E' w A :=
  fun j c d hcd => h j c d (hE c d hcd)

/-- The first arm with codes `ds` is fine against any second arm of length `s`. -/
def OpenOK (ds : List (Fin 3 → Bool)) (s : ℕ) : Prop :=
  ∀ ρ : Fin 3 → Fin 3, Function.Bijective ρ → ∃ τ : Fin 3 → Fin 3, Function.Bijective τ ∧
    ∃ C : Fin 3 → Fin 3 → ℕ, GenOK C idPat (dMat s) noPat (faceN (ds.length + s)) ∧
      ∀ a y, C a y ≤ chainM ds (τ y) (ρ (τ a))

/-- **The open-arm rule.** -/
theorem faceOK_open {S T : Finset ℕ} {U₁ U₂ : List (Finset ℕ)} (hS : S.card = 3)
    (hT : T.card = 3) (hU₂ : ∀ L ∈ U₂, L.card = 3) {ξ₀ α₀ : Fin 3 → ℕ}
    {ds₁ : List (Fin 3 → Bool)} (hξ₀ : Function.Injective ξ₀) (hξ₀m : ∀ i, ξ₀ i ∈ S)
    (hc₁ : Chain ξ₀ U₁ ds₁ α₀) (hopen : OpenOK ds₁ U₂.length) : FaceOK S U₁ T U₂ := by
  intro W hW A hA hin
  have hU₁ := hc₁.cards
  have hLu : (U₁.getLastD S).card = 3 := card_getLastD hS hU₁
  have hLv : (U₂.getLastD T).card = 3 := card_getLastD hT hU₂
  -- frames at the loaded edge and along the arms
  obtain ⟨η₀, hη₀, hη₀m, hal⟩ := exists_aligned hT hξ₀
  obtain ⟨ds₂, β₀, hc₂⟩ := exists_chain U₂ hU₂ η₀ hη₀
  have hα₀ := hc₁.injective hξ₀
  have hα₀m := hc₁.mem hξ₀m
  have hβ₀ := hc₂.injective hη₀
  have hβ₀m := hc₂.mem hη₀m
  refine inBall_of_idx hLu hLv fun α β hα hβ hαm hβm _ => ?_
  -- the mismatch of the frames at the root
  have hκex : ∀ y, ∃ b, β b = β₀ y := fun y => exists_idx hLv hβ hβm (hβ₀m y)
  choose κ₂ hκ₂ using hκex
  have hκinj : Function.Injective κ₂ := fun y y' e => hβ₀ (by rw [← hκ₂ y, ← hκ₂ y', e])
  have hρex : ∀ y, ∃ x, α₀ x = α (κ₂ y) := fun y => exists_idx hLu hα₀ hα₀m (hαm _)
  choose ρ hρ using hρex
  have hρinj : Function.Injective ρ := fun y y' e => hκinj (hα (by rw [← hρ y, ← hρ y', e]))
  obtain ⟨τ, hτ, C, hC, hle⟩ := hopen ρ ⟨hρinj, Finite.injective_iff_surjective.mp hρinj⟩
  have hginj : Function.Injective fun a => κ₂ (τ a) := hκinj.comp hτ.1
  refine ⟨fun a => κ₂ (τ a), ⟨hginj, Finite.injective_iff_surjective.mp hginj⟩, ?_⟩
  -- the loaded edge in index form
  have hξ : Function.Injective fun y => ξ₀ (τ y) := hξ₀.comp hτ.1
  have hη : Function.Injective fun t => η₀ (τ t) := hη₀.comp hτ.1
  have hidx := hin.idx hξ hη (fun y => hξ₀m _) (fun t => hη₀m _)
  have hEl : ∀ y t, decide (ξ₀ (τ y) = η₀ (τ t)) = true → idPat y t = true := fun y t e =>
    decide_eq_true (hτ.1 (hal (τ t) (τ y) (of_decide_eq_true e).symm))
  have hG : GenOK (fun a y => chainM ds₁ (τ y) (ρ (τ a)))
      (fun y t => decide (ξ₀ (τ y) = η₀ (τ t))) (dMat U₂.length) noPat
      (faceN (ds₁.length + U₂.length)) :=
    hC.mono hle (fun _ _ => le_rfl) hEl
  have hw0 : ∀ y t, 0 ≤ W (ξ₀ (τ y)) (η₀ (τ t)) := fun y t => hW _ _
  have key := (hG _ hw0 A hA hidx).weakenE
    (E' := fun a b => decide (α (κ₂ (τ a)) = β (κ₂ (τ b)))) fun _ _ _ => rfl
  rw [faceN_cast, hc₁.length] at key
  refine key.mono (genF_nonneg _ _ _ hw0) fun a b => ?_
  -- the profile of the face in these frames
  have e1 : α (κ₂ (τ a)) = α₀ (ρ (τ a)) := (hρ (τ a)).symm
  have e2 : β (κ₂ (τ b)) = β₀ (τ b) := hκ₂ (τ b)
  rw [e1, e2]
  unfold armF genF
  rw [sum_enum hS hξ (fun y => hξ₀m _)
    (fun s => ∑ t ∈ T, psum U₁ (nes U₁.length) s (α₀ (ρ (τ a))) * W s t
      * psum U₂ (nes U₂.length) t (β₀ (τ b)))]
  refine Finset.sum_le_sum fun y _ => ?_
  rw [sum_enum hT hη (fun t => hη₀m _)
    (fun t => psum U₁ (nes U₁.length) (ξ₀ (τ y)) (α₀ (ρ (τ a))) * W (ξ₀ (τ y)) t
      * psum U₂ (nes U₂.length) t (β₀ (τ b)))]
  refine Finset.sum_le_sum fun t _ => ?_
  have h1 := hc₁.count_ge (τ y) (ρ (τ a))
  have h2 : ((dMat U₂.length t b : ℕ) : ℝ)
      ≤ psum U₂ (nes U₂.length) (η₀ (τ t)) (β₀ (τ b)) := by
    have h3 := dMat_le_chainM ds₂ (τ t) (τ b)
    rw [hc₂.length, dMat_perm _ hτ.1] at h3
    exact (Nat.cast_le.mpr h3).trans (hc₂.count_ge (τ t) (τ b))
  have hp1 := psum_nonneg U₁ (nes U₁.length) (nes_nonneg _) (ξ₀ (τ y)) (α₀ (ρ (τ a)))
  have hp2 := psum_nonneg U₂ (nes U₂.length) (nes_nonneg _) (η₀ (τ t)) (β₀ (τ b))
  split_ifs
  · exact mul_nonneg (mul_nonneg hp1 (hW _ _)) hp2
  · exact mul_le_mul (mul_le_mul_of_nonneg_right h1 (hW _ _)) h2 (Nat.cast_nonneg _)
      (mul_nonneg hp1 (hW _ _))

end Outerplanar
