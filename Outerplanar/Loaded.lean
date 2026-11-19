/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.Ball

/-!
# A face with one loaded edge, in index form

Enumerate the lists at the two ends of an edge by `Fin 3`. A pair profile becomes a table
`w : Fin 3 → Fin 3 → ℝ`, and what is left of the lists is the *pattern* `E : BMat` of equal
colours. This file restates the ball class (`InBall`, `Outerplanar/Ball.lean`) for such tables
and sets up the statement that is proved face by face from certificates.

* `IdxBallAt σ E w A` — the ball inequalities for the matching `σ` of the two lists (good pairs
  `(a, σ b)`, `a ≠ b`), weight being moved to any pair outside `E`;
* `IdxBall E w A` — the same for every matching that extends `E`;
* `InBall.idx`, `inBall_of_idx` — the two translations between lists and indices;
* `genF B₁ El B₂ w` — the profile of a face with one loaded edge: `B₁` and `B₂` count the proper
  colourings of the two arcs of ordinary edges between the root and the loaded edge;
* `GenOK B₁ El B₂ Er α` — such a face maps the ball class to the ball class, with the constant
  multiplied by `α`. `GenOK.mono`: fewer colourings of the arcs and more equal colours on the
  loaded edge make the statement stronger.

This is part of the formalization of the ball invariant, a result of this repository's 2026-11
AI research collaboration.
-/

namespace Outerplanar

open Finset

/-- A pattern of equal colours between two enumerated lists of three colours. -/
abbrev BMat := Fin 3 → Fin 3 → Bool

/-- The `k`-th good pair of the matching `σ`: the index pairs `(a, σ b)` with `a ≠ b`. -/
def gp (σ : Fin 3 → Fin 3) (k : Fin 6) : Fin 3 × Fin 3 := ((offPair k).1, σ (offPair k).2)

/-- The ball inequalities for the matching `σ`, for a profile indexed by enumerations of the two
lists. The pairs of the pattern `E` do not receive weight. -/
def IdxBallAt (σ : Fin 3 → Fin 3) (E : BMat) (w : Fin 3 → Fin 3 → ℝ) (A : ℝ) : Prop :=
  ∀ j : Fin 6, ∀ c d : Fin 3, E c d = false →
    A ^ 600 ≤ (∏ k ∈ univ.erase j, w (gp σ k).1 (gp σ k).2) ^ 100
      * w (gp σ j).1 (gp σ j).2 ^ 91 * w c d ^ 9

/-- `σ` is a matching of the two lists that extends the pattern `E`. -/
def Compat (σ : Fin 3 → Fin 3) (E : BMat) : Prop :=
  Function.Injective σ ∧ ∀ c d, E c d = true → σ c = d

/-- The ball class in index form: the ball inequalities for every matching extending `E`. -/
def IdxBall (E : BMat) (w : Fin 3 → Fin 3 → ℝ) (A : ℝ) : Prop :=
  ∀ σ, Compat σ E → IdxBallAt σ E w A

theorem IdxBallAt.mono {σ : Fin 3 → Fin 3} {E : BMat} {w w' : Fin 3 → Fin 3 → ℝ} {A : ℝ}
    (h : IdxBallAt σ E w A) (h0 : ∀ c d, 0 ≤ w c d) (hle : ∀ c d, w c d ≤ w' c d) :
    IdxBallAt σ E w' A := fun j c d hcd =>
  (h j c d hcd).trans (ball_mul_le (prod_nonneg fun _ _ => h0 _ _) (h0 _ _) (h0 _ _)
    (prod_le_prod₀ (fun _ _ => h0 _ _) fun _ _ => hle _ _) (hle _ _) (hle _ _))

/-! ### Between lists and indices -/

/-- A profile in the ball class, read through enumerations of the two lists. -/
theorem InBall.idx {S T : Finset ℕ} {W : ℕ → ℕ → ℝ} {A : ℝ} (h : InBall S T W A)
    {ζ ξ : Fin 3 → ℕ} (hζ : Function.Injective ζ) (hξ : Function.Injective ξ)
    (hζm : ∀ a, ζ a ∈ S) (hξm : ∀ b, ξ b ∈ T) :
    IdxBall (fun c d => decide (ζ c = ξ d)) (fun c d => W (ζ c) (ξ d)) A := by
  rintro σ ⟨hσ, hc⟩ j c d hcd
  have hm : Matched S T (fun k => ζ (offPair k).1) (fun k => ξ (σ (offPair k).2)) :=
    ⟨ζ, ξ ∘ σ, hζ, hξ.comp hσ, hζm, fun b => hξm _, fun a b hab => by
      obtain ⟨i, hi⟩ := offPair_surj a b hab
      exact ⟨i, by show ζ (offPair i).1 = ζ a; rw [hi],
        by show ξ (σ (offPair i).2) = ξ (σ b); rw [hi]⟩⟩
  have hne : ∀ i, ζ (offPair i).1 ≠ ξ (σ (offPair i).2) := fun i e =>
    offPair_ne i (hσ (hc _ _ (decide_eq_true e)))
  exact h _ _ hm hne j (ζ c) (hζm c) (ξ d) (hξm d) (of_decide_eq_false hcd)

/-- The ball class at a root edge from its index form. For every pair of enumerations in which
a common colour has the same index, the index form may be proved after renumbering both
enumerations by one bijection `π`. -/
theorem inBall_of_idx {Lu Lv : Finset ℕ} (hu : Lu.card = 3) (hv : Lv.card = 3)
    {F : ℕ → ℕ → ℝ} {A : ℝ}
    (h : ∀ α β : Fin 3 → ℕ, Function.Injective α → Function.Injective β → (∀ a, α a ∈ Lu) →
      (∀ b, β b ∈ Lv) → (∀ a b, α a = β b → a = b) →
      ∃ π : Fin 3 → Fin 3, Function.Bijective π ∧
        IdxBallAt id (fun a b => decide (α (π a) = β (π b)))
          (fun a b => F (α (π a)) (β (π b))) A) :
    InBall Lu Lv F A := by
  intro p q hm hpq j c hc d hd hcd
  obtain ⟨α₀, β₀, hα₀, hβ₀, hαm₀, hβm₀, hab₀⟩ := hm
  have hal₀ : ∀ a b, α₀ a = β₀ b → a = b := by
    intro a b e
    by_contra hne
    obtain ⟨i, hi1, hi2⟩ := hab₀ a b hne
    exact hpq i (by rw [hi1, hi2, e])
  obtain ⟨π, hπ, key⟩ := h α₀ β₀ hα₀ hβ₀ hαm₀ hβm₀ hal₀
  -- renumbered enumerations
  set α : Fin 3 → ℕ := fun a => α₀ (π a) with hαdef
  set β : Fin 3 → ℕ := fun b => β₀ (π b) with hβdef
  have hα : Function.Injective α := hα₀.comp hπ.1
  have hβ : Function.Injective β := hβ₀.comp hπ.1
  have hαm : ∀ a, α a ∈ Lu := fun a => hαm₀ _
  have hβm : ∀ b, β b ∈ Lv := fun b => hβm₀ _
  have hab : ∀ a b, a ≠ b → ∃ i, p i = α a ∧ q i = β b := fun a b hne =>
    hab₀ _ _ fun e => hne (hπ.1 e)
  obtain ⟨κ, hκb, hκ⟩ := matched_reindex hα hβ hab
  obtain ⟨j', rfl⟩ := hκb.2 j
  obtain ⟨a, rfl⟩ : ∃ a, α a = c := by
    rw [← image_enum hu hα hαm] at hc
    obtain ⟨a, -, ha⟩ := mem_image.mp hc
    exact ⟨a, ha⟩
  obtain ⟨b, rfl⟩ : ∃ b, β b = d := by
    rw [← image_enum hv hβ hβm] at hd
    obtain ⟨b, -, hb⟩ := mem_image.mp hd
    exact ⟨b, hb⟩
  have key' := key j' a b (decide_eq_false hcd)
  have e1 : ∏ k ∈ univ.erase (κ j'), F (p k) (q k)
      = ∏ k ∈ univ.erase j', F (α (offPair k).1) (β (offPair k).2) := by
    symm
    refine Finset.prod_bij (fun k _ => κ k) (fun k hk => ?_) (fun k _ k' _ e => hκb.1 e)
      (fun k hk => ?_) (fun k _ => by rw [(hκ k).1, (hκ k).2])
    · exact mem_erase.mpr ⟨fun e => (mem_erase.mp hk).1 (hκb.1 e), mem_univ _⟩
    · obtain ⟨k', rfl⟩ := hκb.2 k
      exact ⟨k', mem_erase.mpr ⟨fun e => (mem_erase.mp hk).1 (by rw [e]), mem_univ _⟩, rfl⟩
  rw [e1, (hκ j').1, (hκ j').2]
  exact key'

/-! ### A face with one loaded edge -/

/-- The profile of a face with one loaded edge, in index form. The root pair is `(a, b)`, the
pair on the loaded edge is `(s, t)`, with profile `w s t`; `B₁ a s` and `B₂ t b` are the numbers
of proper colourings of the two arcs of ordinary edges. Pairs of equal colours on the loaded edge
(the pattern `El`) are left out. -/
def genF (B₁ : Fin 3 → Fin 3 → ℕ) (El : BMat) (B₂ : Fin 3 → Fin 3 → ℕ)
    (w : Fin 3 → Fin 3 → ℝ) (a b : Fin 3) : ℝ :=
  ∑ s, ∑ t, if El s t = true then 0 else (B₁ a s : ℝ) * w s t * (B₂ t b : ℝ)

theorem genF_nonneg (B₁ : Fin 3 → Fin 3 → ℕ) (El : BMat) (B₂ : Fin 3 → Fin 3 → ℕ)
    {w : Fin 3 → Fin 3 → ℝ} (hw : ∀ s t, 0 ≤ w s t) (a b : Fin 3) : 0 ≤ genF B₁ El B₂ w a b :=
  sum_nonneg fun s _ => sum_nonneg fun t _ => by
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hw s t)) (Nat.cast_nonneg _)

/-- The face with arc counts `B₁`, `B₂`, pattern `El` on the loaded edge and pattern `Er` on the
root edge maps the ball class to the ball class, multiplying the constant by `α`. -/
def GenOK (B₁ : Fin 3 → Fin 3 → ℕ) (El : BMat) (B₂ : Fin 3 → Fin 3 → ℕ) (Er : BMat) (α : ℕ) :
    Prop :=
  ∀ w : Fin 3 → Fin 3 → ℝ, (∀ s t, 0 ≤ w s t) → ∀ A : ℝ, 0 < A → IdxBall El w A →
    IdxBallAt id Er (genF B₁ El B₂ w) (α * A)

/-- Fewer colourings of the arcs and more equal colours on the loaded edge make the statement
stronger. -/
theorem GenOK.mono {B₁ B₁' B₂ B₂' : Fin 3 → Fin 3 → ℕ} {El El' Er : BMat} {α : ℕ}
    (h : GenOK B₁ El B₂ Er α) (h1 : ∀ a s, B₁ a s ≤ B₁' a s) (h2 : ∀ t b, B₂ t b ≤ B₂' t b)
    (hE : ∀ s t, El' s t = true → El s t = true) : GenOK B₁' El' B₂' Er α := by
  intro w hw A hA hball
  have hball' : IdxBall El w A := by
    intro σ hσ j c d hcd
    refine hball σ ⟨hσ.1, fun c d h' => hσ.2 c d (hE c d h')⟩ j c d ?_
    cases hc : El' c d with
    | false => rfl
    | true => rw [hE c d hc] at hcd; cases hcd
  refine (h w hw A hA hball').mono (genF_nonneg B₁ El B₂ hw) fun a b => ?_
  unfold genF
  refine sum_le_sum fun s _ => sum_le_sum fun t _ => ?_
  by_cases hEl : El s t = true
  · rw [ite_eq_left hEl]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hw s t)) (Nat.cast_nonneg _)
  · have hEl' : ¬ El' s t = true := fun h' => hEl (hE s t h')
    rw [ite_eq_right hEl, ite_eq_right hEl']
    exact mul_le_mul (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (h1 a s)) (hw s t))
      (Nat.cast_le.mpr (h2 t b)) (Nat.cast_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (hw s t))

end Outerplanar
