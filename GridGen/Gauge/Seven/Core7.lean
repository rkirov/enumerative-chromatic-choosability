/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Seven.Cover7
import GridGen.Gauge.Seven.Steps7

/-!
# The seam at `k = 7`: one colour at a time

The bounds a seam needs, as a structure `Bounds7`:

* `star`: deleting an unpaired star gains at least `γ` of the count (`box_bound_seven`);
* `move`: a move through a hole of row `r`, the edge being next to `r`, loses at most `θ` times the
  hit event of a deleted star of row `r` at the hole, plus `ε` of the count (absorption and
  residual chains);
* `drift`: a move at the edge below row `r` through the hole `h` of row `r` changes the hit event
  of a deleted star of row `r` at `h` by at most the factor `1 + δ`;
* the numerical conditions of `step_H`, `step_D`, `step_double`.

`step_slab_H`, `step_slab_D`, `step_slab_double` apply them to one colour of the lookahead
process.
-/

open Finset
open scoped Classical

set_option linter.unusedSectionVars false

namespace GridGen.Gauge

variable {c m : ℕ} {P A : Fin m → Finset ℕ}

/-- **The bounds of a seam at `k = 7`.** -/
structure Bounds7 (c m : ℕ) (P A : Fin m → Finset ℕ) (hc : 1 ≤ c) where
  γ : ℚ
  θ : ℚ
  ε : ℚ
  δ : ℚ
  γV : ℚ
  star : ∀ N : Fin m → ℕ → ℕ, KeyInj 7 A N → ∀ (v : Fin m) (a₀ : ℕ), a₀ ∈ A v → 7 ≤ N v a₀ →
    (6 ≤ (P v).card ∨ a₀ ∉ P v) → ∀ x₀, x₀ < 7 →
      γ * (Z c m 7 P A N : ℚ) ≤ ((slab c m 7 P A N).Ω.filter (Hit hc v a₀ x₀)).card
  move : ∀ M : Fin m → ℕ → ℕ, KeyInj 7 A M → ∀ (w x y : ℕ), x < 7 → y < 7 → x ≠ y →
    ∀ (r : Fin m), (r.val = w ∨ r.val = w + 1) → ∀ h, (h = x ∨ h = y) →
      (∀ a ∈ A r, M r a ≠ h) → ∀ a₀ ∈ A r, 7 ≤ M r a₀ →
        (((slab c m 7 P A M).Ω.filter (Bad hc M w x y)).card : ℚ) ≤
          θ * ((slab c m 7 P A M).Ω.filter (Hit hc r a₀ h)).card + ε * Z c m 7 P A M
  drift : ∀ M : Fin m → ℕ → ℕ, KeyInj 7 A M → ∀ (r : Fin m) (x h : ℕ), x < 7 → h < 7 →
    x ≠ h → (∀ a ∈ A r, M r a ≠ h) → ∀ a₀ ∈ A r, 7 ≤ M r a₀ →
      (((slab c m 7 P A (moveKey M r.val x h)).Ω.filter (Hit hc r a₀ h)).card : ℚ) ≤
        (1 + δ) * ((slab c m 7 P A M).Ω.filter (Hit hc r a₀ h)).card
  hγ0 : 0 ≤ γ
  hγ1 : γ < 1
  hθ0 : 0 ≤ θ
  hε0 : 0 ≤ ε
  hθε : θ ≤ 1 - ε
  hH : ε * (1 - γ) ≤ (1 - ε - θ) * γ
  hD : ε ≤ γV
  hγV1 : γV ≤ 1
  hcoef : 0 ≤ (1 - ε) ^ 2 - (1 - ε) * θ - θ * (1 + δ)
  hdbl : 1 - γV ≤ (1 - ε) ^ 2 + ((1 - ε) ^ 2 - (1 - ε) * θ - θ * (1 + δ)) * γ

variable {hc : 1 ≤ c}

/-- Deleting a star and applying a move through its hole: the counts before and after, and the
hit event, in the form the arithmetic lemmas take. -/
theorem del_move_counts (B : Bounds7 c m P A hc) {M : Fin m → ℕ → ℕ} (hK : KeyInj 7 A M)
    {r : Fin m} {s : ℕ} (hs : s ∈ A r) {g : ℕ} (hMg : M r s = g) (hg : g < 7)
    (hPr : 6 ≤ (P r).card ∨ s ∉ P r) {w x y : ℕ} (hx : x < 7) (hy : y < 7) (hxy : x ≠ y)
    (hrw : r.val = w ∨ r.val = w + 1) (hgxy : g = x ∨ g = y)
    (hhole : ∀ a ∈ A r, unpair 7 M r s r a ≠ g) :
    (Z c m 7 P A (unpair 7 M r s) : ℚ) = Z c m 7 P A M +
        ((slab c m 7 P A (unpair 7 M r s)).Ω.filter (Hit hc r s g)).card ∧
      B.γ * (Z c m 7 P A (unpair 7 M r s) : ℚ) ≤
        ((slab c m 7 P A (unpair 7 M r s)).Ω.filter (Hit hc r s g)).card ∧
      (Z c m 7 P A (unpair 7 M r s) : ℚ) - B.θ *
          ((slab c m 7 P A (unpair 7 M r s)).Ω.filter (Hit hc r s g)).card -
          B.ε * Z c m 7 P A (unpair 7 M r s) ≤
        Z c m 7 P A (moveKey (unpair 7 M r s) w x y) := by
  have hK' := keyInj_unpair hK r s
  have h7 : 7 ≤ unpair 7 M r s r s := by simp [unpair]
  refine ⟨?_, B.star _ hK' r s hs h7 hPr g hg, ?_⟩
  · have := card_unpair (k := 7) (P := P) (A := A) M hc r s g hMg
    unfold Z
    exact_mod_cast this
  · have hmv := card_le_move_add_bad (k := 7) (P := P) (A := A) (hc := hc) (M := unpair 7 M r s) (w := w) hx hy
    have hb := B.move _ hK' w x y hx hy hxy r hrw g hgxy hhole s hs h7
    have hmv' : (Z c m 7 P A (unpair 7 M r s) : ℚ) ≤ Z c m 7 P A (moveKey (unpair 7 M r s) w x y) +
        (((slab c m 7 P A (unpair 7 M r s)).Ω.filter (Bad hc (unpair 7 M r s) w x y)).card : ℚ) := by
      unfold Z; exact_mod_cast hmv
    linarith

/-- **An H- or D-move with its fresh star**: `Z` after `≥ Z` before (H) or `≥ (1 - γ_V) Z`
before (D). -/
theorem step_slab_single (B : Bounds7 c m P A hc) {M : Fin m → ℕ → ℕ} (hK : KeyInj 7 A M)
    {r : Fin m} {s : ℕ} (hs : s ∈ A r) {g : ℕ} (hMg : M r s = g) (hg : g < 7)
    (hPr : 6 ≤ (P r).card ∨ s ∉ P r) {w x y : ℕ} (hx : x < 7) (hy : y < 7) (hxy : x ≠ y)
    (hrw : r.val = w ∨ r.val = w + 1) (hgxy : g = x ∨ g = y)
    (hhole : ∀ a ∈ A r, unpair 7 M r s r a ≠ g) :
    (Z c m 7 P A M : ℚ) ≤ Z c m 7 P A (moveKey (unpair 7 M r s) w x y) ∧
      (1 - B.γV) * (Z c m 7 P A M : ℚ) ≤ Z c m 7 P A (moveKey (unpair 7 M r s) w x y) := by
  obtain ⟨h1, h2, h3⟩ := del_move_counts B hK hs hMg hg hPr hx hy hxy hrw hgxy hhole
  have hZ : (0 : ℚ) ≤ Z c m 7 P A M := by positivity
  have hE : (0 : ℚ) ≤ ((slab c m 7 P A (unpair 7 M r s)).Ω.filter (Hit hc r s g)).card := by
    positivity
  exact ⟨step_H hZ hE h1 h2 h3 B.hε0 B.hγ1 B.hH B.hθε,
    step_D hZ hE h1 h3 B.hθε B.hD⟩

/-- **A double**: the star deleted, the move at the edge below row `r` through its hole, then the
move at the edge above row `r` through the same hole. -/
theorem step_slab_double (B : Bounds7 c m P A hc) {M : Fin m → ℕ → ℕ} (hK : KeyInj 7 A M)
    {r : Fin m} {s : ℕ} (hs : s ∈ A r) {g : ℕ} (hMg : M r s = g) (hg : g < 7)
    (hPr : 6 ≤ (P r).card ∨ s ∉ P r) {x₂ x₁ y₁ w₁ : ℕ} (hx₂ : x₂ < 7) (hx₂g : x₂ ≠ g)
    (hx₁ : x₁ < 7) (hy₁ : y₁ < 7) (hxy₁ : x₁ ≠ y₁) (hrw : r.val = w₁ + 1) (hgxy : g = x₁ ∨ g = y₁)
    (hhole : ∀ a ∈ A r, unpair 7 M r s r a ≠ g) :
    (1 - B.γV) * (Z c m 7 P A M : ℚ) ≤
      Z c m 7 P A (moveKey (moveKey (unpair 7 M r s) r.val x₂ g) w₁ x₁ y₁) := by
  -- the first move, at the edge below row `r`
  obtain ⟨h1, h2, h3⟩ := del_move_counts (w := r.val) B hK hs hMg hg hPr hx₂ hg hx₂g
    (Or.inl rfl) (Or.inr rfl) hhole
  set M₀ := unpair 7 M r s
  set M₁ := moveKey M₀ r.val x₂ g
  have hK₀ : KeyInj 7 A M₀ := keyInj_unpair hK r s
  have hK₁ : KeyInj 7 A M₁ := keyInj_moveKey hK₀ r.val hx₂ hg
  -- row `r` is not moved by the first move
  have hrow : ∀ a, M₁ r a = M₀ r a := fun a => by simp [M₁, moveKey]
  have hhole₁ : ∀ a ∈ A r, M₁ r a ≠ g := fun a ha => by rw [hrow]; exact hhole a ha
  have h7 : 7 ≤ M₁ r s := by rw [hrow]; simp [M₀, unpair]
  -- the second move, at the edge above row `r`
  have hb := B.move _ hK₁ w₁ x₁ y₁ hx₁ hy₁ hxy₁ r (Or.inr hrw) g hgxy hhole₁ s hs h7
  have hmv := card_le_move_add_bad (k := 7) (P := P) (A := A) (hc := hc) (M := M₁) (w := w₁) hx₁ hy₁
  have hmv' : (Z c m 7 P A M₁ : ℚ) ≤ Z c m 7 P A (moveKey M₁ w₁ x₁ y₁) +
      (((slab c m 7 P A M₁).Ω.filter (Bad hc M₁ w₁ x₁ y₁)).card : ℚ) := by
    unfold Z; exact_mod_cast hmv
  have hdr := B.drift _ hK₀ r x₂ g hx₂ hg hx₂g hhole s hs (by simp [M₀, unpair])
  have hZ : (0 : ℚ) ≤ Z c m 7 P A M := by positivity
  have hE : (0 : ℚ) ≤ ((slab c m 7 P A M₀).Ω.filter (Hit hc r s g)).card := by positivity
  exact step_double hZ hE h1 h2 h3 (by linarith) hdr B.hθ0 B.hε0 (by linarith [B.hθε, B.hθ0])
    B.hγ0 B.hcoef B.hdbl

end GridGen.Gauge
