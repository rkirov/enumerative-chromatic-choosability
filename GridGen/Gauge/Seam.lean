/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Labelling

/-!
# The slab count and the star step

The slab count `Z` of a seam (`Slab.lean`) as a function of the seam keys, and the two key
operations of a seam: unpairing a colour that leaves its row (a *star*) and a label transposition
(`moveKey`). Each star multiplies the count by at least `1/(1-γ_k)`, by the box bound with
`γ_k = (k-4)²(k-5)²/(k²(k-3)⁴)` (`star_step`). The moves and the full slab inequality are in
`Eight/`.
-/

open Finset
open scoped Classical

set_option linter.unusedSectionVars false

namespace GridGen.Gauge

variable {c m k : ℕ}

/-- The star gain `γ_k`. -/
noncomputable def gammaK (k : ℕ) : ℚ := ((k : ℚ) - 4) ^ 2 * ((k : ℚ) - 5) ^ 2 / ((k : ℚ) ^ 2 * ((k : ℚ) - 3) ^ 4)

/-! ### The slab count, and the star step -/

variable {P A : Fin m → Finset ℕ}

/-- The slab count. -/
noncomputable def Z (c m k : ℕ) (P A : Fin m → Finset ℕ) (M : Fin m → ℕ → ℕ) : ℕ :=
  (slab c m k P A M).Ω.card

/-- The count only reads the keys of the colours of the seam column. -/
theorem Z_congr {M M' : Fin m → ℕ → ℕ} (h : ∀ v, ∀ a ∈ A v, M v a = M' v a) :
    Z c m k P A M = Z c m k P A M' := by
  unfold Z
  rw [card_Ω_eq, card_Ω_eq]
  refine sum_congr rfl fun p _ => sum_congr rfl fun s hs => ?_
  congr 1
  funext v
  exact h v (s v) (((mem_states (rowG m)).mp (mem_filter.mp hs).1).1 v)

theorem keyInj_unpair {N : Fin m → ℕ → ℕ} (hK : KeyInj k A N) (v : Fin m) (a₀ : ℕ) :
    KeyInj k A (unpair k N v a₀) := by
  intro v' a a' ha ha' e hlt
  unfold unpair at e hlt
  split_ifs at e hlt with h1 h2 h2 <;> try omega
  exact hK v' a a' ha ha' e hlt

theorem keyInj_moveKey {M : Fin m → ℕ → ℕ} (hK : KeyInj k A M) (w : ℕ) {x y : ℕ}
    (hx : x < k) (hy : y < k) : KeyInj k A (moveKey M w x y) := by
  intro v a a' ha ha' e hlt
  unfold moveKey at e hlt
  split_ifs at e hlt with hw
  · have e' := (Equiv.swap x y).injective e
    refine hK v a a' ha ha' e' ?_
    by_contra hge
    push Not at hge
    rw [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)] at hlt
    omega
  · exact hK v a a' ha ha' e hlt

/-- **A star step.** -/
theorem star_step (hk : 6 ≤ k) (hc : 1 ≤ c) (hA : ∀ v, (A v).card = k) {N : Fin m → ℕ → ℕ}
    (hK : KeyInj k A N) (v : Fin m) {a₀ : ℕ} (ha : a₀ ∈ A v) (hx : N v a₀ < k)
    (hPv : k - 1 ≤ (P v).card ∨ a₀ ∉ P v) :
    (Z c m k P A N : ℚ) ≤ (1 - gammaK k) * Z c m k P A (unpair k N v a₀) := by
  have hsplit := card_unpair (k := k) (P := P) (A := A) N hc v a₀ (N v a₀) rfl
  have hbox := box_bound (P := P) (by omega) (keyInj_unpair hK v a₀) hA hc v ha hx
    (by simp [unpair]) hPv
  unfold Z
  set Z₁ := (slab c m k P A (unpair k N v a₀)).Ω.card
  set hit := ((slab c m k P A (unpair k N v a₀)).Ω.filter (Hit hc v a₀ (N v a₀))).card
  have hk' : (6 : ℚ) ≤ k := by exact_mod_cast hk
  have hq : (Z₁ : ℚ) * (((k : ℚ) - 4) ^ 2 * ((k : ℚ) - 5) ^ 2) ≤
      (hit : ℚ) * ((k : ℚ) ^ 2 * ((k : ℚ) - 3) ^ 4) := by
    have := hbox
    rw [show k - 4 = (k - 4 : ℕ) from rfl] at this
    have e4 : ((k - 4 : ℕ) : ℚ) = (k : ℚ) - 4 := by push_cast [Nat.cast_sub (by omega : 4 ≤ k)]; ring
    have e5 : ((k - 5 : ℕ) : ℚ) = (k : ℚ) - 5 := by push_cast [Nat.cast_sub (by omega : 5 ≤ k)]; ring
    have e3 : ((k - 3 : ℕ) : ℚ) = (k : ℚ) - 3 := by push_cast [Nat.cast_sub (by omega : 3 ≤ k)]; ring
    have := (Nat.cast_le (α := ℚ)).mpr hbox
    push_cast at this
    rw [e4, e5, e3] at this
    linarith
  have hsplit' : (Z₁ : ℚ) = (slab c m k P A N).Ω.card + hit := by exact_mod_cast hsplit
  have hden : 0 < (k : ℚ) ^ 2 * ((k : ℚ) - 3) ^ 4 := by
    have : 0 < (k : ℚ) - 3 := by linarith
    positivity
  have hγ : gammaK k * Z₁ ≤ hit := by
    unfold gammaK
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    linarith
  linarith

/-- The stars. -/
noncomputable def stars (A B : Fin m → Finset ℕ) : Finset (Fin m × ℕ) :=
  univ.biUnion fun v => (A v \ B v).image fun a => (v, a)

theorem mem_stars {A B : Fin m → Finset ℕ} {p : Fin m × ℕ} :
    p ∈ stars A B ↔ p.2 ∈ A p.1 ∧ p.2 ∉ B p.1 := by
  unfold stars
  simp only [mem_biUnion, mem_univ, true_and, mem_image, mem_sdiff]
  constructor
  · rintro ⟨v, a, ha, rfl⟩; exact ha
  · intro h; exact ⟨p.1, p.2, h, rfl⟩

theorem card_stars (A B : Fin m → Finset ℕ) :
    (stars A B).card = ∑ v, (A v \ B v).card := by
  unfold stars
  rw [card_biUnion]
  · exact sum_congr rfl fun v _ => card_image_of_injective _ fun a b h => by simpa using h
  · intro v _ w _ hvw
    refine Finset.disjoint_left.mpr fun p hp hq => hvw ?_
    rw [mem_image] at hp hq
    obtain ⟨a, _, rfl⟩ := hp
    obtain ⟨b, _, e⟩ := hq
    exact (congrArg Prod.fst e).symm

/-- Keys after unpairing a set of stars. -/
def starKeys (k : ℕ) (β : ℕ → ℕ → ℕ) (S : Finset (Fin m × ℕ)) : Fin m → ℕ → ℕ :=
  fun v a => if (v, a) ∈ S then k else β v.val a

/-! ### Rows beyond the column -/

/-- Rows of a column, extended by empty lists. -/
def extR (A : Fin m → Finset ℕ) : ℕ → Finset ℕ := fun v => if h : v < m then A ⟨v, h⟩ else ∅

theorem extR_val (A : Fin m → Finset ℕ) (v : Fin m) : extR A v.val = A v := by
  simp [extR, v.isLt]

theorem extR_ge (A : Fin m → Finset ℕ) {v : ℕ} (h : m ≤ v) : extR A v = ∅ := by
  simp [extR, show ¬ v < m by omega]

end GridGen.Gauge
