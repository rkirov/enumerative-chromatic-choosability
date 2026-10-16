/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Slab

/-!
# Deleting a seam pair (a "star")

When a colour `a₀` of the seam column leaves the list of the next column, its seam pair
`(a₀, x₀)` in row `v` is deleted: its key becomes `k`, which no future label equals. Deleting a
constraint only adds solutions. The added ones are exactly the solutions that put `a₀` at
`(1, v)` and `x₀` at `(2, v)` (`card_unpair`).
-/

open Finset
open scoped Classical

set_option linter.unusedSectionVars false

namespace GridGen.Gauge

variable {c m k : ℕ} {P A : Fin m → Finset ℕ}

/-- Unpair the colour `a₀` in row `v`: its key becomes `k`. -/
def unpair (k : ℕ) (M : Fin m → ℕ → ℕ) (v : Fin m) (a₀ : ℕ) : Fin m → ℕ → ℕ :=
  fun v' a => if v' = v ∧ a = a₀ then k else M v' a

/-- The first future column. -/
def fut0 (hc : 1 ≤ c) : Fin (c + 2) := ⟨2, by omega⟩

/-- The "hit" event of a star: `a₀` on the seam cell, `x₀` on the first future cell of row `v`. -/
def Hit (hc : 1 ≤ c) (v : Fin m) (a₀ x₀ : ℕ) (f : Cell c m → ℕ) : Prop :=
  f (1, v) = a₀ ∧ f (fut0 hc, v) = x₀

theorem futOf_zero {f : Cell c m → ℕ} (hc : 1 ≤ c) (v : Fin m) :
    futOf f ⟨0, by omega⟩ v = f (fut0 hc, v) := rfl

/-- **The star identity.** -/
theorem card_unpair (M : Fin m → ℕ → ℕ) (hc : 1 ≤ c) (v : Fin m) (a₀ x₀ : ℕ)
    (hx : M v a₀ = x₀) :
    (slab c m k P A (unpair k M v a₀)).Ω.card
      = (slab c m k P A M).Ω.card
        + ((slab c m k P A (unpair k M v a₀)).Ω.filter (Hit hc v a₀ x₀)).card := by
  set Ω₁ := (slab c m k P A (unpair k M v a₀)).Ω
  set Ω₀ := (slab c m k P A M).Ω
  -- a valid future has labels below `k`
  have hlab : ∀ f : Cell c m → ℕ, FutValid k (keyed M (colOf f 1)) (futOf f) ∨
      FutValid k (keyed (unpair k M v a₀) (colOf f 1)) (futOf f) →
      ∀ t v', futOf f t v' < k := by
    intro f h t v'
    rcases h with h | h <;>
    · have := ((mem_states (rowG m)).mp (h.1 t)).1 v'
      simpa [unif] using this
  have hsub : Ω₀ ⊆ Ω₁ := by
    intro f hf
    rw [CSP.mem_Ω, valid_iff] at hf ⊢
    obtain ⟨h0, h1, h01, hψ⟩ := hf
    refine ⟨h0, h1, h01, hψ.1, fun t ht v' => ?_, hψ.2.2⟩
    have hk := hlab f (Or.inl hψ) t v'
    simp only [keyed, unpair]
    split_ifs with h
    · exact fun he => by omega
    · exact hψ.2.1 t ht v'
  have hdiff : Ω₁ \ Ω₀ = Ω₁.filter (Hit hc v a₀ x₀) := by
    ext f
    rw [mem_sdiff, mem_filter]
    constructor
    · rintro ⟨h1, h0⟩
      refine ⟨h1, ?_⟩
      by_contra hn
      apply h0
      rw [CSP.mem_Ω, valid_iff] at h1 ⊢
      obtain ⟨g0, g1, g01, hψ⟩ := h1
      refine ⟨g0, g1, g01, hψ.1, fun t ht v' => ?_, hψ.2.2⟩
      have e := hψ.2.1 t ht v'
      simp only [keyed, unpair] at e ⊢
      by_cases hv : v' = v ∧ colOf f 1 v' = a₀
      · obtain ⟨rfl, ha⟩ := hv
        rw [ha, hx]
        intro he
        apply hn
        refine ⟨ha, ?_⟩
        have : t = ⟨0, by omega⟩ := Fin.ext ht
        rw [this, futOf_zero hc] at he
        exact he.symm
      · rwa [ite_eq_right hv] at e
    · rintro ⟨h1, hhit⟩
      refine ⟨h1, fun h0 => ?_⟩
      rw [CSP.mem_Ω, valid_iff] at h0
      have e := h0.2.2.2.2.1 ⟨0, by omega⟩ rfl v
      simp only [keyed] at e
      apply e
      rw [futOf_zero (f := f) hc]
      show M v (f (1, v)) = f (fut0 hc, v)
      rw [hhit.1, hhit.2, hx]
  rw [← hdiff, card_sdiff_of_subset hsub, Nat.add_sub_cancel' (card_le_card hsub)]

end GridGen.Gauge
