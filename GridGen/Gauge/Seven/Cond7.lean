/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.CSP

/-!
# Fibre bounds relative to an event off the fibre

`fibre_sum_le` compares a predicate with the whole solution set, fibre by fibre. Here the
solutions are first restricted to an event `R` that reads only the vertices off the fibre set `U`.
Each fibre then lies inside `R` or outside it, so the same comparison holds inside `R`
(`fibre_sum_le_rel`). The chain bound follows in the same form: prescribing the values on a chain
avoiding the vertices `R` reads costs the chain product *inside* `R` (`card_prescribed_cond`).
-/

open Finset
open scoped Classical

namespace GridGen.Gauge

variable {X : Type*} [Fintype X] [DecidableEq X]

namespace CSP

variable (C : CSP X)

/-- An event that reads only the vertices off `U`. -/
def OffU (U : Finset X) (R : (X → ℕ) → Prop) : Prop :=
  ∀ f g : X → ℕ, (∀ x, x ∉ U → f x = g x) → (R f ↔ R g)

/-- **Fibre sums inside an event read off the fibres.** -/
theorem fibre_sum_le_rel (U : Finset X) (Q R : (X → ℕ) → Prop) [DecidablePred Q]
    [DecidablePred R] (hR : OffU U R) (c : ℕ)
    (h : ∀ g ∈ C.Ω, R g → ((C.cls U g).filter Q).card * c ≤ (C.cls U g).card) :
    ((C.Ω.filter R).filter Q).card * c ≤ (C.Ω.filter R).card := by
  set T := (C.Ω.filter R).image (restr U)
  have hΩ : (C.Ω.filter R).card =
      ∑ ω ∈ T, ((C.Ω.filter R).filter (fun f => restr U f = ω)).card :=
    card_eq_sum_card_fiberwise (fun f hf => mem_image_of_mem _ hf)
  have hQ : ((C.Ω.filter R).filter Q).card =
      ∑ ω ∈ T, (((C.Ω.filter R).filter Q).filter (fun f => restr U f = ω)).card :=
    card_eq_sum_card_fiberwise (fun f hf => mem_image_of_mem _ (mem_filter.mp hf).1)
  rw [hΩ, hQ, sum_mul]
  refine sum_le_sum fun ω hω => ?_
  obtain ⟨g, hg, rfl⟩ := mem_image.mp hω
  rw [mem_filter] at hg
  -- the fibre of `g` inside `R` is the whole fibre
  have hfib : (C.Ω.filter R).filter (fun f => restr U f = restr U g) = C.cls U g := by
    rw [cls_eq_filter]
    ext f
    simp only [mem_filter]
    constructor
    · rintro ⟨⟨hf, -⟩, he⟩; exact ⟨hf, he⟩
    · rintro ⟨hf, he⟩
      refine ⟨⟨hf, (hR f g fun x hx => ?_).mpr hg.2⟩, he⟩
      have := congrFun he x
      simpa [restr, hx] using this
  have hfibQ : ((C.Ω.filter R).filter Q).filter (fun f => restr U f = restr U g) =
      (C.cls U g).filter Q := by
    rw [← hfib]; ext f; simp only [mem_filter]; tauto
  rw [hfib, hfibQ]
  exact h g hg.1 hg.2

/-- **The chain bound inside an event read off the chain.** -/
theorem card_prescribed_cond (hM : C.Match) (hI : C.Irrefl) (ch : List X) (hch : ch.Nodup)
    (S : X → Finset ℕ) (hS : ∀ x ∈ ch, (S x).card ≤ 1) (R : (X → ℕ) → Prop) [DecidablePred R]
    (hR : OffU ch.toFinset R) :
    ((C.Ω.filter R).filter (fun f => ∀ x ∈ ch, f x ∈ S x)).card * C.chainProd ch ≤
      (C.Ω.filter R).card := by
  have hQ : ((C.Ω.filter R).filter fun f : X → ℕ => ∀ x ∈ ch, f x ∈ S x)
      = (C.Ω.filter R).filter (fun f => ∀ x ∈ ch.toFinset, f x ∈ S x) := by
    ext f; simp
  rw [hQ]
  refine C.fibre_sum_le_rel ch.toFinset _ R hR _ fun g hg _ => ?_
  have h1 := C.card_cls_prescribed_le_one ch.toFinset g S (fun x hx => hS x (by simpa using hx))
  have h2 := C.chainProd_le_card_cls hM hI ch g hch (C.validOff_of_valid ((C.mem_Ω).mp hg))
  calc _ ≤ 1 * C.chainProd ch := Nat.mul_le_mul_right _ h1
    _ ≤ _ := by rw [one_mul]; exact h2

end CSP

end GridGen.Gauge
