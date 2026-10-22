/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Seven.Cond7

/-!
# Swapping the value of one vertex

Fix a vertex `z` and a set `N` of pairwise non-adjacent vertices, not containing `z`, and look at
the fibre over `U = {z} ∪ N`. With the value of `z` fixed, the vertices of `N` are independent:

* the solutions with `z = a` are at most the product of the available sets on `N`
  (`card_cls_val_le`);
* if `a₀` is available at `z`, the solutions with `z = a₀` are at least the product of the values
  on `N` compatible with `a₀` (`card_cls_val_ge`).

So in every fibre the value `a` is at most `∏ |avail| / |avail compatible with a₀|` times as
frequent as `a₀`. With a fibre comparison inside an event read off `U` (`fibre_cmp_rel`), this
bounds an event with `z = a` by the same event with `z = a₀`.
-/

open Finset
open scoped Classical

namespace GridGen.Gauge

variable {X : Type*} [Fintype X] [DecidableEq X]

namespace CSP

variable (C : CSP X)

/-- **Fibre comparison inside an event read off the fibres.** -/
theorem fibre_cmp_rel (U : Finset X) (Q₁ Q₂ R : (X → ℕ) → Prop) [DecidablePred Q₁]
    [DecidablePred Q₂] [DecidablePred R] (hR : OffU U R) (a b : ℕ)
    (h : ∀ g ∈ C.Ω, R g → ((C.cls U g).filter Q₁).card * a ≤ ((C.cls U g).filter Q₂).card * b) :
    ((C.Ω.filter R).filter Q₁).card * a ≤ ((C.Ω.filter R).filter Q₂).card * b := by
  set T := (C.Ω.filter R).image (restr U)
  have hfib : ∀ g ∈ C.Ω.filter R,
      (C.Ω.filter R).filter (fun f => restr U f = restr U g) = C.cls U g := by
    intro g hg
    rw [mem_filter] at hg
    rw [cls_eq_filter]
    ext f
    simp only [mem_filter]
    constructor
    · rintro ⟨⟨hf, -⟩, he⟩; exact ⟨hf, he⟩
    · rintro ⟨hf, he⟩
      refine ⟨⟨hf, (hR f g fun x hx => ?_).mpr hg.2⟩, he⟩
      have := congrFun he x
      simpa [restr, hx] using this
  have hsum : ∀ Q : (X → ℕ) → Prop, ∀ [DecidablePred Q], ((C.Ω.filter R).filter Q).card =
      ∑ ω ∈ T, ((C.Ω.filter R).filter Q |>.filter (fun f => restr U f = ω)).card := by
    intro Q _
    exact card_eq_sum_card_fiberwise (fun f hf => mem_image_of_mem _ (mem_filter.mp hf).1)
  rw [hsum Q₁, hsum Q₂, sum_mul, sum_mul]
  refine sum_le_sum fun ω hω => ?_
  obtain ⟨g, hg, rfl⟩ := mem_image.mp hω
  have e : ∀ Q : (X → ℕ) → Prop, ∀ [DecidablePred Q],
      ((C.Ω.filter R).filter Q).filter (fun f => restr U f = restr U g) = (C.cls U g).filter Q := by
    intro Q _
    rw [← hfib g hg]; ext f; simp only [mem_filter]; tauto
  rw [e Q₁, e Q₂]
  exact h g (mem_filter.mp hg).1 (mem_filter.mp hg).2

variable {C}

section Swap

variable {z : X} {N : Finset X}

/-- **Upper count with `z` fixed.** -/
theorem card_cls_val_le (hzN : z ∉ N) (g : X → ℕ) (a : ℕ) :
    ((C.cls (insert z N) g).filter (fun f => f z = a)).card ≤
      ∏ n ∈ N, (C.avail (insert z N) g n).card := by
  rw [← card_pi]
  refine card_le_card_of_injOn (fun f n _ => f n) (fun f hf => ?_) (fun f hf f' hf' he => ?_)
  · rw [mem_coe, mem_filter] at hf
    rw [mem_coe, mem_pi]
    intro n hn
    exact C.mem_avail_of_mem_cls hf.1 (mem_insert_of_mem hn)
  · rw [mem_coe, mem_filter] at hf hf'
    have h1 := (C.mem_cls.mp hf.1).2
    have h1' := (C.mem_cls.mp hf'.1).2
    funext x
    by_cases hxU : x ∈ insert z N
    · rcases mem_insert.mp hxU with rfl | hxN
      · rw [hf.2, hf'.2]
      · exact congrFun (congrFun he x) hxN
    · rw [h1 x hxU, h1' x hxU]

/-- The values at `n` compatible with `a₀` at `z`. -/
noncomputable def compat (U : Finset X) (g : X → ℕ) (z n : X) (a₀ : ℕ) : Finset ℕ :=
  (C.avail U g n).filter (fun b => (C.adj z n → ¬ C.conf z n a₀ b) ∧ (C.adj n z → ¬ C.conf n z b a₀))

/-- **Lower count with `z = a₀`.** -/
theorem card_cls_val_ge (hzN : z ∉ N) (hNN : ∀ n ∈ N, ∀ n' ∈ N, ¬ C.adj n n') (hI : C.Irrefl)
    {g : X → ℕ} (hg : C.ValidOff (insert z N) g) {a₀ : ℕ}
    (ha₀ : a₀ ∈ C.avail (insert z N) g z) :
    ∏ n ∈ N, (C.compat (insert z N) g z n a₀).card ≤
      ((C.cls (insert z N) g).filter (fun f => f z = a₀)).card := by
  rw [← card_pi]
  set fill : ((n : X) → n ∈ N → ℕ) → X → ℕ := fun t x =>
    if h : x ∈ N then t x h else if x = z then a₀ else g x with hfill
  refine card_le_card_of_injOn fill (fun t ht => ?_) (fun t ht t' ht' he => ?_)
  · rw [mem_coe, mem_pi] at ht
    rw [mem_coe, mem_filter]
    have hz : fill t z = a₀ := by simp [hfill, hzN]
    refine ⟨C.mem_cls_of hg (fun x hx => ?_) (fun u hu => ?_) (fun u u' hu hu' hadj => ?_), hz⟩
    · have hxN : x ∉ N := fun h => hx (mem_insert_of_mem h)
      have hxz : x ≠ z := fun h => hx (h ▸ mem_insert_self _ _)
      simp [hfill, hxN, hxz]
    · rcases mem_insert.mp hu with rfl | huN
      · rw [hz]; exact ha₀
      · have := ht u huN
        simp only [hfill, dite_eq_left huN]
        exact (mem_filter.mp this).1
    · rcases mem_insert.mp hu with rfl | huN <;> rcases mem_insert.mp hu' with rfl | hu'N
      · exact absurd hadj (hI _)
      · rw [hz]
        have := ht u' hu'N
        simp only [hfill, dite_eq_left hu'N]
        exact (mem_filter.mp this).2.1 hadj
      · rw [hz]
        have := ht u huN
        simp only [hfill, dite_eq_left huN]
        exact (mem_filter.mp this).2.2 hadj
      · exact absurd hadj (hNN u huN u' hu'N)
  · funext n hn
    have := congrFun he n
    simpa [hfill, hn] using this

end Swap

end CSP

end GridGen.Gauge
