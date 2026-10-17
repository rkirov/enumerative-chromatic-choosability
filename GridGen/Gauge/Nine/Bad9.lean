/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Nine.Box9
import GridGen.Gauge.Nine.Counts

/-!
# The bad event at `k = 9`: per-path chain weights

`card_bad_le` charges every chain `(k-3)^{L+1}(k-4)`. A crossing path of two cells closes a
4-cycle with its two seam cells. There the first seam cell has two later neighbours, and the
chain costs `(k-2)(k-3)²(k-4)` (`chainProd_two`). `card_bad_le_w` takes any per-length weight
dominated by the chain products. At `k = 9` the weights are `1260` for two cells and
`5 · 6^{L+1}` otherwise.
-/

open Finset
open scoped Classical

set_option linter.unusedSectionVars false

namespace GridGen.Gauge

variable {c m k : ℕ} {P A : Fin m → Finset ℕ} {M : Fin m → ℕ → ℕ}

/-- **The 4-cycle chain.** -/
theorem chainProd_two {hc : 1 ≤ c} {w : ℕ} (hk : 4 ≤ k) (hA : ∀ v, (A v).card = k)
    {l : List (Cell c m)} (hl : CrossPath hc w l) (hlen : l.length = 2) :
    (k - 2) * ((k - 3) ^ 2 * (k - 4)) ≤ (slab c m k P A M).chainProd (chainOf l) := by
  obtain ⟨hnd, hch, hfut, ⟨v₁, hw₁, h1⟩, ⟨v₂, hw₂, h2⟩⟩ := hl
  obtain ⟨a, b, rfl⟩ : ∃ a b, l = [a, b] := by
    match l, hlen with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  simp only [List.head?_cons, Option.some.injEq] at h1
  simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at h2
  subst h1; subst h2
  have hadj : slabAdj (fut0 hc, v₁) (fut0 hc, v₂) := by
    rw [List.isChain_cons_cons] at hch; exact hch.1
  have hv : v₂.val + 1 = v₁.val := by unfold slabAdj at hadj; simp at hadj; omega
  have hcl : chainOf [(fut0 hc, v₁), (fut0 hc, v₂)] =
      (1, v₁) :: [(fut0 hc, v₁), (fut0 hc, v₂), (1, v₂)] := by
    simp [chainOf, seamOf]
  rw [hcl]
  have hprops := chainOf_props (hc := hc) (w := w) (l := [(fut0 hc, v₁), (fut0 hc, v₂)])
    ⟨hnd, hch, hfut, ⟨v₁, hw₁, rfl⟩, ⟨v₂, hw₂, rfl⟩⟩
  rw [hcl] at hprops
  obtain ⟨-, hnd', hch', -, hcol⟩ := hprops
  rw [List.nodup_cons] at hnd'
  rw [List.isChain_cons_cons] at hch'
  have hD : ∀ z ∈ [(fut0 hc, v₁), (fut0 hc, v₂), ((1 : Fin (c + 2)), v₂)],
      ((slab c m k P A M).D z).card = k := by
    intro z hz
    by_cases h1 : z.1.val = 1
    · rw [slab_D_one h1, hA]
    · rw [slab_D_fut (by have := hcol z (by simp at hz ⊢; tauto); omega), card_range]
  have hrest := chainProd_ge (P := P) (A := A) (M := M) hk _ (by simp) hnd'.2 hch'.2 hD
  simp only [List.length_cons, List.length_nil] at hrest
  have h1v : (1 : Fin (c + 2)).val = 1 := Fin.val_one _
  have hout : ((slab c m k P A M).nbrsOut (1, v₁)
      [(fut0 hc, v₁), (fut0 hc, v₂), ((1 : Fin (c + 2)), v₂)].toFinset).card ≤ 2 := by
    refine card_le_of_coords _ [(0, v₁.val), (1, v₁.val + 1)] fun z hz => ?_
    rw [CSP.mem_nbrsOut] at hz
    have hcz := adj_coords (c := c) (k := k) (P := P) (A := A) (N := M) hz.1
    have hz2 := hz.2
    simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq, mem_insert,
      mem_singleton, not_or] at hz2
    have e1 : ((1 : Fin (c + 2)), v₁).1.val = 1 := h1v
    have e2 : ((1 : Fin (c + 2)), v₁).2.val = v₁.val := rfl
    rw [e1, e2] at hcz
    obtain ⟨n1, n2, n3⟩ := hz2
    have n1' : ¬ (z.1.val = 2 ∧ z.2.val = v₁.val) := fun h =>
      n1 (cell_eq (by rw [h.1]; rfl) h.2)
    have n3' : ¬ (z.1.val = 1 ∧ z.2.val = v₂.val) := fun h =>
      n3 (cell_eq (by rw [h.1, h1v]) h.2)
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
    omega
  simp only [CSP.chainProd]
  have hDz : ((slab c m k P A M).D ((1 : Fin (c + 2)), v₁)).card = k := by
    rw [slab_D_one h1v, hA]
  rw [hDz]
  calc (k - 2) * ((k - 3) ^ 2 * (k - 4))
      ≤ (k - ((slab c m k P A M).nbrsOut (1, v₁)
          [(fut0 hc, v₁), (fut0 hc, v₂), ((1 : Fin (c + 2)), v₂)].toFinset).card) *
        (slab c m k P A M).chainProd [(fut0 hc, v₁), (fut0 hc, v₂), ((1 : Fin (c + 2)), v₂)] :=
        Nat.mul_le_mul (by omega) (by simpa [CSP.chainProd] using hrest)
    _ = _ := by simp [CSP.chainProd]

/-- **The bad event, with per-length chain weights.** -/
theorem card_bad_le_w {hc : 1 ≤ c} {w x y : ℕ} (hK : KeyInj k A M) (hA : ∀ v, (A v).card = k)
    (hxy : x ≠ y) (hx : x < k) (hy : y < k) (W : ℕ → ℚ)
    (hW : ∀ l ∈ crossPaths (m := m) hc w,
      0 < W l.length ∧ W l.length ≤ (slab c m k P A M).chainProd (chainOf l)) :
    (((slab c m k P A M).Ω.filter (Bad hc M w x y)).card : ℚ) ≤
      (slab c m k P A M).Ω.card * ∑ l ∈ crossPaths (m := m) hc w, 2 / W l.length := by
  set C := slab c m k P A M
  set I := crossPaths (m := m) hc w ×ˢ ({x, y} : Finset ℕ)
  have hsub : C.Ω.filter (Bad hc M w x y) ⊆
      I.biUnion (fun i => C.Ω.filter (Event (A := A) M x y i.1 i.2)) := by
    intro f hf
    rw [mem_filter, CSP.mem_Ω] at hf
    obtain ⟨l, hl, ℓ₀, hℓ, he⟩ := bad_event (P := P) hxy hf.1 hf.2
    rw [mem_biUnion]
    exact ⟨(l, ℓ₀), mem_product.mpr ⟨hl, hℓ⟩, mem_filter.mpr ⟨(CSP.mem_Ω _).mpr hf.1, he⟩⟩
  have hone : ∀ i ∈ I, ((C.Ω.filter (Event (A := A) M x y i.1 i.2)).card : ℚ) ≤
      C.Ω.card / W i.1.length := by
    rintro ⟨l, ℓ₀⟩ hi
    rw [mem_product] at hi
    obtain ⟨hl, hℓ⟩ := hi
    have hl' : CrossPath hc w l := (mem_filter.mp hl).2
    have hℓ' : ℓ₀ = x ∨ ℓ₀ = y := by simpa using hℓ
    obtain ⟨_, hnd, _, _, _⟩ := chainOf_props hl'
    have hpresc : ∀ z ∈ chainOf l, (presc (A := A) M x y l ℓ₀ z).card ≤ 1 := by
      intro z _
      unfold presc
      have hfil : ∀ t, (t = x ∨ t = y) → ((A z.2).filter (fun a => M z.2 a = t)).card ≤ 1 := by
        intro t ht
        refine card_le_one.mpr fun a ha a' ha' => ?_
        rw [mem_filter] at ha ha'
        exact hK z.2 a a' ha.1 ha'.1 (ha.2.trans ha'.2.symm) (by rcases ht with rfl | rfl <;>
          rw [ha.2] <;> assumption)
      split_ifs
      · exact hfil _ (oth_mem hℓ')
      · exact hfil _ (oth_mem (lab_mem hℓ' _))
      · simp
    have hprod := C.card_prescribed_mul_le (slab_match hK) slab_irrefl (chainOf l) hnd
      (presc (A := A) M x y l ℓ₀) hpresc
    have heq : C.Ω.filter (Event (A := A) M x y l ℓ₀) =
        C.Ω.filter (fun f => ∀ z ∈ chainOf l, f z ∈ presc (A := A) M x y l ℓ₀ z) := by
      ext f; simp only [mem_filter, Event]
    obtain ⟨hW0, hW1⟩ := hW l hl
    have hq : ((C.Ω.filter (Event (A := A) M x y l ℓ₀)).card : ℚ) * C.chainProd (chainOf l)
        ≤ C.Ω.card := by
      rw [heq]; exact_mod_cast hprod
    rw [le_div_iff₀ hW0]
    calc ((C.Ω.filter (Event (A := A) M x y l ℓ₀)).card : ℚ) * W l.length
        ≤ ((C.Ω.filter (Event (A := A) M x y l ℓ₀)).card : ℚ) * C.chainProd (chainOf l) :=
          mul_le_mul_of_nonneg_left hW1 (by positivity)
      _ ≤ _ := hq
  calc ((C.Ω.filter (Bad hc M w x y)).card : ℚ)
      ≤ ∑ i ∈ I, ((C.Ω.filter (Event (A := A) M x y i.1 i.2)).card : ℚ) := by
        exact_mod_cast le_trans (card_le_card hsub) card_biUnion_le
    _ ≤ ∑ i ∈ I, (C.Ω.card : ℚ) / W i.1.length := sum_le_sum hone
    _ = ∑ l ∈ crossPaths (m := m) hc w, ∑ _ℓ ∈ ({x, y} : Finset ℕ),
          (C.Ω.card : ℚ) / W l.length := sum_product _ _ _
    _ = _ := by
        rw [mul_sum]
        refine sum_congr rfl fun l _ => ?_
        rw [sum_const, card_pair hxy]
        simp only [nsmul_eq_mul]
        ring

/-- The chain weights at `k = 9`: `1260` for two cells, `5 · 6^{L+1}` otherwise. -/
def W9 (L : ℕ) : ℚ := if L = 2 then 1260 else 5 * 6 ^ (L + 1)

theorem W9_le {hc : 1 ≤ c} {w : ℕ} (hA : ∀ v, (A v).card = 9) :
    ∀ l ∈ crossPaths (m := m) hc w,
      0 < W9 l.length ∧ W9 l.length ≤ (slab c m 9 P A M).chainProd (chainOf l) := by
  intro l hl
  have hl' : CrossPath hc w l := (mem_filter.mp hl).2
  refine ⟨by unfold W9; split_ifs <;> positivity, ?_⟩
  unfold W9
  split_ifs with h2
  · have := chainProd_two (P := P) (M := M) (by norm_num) hA hl' h2
    norm_num at this
    exact_mod_cast this
  · obtain ⟨hne, hnd, hch, hlen, hcol⟩ := chainOf_props hl'
    have hD : ∀ z ∈ chainOf l, ((slab c m 9 P A M).D z).card = 9 := by
      intro z hz
      by_cases h1 : z.1.val = 1
      · rw [slab_D_one h1, hA]
      · rw [slab_D_fut (by have := hcol z hz; omega), card_range]
    have hge := chainProd_ge (P := P) (A := A) (M := M) (by norm_num) (chainOf l) hne hnd hch hD
    rw [hlen, show l.length + 2 - 1 = l.length + 1 by omega] at hge
    norm_num at hge
    have := (Nat.cast_le (α := ℚ)).mpr hge
    push_cast at this
    linarith

end GridGen.Gauge
