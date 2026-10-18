/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Nine.Bad9

/-!
# The bad event of a move through a hole

A crossing path of two cells is `(2, w+1), (2, w)`. Its prescribed event for the first label `ℓ₀`
asks for a colour of row `w + 1` keyed `oth ℓ₀` and a colour of row `w` keyed `ℓ₀`. If one of the
move's labels is a *hole* — no colour of row `w` or row `w + 1` carries it as a key — one of the two
phases is impossible. The two-cell term of the bad event then counts once, not twice
(`card_bad_le_hole`).
-/

open Finset
open scoped Classical

set_option linter.unusedSectionVars false

namespace GridGen.Gauge

variable {c m k : ℕ} {P A : Fin m → Finset ℕ} {M : Fin m → ℕ → ℕ}

/-- One of the labels `x, y` is a hole of row `w` or of row `w + 1`. -/
def HoleAt (A : Fin m → Finset ℕ) (M : Fin m → ℕ → ℕ) (w x y : ℕ) : Prop :=
  ∀ h : w + 1 < m,
    (∀ a ∈ A ⟨w, by omega⟩, M ⟨w, by omega⟩ a ≠ x) ∨ (∀ a ∈ A ⟨w, by omega⟩, M ⟨w, by omega⟩ a ≠ y) ∨
      (∀ a ∈ A ⟨w + 1, h⟩, M ⟨w + 1, h⟩ a ≠ x) ∨ (∀ a ∈ A ⟨w + 1, h⟩, M ⟨w + 1, h⟩ a ≠ y)

/-- A two-cell crossing path. -/
theorem two_cell {hc : 1 ≤ c} {w : ℕ} {l : List (Cell c m)} (hl : CrossPath hc w l)
    (hlen : l.length = 2) : ∃ (h : w + 1 < m),
      l = [(fut0 hc, ⟨w + 1, h⟩), (fut0 hc, ⟨w, Nat.lt_of_succ_lt h⟩)] := by
  obtain ⟨_, hch, _, ⟨v₁, hw₁, h1⟩, ⟨v₂, hw₂, h2⟩⟩ := hl
  obtain ⟨a, b, rfl⟩ : ∃ a b, l = [a, b] := by
    match l, hlen with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  simp only [List.head?_cons, Option.some.injEq] at h1
  simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at h2
  subst h1; subst h2
  have hadj : slabAdj (fut0 hc, v₁) (fut0 hc, v₂) := by
    rw [List.isChain_cons_cons] at hch; exact hch.1
  have hv : v₂.val + 1 = v₁.val := by unfold slabAdj at hadj; simp at hadj; omega
  have e2 : v₂.val = w := by omega
  refine ⟨by have := v₁.isLt; omega, ?_⟩
  simp only [List.cons.injEq, Prod.mk.injEq, true_and, and_true]
  exact ⟨Fin.ext (by simp; omega), Fin.ext (by simp; omega)⟩

/-- Through a hole, one phase of the two-cell event is empty. -/
theorem event_two_empty {hc : 1 ≤ c} {w x y : ℕ} (hxy : x ≠ y) (hhole : HoleAt A M w x y)
    {l : List (Cell c m)} (hl : CrossPath hc w l) (hlen : l.length = 2) :
    ∃ ℓ₁ ∈ ({x, y} : Finset ℕ), ∀ f : Cell c m → ℕ, ¬ Event (A := A) M x y l ℓ₁ f := by
  obtain ⟨h, hl2⟩ := two_cell hl hlen
  rw [hl2]
  have hcol1 : ((1 : Fin (c + 2))).val = 1 := Fin.val_one _
  -- the two seam conditions of the event
  have key : ∀ ℓ₀ f, Event (A := A) M x y [(fut0 hc, ⟨w + 1, h⟩),
      (fut0 hc, ⟨w, Nat.lt_of_succ_lt h⟩)] ℓ₀ f →
      (∃ a ∈ A ⟨w + 1, h⟩, M ⟨w + 1, h⟩ a = oth x y ℓ₀) ∧
        (∃ a ∈ A ⟨w, Nat.lt_of_succ_lt h⟩, M ⟨w, Nat.lt_of_succ_lt h⟩ a =
          oth x y (lab x y ℓ₀ 1)) := by
    intro ℓ₀ f he
    have hc1 := he (1, ⟨w + 1, h⟩) (by simp [chainOf, seamOf])
    have hc2 := he (1, ⟨w, Nat.lt_of_succ_lt h⟩) (by simp [chainOf, seamOf])
    unfold presc at hc1 hc2
    rw [ite_eq_left hcol1, ite_eq_left (by simp), mem_filter] at hc1
    rw [ite_eq_left hcol1, ite_eq_right (by simp), mem_filter] at hc2
    exact ⟨⟨_, hc1.1, hc1.2⟩, ⟨_, hc2.1, hc2.2⟩⟩
  have hl1 : ∀ ℓ₀, ℓ₀ = x ∨ ℓ₀ = y → oth x y (lab x y ℓ₀ 1) = ℓ₀ := by
    intro ℓ₀ hℓ; unfold lab; rw [ite_eq_right (by omega)]; exact oth_oth hxy hℓ
  have othx : oth x y x = y := by simp [oth]
  have othy : oth x y y = x := by simp [oth, Ne.symm hxy]
  rcases hhole h with ht | ht | ht | ht
  · refine ⟨x, by simp, fun f he => ?_⟩
    obtain ⟨-, a, ha, e⟩ := key x f he
    rw [hl1 x (Or.inl rfl)] at e; exact ht a ha e
  · refine ⟨y, by simp, fun f he => ?_⟩
    obtain ⟨-, a, ha, e⟩ := key y f he
    rw [hl1 y (Or.inr rfl)] at e; exact ht a ha e
  · refine ⟨y, by simp, fun f he => ?_⟩
    obtain ⟨⟨a, ha, e⟩, -⟩ := key y f he
    rw [othy] at e; exact ht a ha e
  · refine ⟨x, by simp, fun f he => ?_⟩
    obtain ⟨⟨a, ha, e⟩, -⟩ := key x f he
    rw [othx] at e; exact ht a ha e

/-- **The bad event through a hole**, with per-length chain weights: two-cell paths count once. -/
theorem card_bad_le_hole {hc : 1 ≤ c} {w x y : ℕ} (hK : KeyInj k A M)
    (hxy : x ≠ y) (hx : x < k) (hy : y < k) (hhole : HoleAt A M w x y) (W : ℕ → ℚ)
    (hW : ∀ l ∈ crossPaths (m := m) hc w,
      0 < W l.length ∧ W l.length ≤ (slab c m k P A M).chainProd (chainOf l)) :
    (((slab c m k P A M).Ω.filter (Bad hc M w x y)).card : ℚ) ≤
      (slab c m k P A M).Ω.card * ∑ l ∈ crossPaths (m := m) hc w,
        (if l.length = 2 then 1 else 2) / W l.length := by
  set C := slab c m k P A M
  set I := crossPaths (m := m) hc w ×ˢ ({x, y} : Finset ℕ)
  have hsub : C.Ω.filter (Bad hc M w x y) ⊆
      I.biUnion (fun i => C.Ω.filter (Event (A := A) M x y i.1 i.2)) := by
    intro f hf
    rw [mem_filter, CSP.mem_Ω] at hf
    obtain ⟨l, hl, ℓ₀, hℓ, he⟩ := bad_event (P := P) hxy hf.1 hf.2
    rw [mem_biUnion]
    exact ⟨(l, ℓ₀), mem_product.mpr ⟨hl, hℓ⟩, mem_filter.mpr ⟨(CSP.mem_Ω _).mpr hf.1, he⟩⟩
  have hone : ∀ l ∈ crossPaths (m := m) hc w, ∀ ℓ₀ ∈ ({x, y} : Finset ℕ),
      ((C.Ω.filter (Event (A := A) M x y l ℓ₀)).card : ℚ) ≤ C.Ω.card / W l.length := by
    intro l hl ℓ₀ hℓ
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
  have hpair : ∀ l ∈ crossPaths (m := m) hc w,
      ∑ ℓ₀ ∈ ({x, y} : Finset ℕ), ((C.Ω.filter (Event (A := A) M x y l ℓ₀)).card : ℚ) ≤
        C.Ω.card * ((if l.length = 2 then 1 else 2) / W l.length) := by
    intro l hl
    have hW0 := (hW l hl).1
    by_cases h2 : l.length = 2
    · rw [ite_eq_left h2]
      obtain ⟨ℓ₁, hℓ₁, hempty⟩ := event_two_empty hxy hhole (mem_filter.mp hl).2 h2
      have h0 : (C.Ω.filter (Event (A := A) M x y l ℓ₁)) = ∅ :=
        filter_eq_empty_iff.mpr fun f _ => hempty f
      rw [← add_sum_erase _ _ hℓ₁, h0, card_empty, Nat.cast_zero, zero_add]
      have hrest : ({x, y} : Finset ℕ).erase ℓ₁ = {if ℓ₁ = x then y else x} := by
        have : ℓ₁ = x ∨ ℓ₁ = y := by simpa using hℓ₁
        rcases this with rfl | rfl
        · rw [ite_eq_left rfl, erase_insert (by simpa using hxy)]
        · rw [ite_eq_right (Ne.symm hxy), pair_comm, erase_insert (by simpa using Ne.symm hxy)]
      rw [hrest, sum_singleton]
      have := hone l hl (if ℓ₁ = x then y else x) (by split_ifs <;> simp)
      rw [mul_one_div]
      exact this
    · rw [ite_eq_right h2, sum_pair hxy]
      have h1 := hone l hl x (by simp)
      have h2' := hone l hl y (by simp)
      calc ((C.Ω.filter (Event (A := A) M x y l x)).card : ℚ) +
            (C.Ω.filter (Event (A := A) M x y l y)).card
          ≤ C.Ω.card / W l.length + C.Ω.card / W l.length := add_le_add h1 h2'
        _ = _ := by ring
  calc ((C.Ω.filter (Bad hc M w x y)).card : ℚ)
      ≤ ∑ i ∈ I, ((C.Ω.filter (Event (A := A) M x y i.1 i.2)).card : ℚ) := by
        exact_mod_cast le_trans (card_le_card hsub) card_biUnion_le
    _ = ∑ l ∈ crossPaths (m := m) hc w, ∑ ℓ₀ ∈ ({x, y} : Finset ℕ),
          ((C.Ω.filter (Event (A := A) M x y l ℓ₀)).card : ℚ) := sum_product _ _ _
    _ ≤ ∑ l ∈ crossPaths (m := m) hc w, C.Ω.card * ((if l.length = 2 then 1 else 2) / W l.length) :=
        sum_le_sum hpair
    _ = _ := by rw [mul_sum]

end GridGen.Gauge
