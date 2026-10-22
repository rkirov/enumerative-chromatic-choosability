/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Seven.AbsChain7
import GridGen.Gauge.Seven.Counts7

/-!
# The bad set of a move through a hole

A move `(x, y)` at the edge below row `w` loses at most its bad set. A bad solution realizes the
event of a chordless crossing path (`bad_event_chordless`). Split the paths:

* **H**, the hole `h` in row `w + 1`: paths with their head at row `w + 1` are *absorbed*. Their
  phase `oth h` is empty (`event_head_hole`), and the phase `h` is compared with the hit event of
  the deleted star of row `w + 1`. The other paths are *residual*: both phases are compared with
  the whole count.
* **D**, the hole in row `w`: the same with the last cell at row `w`.

`bad_le_H` and `bad_le_D` give the bad set as such sums over paths.
-/

open Finset
open scoped Classical

set_option linter.unusedSectionVars false

namespace GridGen.Gauge

variable {c m : ℕ} {P A : Fin m → Finset ℕ} {M : Fin m → ℕ → ℕ}

/-- **The chain bound for one path and phase**, at `k = 7`. -/
theorem event_chain_le (hK : KeyInj 7 A M) (hA : ∀ v, (A v).card = 7) (hc : 1 ≤ c)
    {w x y ℓ₀ : ℕ} (hx : x < 7) (hy : y < 7) (hℓ : ℓ₀ = x ∨ ℓ₀ = y) {l : List (Cell c m)}
    (hl : CrossPath hc w l) :
    ((slab c m 7 P A M).Ω.filter (Event (A := A) M x y l ℓ₀)).card * (4 ^ (l.length + 1) * 3) ≤
      (slab c m 7 P A M).Ω.card := by
  obtain ⟨hne, hnd, hch, hlen, hcol⟩ := chainOf_props hl
  have hprod := (slab c m 7 P A M).card_prescribed_mul_le (slab_match hK) slab_irrefl (chainOf l) hnd
    (presc (A := A) M x y l ℓ₀) (fun z _ => presc_card_le hK hx hy l hℓ z)
  have hge := chainProd_ge (P := P) (A := A) (M := M) (k := 7) (by omega) (chainOf l) hne hnd hch
    (fun z hz => cell_card_seven hA (hcol z hz))
  rw [hlen, show l.length + 2 - 1 = l.length + 1 by omega] at hge
  have heq : (slab c m 7 P A M).Ω.filter (Event (A := A) M x y l ℓ₀) =
      (slab c m 7 P A M).Ω.filter (fun f => ∀ z ∈ chainOf l, f z ∈ presc (A := A) M x y l ℓ₀ z) := by
    ext f; simp only [mem_filter, Event]
  rw [heq]
  exact le_trans (Nat.mul_le_mul_left _ (by simpa using hge)) hprod

theorem headRow_of_head {hc : 1 ≤ c} {l : List (Cell c m)} {v : Fin m}
    (h : l.head? = some (fut0 hc, v)) : headRow l = v.val := by
  simp [headRow, h]

theorem lastRow_of_last {hc : 1 ≤ c} {l : List (Cell c m)} {v : Fin m}
    (h : l.getLast? = some (fut0 hc, v)) : lastRow l = v.val := by
  simp [lastRow, h]

/-- The bad set is covered by the events of chordless crossing paths, both phases. -/
theorem bad_subset (hc : 1 ≤ c) {w x y : ℕ} (hxy : x ≠ y) :
    (slab c m 7 P A M).Ω.filter (Bad hc M w x y) ⊆
      (((crossPaths hc w).filter Chordless) ×ˢ ({x, y} : Finset ℕ)).biUnion
        (fun i => (slab c m 7 P A M).Ω.filter (Event (A := A) M x y i.1 i.2)) := by
  intro f hf
  rw [mem_filter, CSP.mem_Ω] at hf
  obtain ⟨l, hl, hch, ℓ₀, hℓ, he⟩ := bad_event_chordless (P := P) hxy hf.1 hf.2
  rw [mem_biUnion]
  exact ⟨(l, ℓ₀), mem_product.mpr ⟨mem_filter.mpr ⟨hl, hch⟩, hℓ⟩,
    mem_filter.mpr ⟨(CSP.mem_Ω _).mpr hf.1, he⟩⟩

/-- **The bad set, split at the hole row** (H: the hole in row `w + 1`). -/
theorem bad_le_H (hc : 1 ≤ c) {w x y h : ℕ} (hxy : x ≠ y) (hh : h = x ∨ h = y) (hw : w + 1 < m)
    (hhole : ∀ a ∈ A ⟨w + 1, hw⟩, M ⟨w + 1, hw⟩ a ≠ h) :
    (((slab c m 7 P A M).Ω.filter (Bad hc M w x y)).card : ℚ) ≤
      ∑ l ∈ (crossPaths hc w).filter (fun l => Chordless l ∧ headRow l = w + 1),
          (((slab c m 7 P A M).Ω.filter (Event (A := A) M x y l h)).card : ℚ) +
        ∑ l ∈ (crossPaths hc w).filter (fun l => Chordless l ∧ w + 2 ≤ headRow l),
          ∑ ℓ₀ ∈ ({x, y} : Finset ℕ),
            (((slab c m 7 P A M).Ω.filter (Event (A := A) M x y l ℓ₀)).card : ℚ) := by
  set C := slab c m 7 P A M
  set S := (crossPaths hc w).filter Chordless
  set SA := (crossPaths hc w).filter (fun l => Chordless l ∧ headRow l = w + 1)
  set SR := (crossPaths hc w).filter (fun l => Chordless l ∧ w + 2 ≤ headRow l)
  have h1 := card_le_card (bad_subset (P := P) (A := A) (M := M) hc (w := w) hxy)
  have h2 := card_biUnion_le (s := S ×ˢ ({x, y} : Finset ℕ))
    (t := fun i => C.Ω.filter (Event (A := A) M x y i.1 i.2))
  have h3 : ((C.Ω.filter (Bad hc M w x y)).card : ℚ) ≤
      ∑ l ∈ S, ∑ ℓ₀ ∈ ({x, y} : Finset ℕ), ((C.Ω.filter (Event (A := A) M x y l ℓ₀)).card : ℚ) := by
    rw [← sum_product']; exact_mod_cast le_trans h1 h2
  -- every chordless crossing path has its head at row `w + 1` or below
  have hsplit : S = SA ∪ SR := by
    ext l
    simp only [S, SA, SR, mem_filter, mem_union]
    constructor
    · rintro ⟨hl, hch⟩
      obtain ⟨-, -, -, ⟨v₁, hw₁, h1⟩, -⟩ := (mem_filter.mp hl).2
      rw [headRow_of_head h1]
      by_cases e : v₁.val = w + 1
      · exact Or.inl ⟨hl, hch, e⟩
      · exact Or.inr ⟨hl, hch, by omega⟩
    · rintro (⟨hl, hch, -⟩ | ⟨hl, hch, -⟩) <;> exact ⟨hl, hch⟩
  have hdisj : Disjoint SA SR := by
    rw [disjoint_filter]; intro l _ h1 h2; omega
  rw [hsplit, sum_union hdisj] at h3
  refine le_trans h3 (add_le_add (sum_le_sum fun l hl => ?_) le_rfl)
  -- absorbed paths: only the phase `h`
  obtain ⟨hlc, hch, hrow⟩ := mem_filter.mp hl
  obtain ⟨-, -, -, ⟨v₁, hw₁, h1⟩, -⟩ := (mem_filter.mp hlc).2
  have hv : v₁ = ⟨w + 1, hw⟩ := Fin.ext (by rw [headRow_of_head h1] at hrow; exact hrow)
  subst hv
  have hempty : C.Ω.filter (Event (A := A) M x y l (oth x y h)) = ∅ :=
    filter_eq_empty_iff.mpr fun f _ => event_head_hole hxy hh h1 hhole f
  have hpair : ({x, y} : Finset ℕ) = {h, oth x y h} := by
    rcases hh with rfl | rfl
    · simp [oth]
    · simp [oth, Ne.symm hxy, pair_comm]
  rw [hpair, sum_pair (by unfold oth; split_ifs <;> simp_all), hempty, card_empty, Nat.cast_zero,
    add_zero]

/-- **The bad set, split at the hole row** (D: the hole in row `w`). -/
theorem bad_le_D (hc : 1 ≤ c) {w x y h : ℕ} (hxy : x ≠ y) (hh : h = x ∨ h = y) (hw : w < m)
    (hhole : ∀ a ∈ A ⟨w, hw⟩, M ⟨w, hw⟩ a ≠ h) :
    (((slab c m 7 P A M).Ω.filter (Bad hc M w x y)).card : ℚ) ≤
      ∑ l ∈ (crossPaths hc w).filter (fun l => Chordless l ∧ lastRow l = w),
          ∑ ℓ₀ ∈ ({x, y} : Finset ℕ).filter (fun ℓ₀ => lab x y ℓ₀ (l.length - 1) = h),
            (((slab c m 7 P A M).Ω.filter (Event (A := A) M x y l ℓ₀)).card : ℚ) +
        ∑ l ∈ (crossPaths hc w).filter (fun l => Chordless l ∧ lastRow l + 1 ≤ w),
          ∑ ℓ₀ ∈ ({x, y} : Finset ℕ),
            (((slab c m 7 P A M).Ω.filter (Event (A := A) M x y l ℓ₀)).card : ℚ) := by
  set C := slab c m 7 P A M
  set S := (crossPaths hc w).filter Chordless
  set SA := (crossPaths hc w).filter (fun l => Chordless l ∧ lastRow l = w)
  set SR := (crossPaths hc w).filter (fun l => Chordless l ∧ lastRow l + 1 ≤ w)
  have h1 := card_le_card (bad_subset (P := P) (A := A) (M := M) hc (w := w) hxy)
  have h2 := card_biUnion_le (s := S ×ˢ ({x, y} : Finset ℕ))
    (t := fun i => C.Ω.filter (Event (A := A) M x y i.1 i.2))
  have h3 : ((C.Ω.filter (Bad hc M w x y)).card : ℚ) ≤
      ∑ l ∈ S, ∑ ℓ₀ ∈ ({x, y} : Finset ℕ), ((C.Ω.filter (Event (A := A) M x y l ℓ₀)).card : ℚ) := by
    rw [← sum_product']; exact_mod_cast le_trans h1 h2
  have hsplit : S = SA ∪ SR := by
    ext l
    simp only [S, SA, SR, mem_filter, mem_union]
    constructor
    · rintro ⟨hl, hch⟩
      obtain ⟨-, -, -, -, ⟨v₂, hw₂, h2⟩⟩ := (mem_filter.mp hl).2
      rw [lastRow_of_last h2]
      by_cases e : v₂.val = w
      · exact Or.inl ⟨hl, hch, e⟩
      · exact Or.inr ⟨hl, hch, by omega⟩
    · rintro (⟨hl, hch, -⟩ | ⟨hl, hch, -⟩) <;> exact ⟨hl, hch⟩
  have hdisj : Disjoint SA SR := by
    rw [disjoint_filter]; intro l _ h1 h2; omega
  rw [hsplit, sum_union hdisj] at h3
  refine le_trans h3 (add_le_add (sum_le_sum fun l hl => ?_) le_rfl)
  obtain ⟨hlc, hch, hrow⟩ := mem_filter.mp hl
  obtain ⟨-, -, -, ⟨v₁, hw₁, h1⟩, ⟨v₂, hw₂, h2⟩⟩ := (mem_filter.mp hlc).2
  have hv : v₂ = ⟨w, hw⟩ := Fin.ext (by rw [lastRow_of_last h2] at hrow; exact hrow)
  subst hv
  have hv12 : v₁ ≠ ⟨w, hw⟩ := fun e => by rw [e] at hw₁; simp at hw₁
  rw [← sum_filter_add_sum_filter_not ({x, y} : Finset ℕ) (fun ℓ₀ => lab x y ℓ₀ (l.length - 1) = h)]
  have hzero : ∑ ℓ₀ ∈ ({x, y} : Finset ℕ).filter (fun ℓ₀ => ¬ lab x y ℓ₀ (l.length - 1) = h),
      ((C.Ω.filter (Event (A := A) M x y l ℓ₀)).card : ℚ) = 0 := by
    refine sum_eq_zero fun ℓ₀ hℓ₀ => ?_
    rw [mem_filter] at hℓ₀
    have hℓ : ℓ₀ = x ∨ ℓ₀ = y := by simpa using hℓ₀.1
    have hlab : lab x y ℓ₀ (l.length - 1) = oth x y h :=
      eq_oth hxy hh (lab_mem hℓ _) hℓ₀.2
    have : C.Ω.filter (Event (A := A) M x y l ℓ₀) = ∅ :=
      filter_eq_empty_iff.mpr fun f _ => event_last_hole hxy hh hv12 h1 h2 hhole hlab f
    rw [this, card_empty, Nat.cast_zero]
  rw [hzero, add_zero]

end GridGen.Gauge
