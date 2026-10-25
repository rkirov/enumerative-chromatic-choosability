/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Seam
import GridGen.Main

/-!
# The gauges of a chain of columns

The gauge telescope runs along a chain of columns of `k`-lists. Column `j` carries a vertically
consistent labelling `gauge j`, built from `gauge (j-1)` by `tilde` and `glueLab`. This file
builds the gauges (`gauge_props`), pulls label states back along them (`surj_of_rowLab`), and
writes the slab sums of a seam as slab counts (`slab_sum`, `freshP`). The telescope itself, with
the relaxation potential, is `Eight/Main8.lean`.
-/

open Finset SimpleGraph ListColoring
open scoped Classical SimpleGraph

set_option linter.unusedSectionVars false

namespace GridGen.Gauge

variable {m k : ℕ}

/-! ### Pulling uniform states back along a labelling -/

/-- If every state of `U` is the key image of a state of `T`, the `T`-sum dominates. -/
theorem sum_le_of_preimage {U T : Finset (State (Fin m))} (G : State (Fin m) → ℕ)
    (key : State (Fin m) → State (Fin m)) (h : ∀ u ∈ U, ∃ t ∈ T, key t = u) :
    ∑ u ∈ U, G u ≤ ∑ t ∈ T, G (key t) := by
  choose! φ hφT hφ using h
  have hinj : Set.InjOn φ U := fun u hu u' hu' e => by rw [← hφ u hu, ← hφ u' hu', e]
  calc ∑ u ∈ U, G u = ∑ u ∈ U, G (key (φ u)) := sum_congr rfl fun u hu => by rw [hφ u hu]
    _ = ∑ t ∈ U.image φ, G (key t) := (sum_image (f := fun t => G (key t)) hinj).symm
    _ ≤ ∑ t ∈ T, G (key t) :=
        sum_le_sum_of_subset_of_nonneg (fun t ht => by
          obtain ⟨u, hu, rfl⟩ := mem_image.mp ht; exact hφT u hu) fun _ _ _ => Nat.zero_le _

/-- A labelling that is injective with labels below `k` on `k`-lists is onto `{0, …, k-1}`. -/
theorem surj_of_rowLab {X : Fin m → Finset ℕ} (hX : ∀ v, (X v).card = k) {g : ℕ → ℕ → ℕ}
    (hR : RowLab k (extR X) g) (v : Fin m) {ℓ : ℕ} (hℓ : ℓ < k) : ∃ a ∈ X v, g v.val a = ℓ := by
  have hR' := hR v.val
  rw [extR_val] at hR'
  have hsub : (X v).image (g v.val) ⊆ range k := fun z hz => by
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hz; exact mem_range.mpr (hR'.2 a ha)
  have hc : ((X v).image (g v.val)).card = k := by rw [card_image_of_injOn hR'.1, hX]
  have heq := eq_of_subset_of_card_le hsub (by rw [hc, card_range])
  have : ℓ ∈ (X v).image (g v.val) := by rw [heq]; exact mem_range.mpr hℓ
  obtain ⟨a, ha, e⟩ := mem_image.mp this
  exact ⟨a, ha, e⟩

/-! ### The gauges of a chain of columns -/

/-- A first row labelling: the position of a colour in its list. -/
noncomputable def initLab (Bx : ℕ → Finset ℕ) (v a : ℕ) : ℕ :=
  if h : a ∈ Bx v then (((Bx v).equivFin ⟨a, h⟩ : Fin (Bx v).card) : ℕ) else 0

theorem rowLab_initLab {Bx : ℕ → Finset ℕ} (hB : ∀ v, (Bx v).card ≤ k) :
    RowLab k Bx (initLab Bx) := by
  intro v
  refine ⟨fun a ha a' ha' e => ?_, fun a ha => ?_⟩
  · rw [Finset.mem_coe] at ha ha'
    unfold initLab at e
    rw [dite_eq_left ha, dite_eq_left ha'] at e
    have := (Bx v).equivFin.injective (Fin.ext e)
    exact congrArg Subtype.val this
  · unfold initLab; rw [dite_eq_left ha]
    exact lt_of_lt_of_le (Fin.isLt _) (hB v)

/-- The gauge of column `j`. -/
noncomputable def gauge (k : ℕ) (L : Cols (Fin m)) : ℕ → ℕ → ℕ → ℕ
  | 0 => glueLab k (extR (L 0)) (initLab (extR (L 0)))
  | j + 1 => glueLab k (extR (L (j + 1))) (tilde (extR (L j)) (extR (L (j + 1))) (gauge k L j))

theorem extR_card_le {X : Fin m → Finset ℕ} (hX : ∀ v, (X v).card = k) (v : ℕ) :
    (extR X v).card ≤ k := by
  unfold extR; split_ifs with h
  · rw [hX]
  · simp

theorem extR_card_eq {X Y : Fin m → Finset ℕ} (hX : ∀ v, (X v).card = k)
    (hY : ∀ v, (Y v).card = k) (v : ℕ) : (extR X v).card = (extR Y v).card := by
  unfold extR; split_ifs with h
  · rw [hX, hY]
  · rfl

/-- **The gauges are row labellings and vertically consistent.** -/
theorem gauge_props {L : Cols (Fin m)} (hL : IsKCols k L) : ∀ j,
    RowLab k (extR (L j)) (gauge k L j) ∧
      ∀ v, ∀ c ∈ extR (L j) v ∩ extR (L j) (v + 1), gauge k L j (v + 1) c = gauge k L j v c := by
  intro j
  have glue_props : ∀ {Bx : ℕ → Finset ℕ} {βx : ℕ → ℕ → ℕ}, RowLab k Bx βx →
      RowLab k Bx (glueLab k Bx βx) ∧
        ∀ v, ∀ c ∈ Bx v ∩ Bx (v + 1), glueLab k Bx βx (v + 1) c = glueLab k Bx βx v c :=
    fun hR => ⟨fun v => ⟨glueLab_injOn hR v, fun a ha => glueLab_lt hR v ha⟩,
      fun v c hc => glueLab_vc hR v hc⟩
  induction j with
  | zero => exact glue_props (rowLab_initLab (extR_card_le (hL 0)))
  | succ j ih =>
      refine glue_props (rowLab_tilde (extR_card_eq (hL j) (hL (j + 1))) fun v => ?_)
      exact ⟨(ih.1 v).1, (ih.1 v).2⟩

/-! ### The slab sums of a seam -/

section Seam

/-- The states of a column compatible with `r`: the lists with `r`'s colours removed. -/
theorem filter_compat_states (X : Fin m → Finset ℕ) (r : State (Fin m)) :
    (states (rowG m) X).filter (Compat r) = states (rowG m) (fun v => (X v).erase (r v)) := by
  ext p
  simp only [mem_filter, mem_states, mem_erase, Compat]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨fun v => ⟨fun e => h3 v e.symm, h1 v⟩, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨fun v => (h1 v).2, h2⟩, fun v e => (h1 v).1 e.symm⟩

/-- The slab sums. -/
theorem slab_sum (P A : Fin m → Finset ℕ) (M : Fin m → ℕ → ℕ) (c : ℕ) :
    ∑ p ∈ states (rowG m) P, ∑ s ∈ (states (rowG m) A).filter (Compat p),
      F (rowG m) k c (keyed M s) = Z c m k P A M := (card_Ω_eq).symm

/-- The fresh past column of the first seam: one colour per row, above every list colour. -/
noncomputable def freshP (L : Cols (Fin m)) : Fin m → Finset ℕ :=
  fun v => {((univ : Finset (Fin m)).biUnion (L 0)).sup id + 1 + v.val % 2}

theorem lt_fresh {L : Cols (Fin m)} {v : Fin m} {a : ℕ} (ha : a ∈ L 0 v) :
    a < ((univ : Finset (Fin m)).biUnion (L 0)).sup id + 1 := by
  have : a ≤ ((univ : Finset (Fin m)).biUnion (L 0)).sup id :=
    le_sup (f := id) (mem_biUnion.mpr ⟨v, mem_univ _, ha⟩)
  omega

theorem states_freshP (L : Cols (Fin m)) :
    states (rowG m) (freshP L) =
      {fun v => ((univ : Finset (Fin m)).biUnion (L 0)).sup id + 1 + v.val % 2} := by
  ext p
  rw [mem_states, mem_singleton]
  simp only [freshP, mem_singleton]
  constructor
  · rintro ⟨h, _⟩; funext v; exact h v
  · rintro rfl
    refine ⟨fun v => rfl, fun v v' hvv' e => ?_⟩
    rcases hvv' with h | h <;> simp only at e <;> omega

end Seam

end GridGen.Gauge
