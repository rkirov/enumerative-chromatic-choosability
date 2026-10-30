/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Six.Cone

/-!
# Height six: rows by index, admissible colours, and row reflection

`GridGen/Five/Small5/Fibre.lean` with six rows. `setAt i t x` overwrites row `i` (rows numbered
from `0`, `rowAt` of `GridGen/Six/PatCount.lean`), and `optsAt X i t` is the set of colours row
`i` may take given the other rows: its list minus the colours of its neighbours (`optsAt_cur`,
`optsAt_mem`). These feed the sharp fibre bound `Lookback.fibre_row_sharp`
(`GridGen/Six/Peel.lean`).

**Reflection.** Reversing the rows maps the proper columns of `X₁, …, X₆` onto those of
`X₆, …, X₁` and preserves the orbit (`orb_rev`, a kernel check over the canonical patterns),
hence `GU` and `GB` with reversed lists, so the seam inequality for reversed lists implies it
for the original ones (`seam_of_rev`).
-/

namespace GridGen.Six

open Finset

/-- Overwrite row `i`. -/
def setAt (i : ℕ) (t : T6) (x : ℕ) : T6 :=
  match i with
  | 0 => (x, t.2)
  | 1 => (t.1, x, t.2.2)
  | 2 => (t.1, t.2.1, x, t.2.2.2)
  | 3 => (t.1, t.2.1, t.2.2.1, x, t.2.2.2.2)
  | 4 => (t.1, t.2.1, t.2.2.1, t.2.2.2.1, x, t.2.2.2.2.2)
  | _ => (t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, x)

/-- Six lists as a function of the row index. -/
def bl (B₁ B₂ B₃ B₄ B₅ B₆ : Finset ℕ) (i : ℕ) : Finset ℕ :=
  match i with
  | 0 => B₁
  | 1 => B₂
  | 2 => B₃
  | 3 => B₄
  | 4 => B₅
  | _ => B₆

/-- The admissible new colours of row `i`: its list minus the neighbouring colours. -/
def optsAt (X₁ X₂ X₃ X₄ X₅ X₆ : Finset ℕ) (i : ℕ) (t : T6) : Finset ℕ :=
  match i with
  | 0 => X₁.erase (r2 t)
  | 1 => (X₂.erase (r1 t)).erase (r3 t)
  | 2 => (X₃.erase (r2 t)).erase (r4 t)
  | 3 => (X₄.erase (r3 t)).erase (r5 t)
  | 4 => (X₅.erase (r4 t)).erase (r6 t)
  | _ => X₆.erase (r5 t)

theorem getAt_setAt (i : ℕ) (t : T6) (x : ℕ) : rowAt i (setAt i t x) = x := by
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | _ + 5 => rfl

theorem setAt_inj (i : ℕ) (t₁ t₂ : T6) (x₁ x₂ : ℕ) (he : setAt i t₁ x₁ = setAt i t₂ x₂)
    (hg : rowAt i t₁ = rowAt i t₂) : t₁ = t₂ := by
  obtain ⟨a, b, c, d, e, f⟩ := t₁
  obtain ⟨a', b', c', d', e', f'⟩ := t₂
  match i with
  | 0 => simp_all [setAt, rowAt, r1, r2, r3, r4, r5, r6]
  | 1 => simp_all [setAt, rowAt, r1, r2, r3, r4, r5, r6]
  | 2 => simp_all [setAt, rowAt, r1, r2, r3, r4, r5, r6]
  | 3 => simp_all [setAt, rowAt, r1, r2, r3, r4, r5, r6]
  | 4 => simp_all [setAt, rowAt, r1, r2, r3, r4, r5, r6]
  | _ + 5 => simp_all [setAt, rowAt, r1, r2, r3, r4, r5, r6]

theorem rowAt_setAt_ne {i j : ℕ} (hij : i ≠ j) (hi : i < 6) (hj : j < 6) (t : T6) (x : ℕ) :
    rowAt j (setAt i t x) = rowAt j t := by
  obtain ⟨a, b, c, d, e, f⟩ := t
  interval_cases i <;> interval_cases j <;> first | omega | rfl

theorem card_erase_ge (A : Finset ℕ) (a : ℕ) : A.card - 1 ≤ (A.erase a).card :=
  Finset.pred_card_le_card_erase

theorem optsAt_cur {X₁ X₂ X₃ X₄ X₅ X₆ : Finset ℕ} {i : ℕ} (hi : i < 6) {t : T6}
    (ht : t ∈ sts X₁ X₂ X₃ X₄ X₅ X₆) : rowAt i t ∈ optsAt X₁ X₂ X₃ X₄ X₅ X₆ i t := by
  rw [mem_sts] at ht
  obtain ⟨h1, h2, h3, h4, h5, h6, p1, p2, p3, p4, p5⟩ := ht
  interval_cases i <;> simp only [rowAt, optsAt, Finset.mem_erase] <;> grind

theorem optsAt_mem {X₁ X₂ X₃ X₄ X₅ X₆ : Finset ℕ} {i : ℕ} (hi : i < 6) {t : T6}
    (ht : t ∈ sts X₁ X₂ X₃ X₄ X₅ X₆) {x : ℕ} (hx : x ∈ optsAt X₁ X₂ X₃ X₄ X₅ X₆ i t) :
    setAt i t x ∈ sts X₁ X₂ X₃ X₄ X₅ X₆ := by
  obtain ⟨a, b, c, d, e, f⟩ := t
  rw [mem_sts] at ht ⊢
  interval_cases i <;>
    simp only [optsAt, setAt, Finset.mem_erase, r1, r2, r3, r4, r5, r6] at hx ht ⊢ <;> grind

/-! ### Row reflection -/

/-- Reverse the rows of a column. -/
def rev6 (t : T6) : T6 := (r6 t, r5 t, r4 t, r3 t, r2 t, r1 t)

theorem samePat_rev {s t : T6} (h : SamePat s t) : SamePat (rev6 s) (rev6 t) := by
  obtain ⟨h13, h24, h35, h46, h14, h25, h36, h15, h26, h16⟩ := h
  simp only [SamePat, rev6, r1, r2, r3, r4, r5, r6] at *
  exact ⟨eq_comm.trans (h46.trans eq_comm), eq_comm.trans (h35.trans eq_comm),
    eq_comm.trans (h24.trans eq_comm), eq_comm.trans (h13.trans eq_comm),
    eq_comm.trans (h36.trans eq_comm), eq_comm.trans (h25.trans eq_comm),
    eq_comm.trans (h14.trans eq_comm), eq_comm.trans (h26.trans eq_comm),
    eq_comm.trans (h15.trans eq_comm), eq_comm.trans (h16.trans eq_comm)⟩

theorem orb_rev_canons : ∀ c ∈ canons, orb (rev6 c) = orb c := by decide +kernel

theorem orb_rev {t : T6} (ht : Proper t) : orb (rev6 t) = orb t := by
  have hs := samePat_canon ht
  rw [orb_congr (samePat_rev hs), orb_congr hs]
  exact orb_rev_canons _ (canon_mem ht)

theorem proper_rev {t : T6} (ht : Proper t) : Proper (rev6 t) := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := ht
  exact ⟨Ne.symm p5, Ne.symm p4, Ne.symm p3, Ne.symm p2, Ne.symm p1⟩

theorem mem_sts_rev {X₁ X₂ X₃ X₄ X₅ X₆ : Finset ℕ} {t : T6} :
    rev6 t ∈ sts X₆ X₅ X₄ X₃ X₂ X₁ ↔ t ∈ sts X₁ X₂ X₃ X₄ X₅ X₆ := by
  simp only [mem_sts, rev6, r1, r2, r3, r4, r5, r6]
  grind

theorem sum_sts_rev {β : Type*} [AddCommMonoid β] (X₁ X₂ X₃ X₄ X₅ X₆ : Finset ℕ) (f : T6 → β) :
    ∑ t ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, f t = ∑ t ∈ sts X₆ X₅ X₄ X₃ X₂ X₁, f (rev6 t) := by
  refine Finset.sum_nbij' rev6 rev6 (fun t ht => ?_) (fun t ht => ?_) (fun t _ => rfl)
    (fun t _ => rfl) (fun t _ => rfl)
  · exact mem_sts_rev.mpr ht
  · exact mem_sts_rev.mpr ht

theorem G_rev (w : Wt6) (A B C D E F : Finset ℕ) : G w A B C D E F = G w F E D C B A := by
  unfold G
  rw [sum_sts_rev]
  refine Finset.sum_congr rfl fun t ht => ?_
  unfold gw
  rw [orb_rev (proper_of_mem_sts ht)]

theorem GU_rev (w : Wt6) {s : T6} (hs : Proper s) : GU 6 w (rev6 s) = GU 6 w s := by
  rw [GU_six w hs, GU_six w (proper_rev hs), orb_rev hs]

theorem GB_rev (w : Wt6) (B₁ B₂ B₃ B₄ B₅ B₆ : Finset ℕ) (s : T6) :
    GB w B₆ B₅ B₄ B₃ B₂ B₁ (rev6 s) = GB w B₁ B₂ B₃ B₄ B₅ B₆ s := by
  unfold GB
  rw [G_rev]
  rfl

/-- **Row reflection**: the seam inequality for the reversed lists gives it for the lists. -/
theorem seam_of_rev {w : Wt6} {X₁ X₂ X₃ X₄ X₅ X₆ B₁ B₂ B₃ B₄ B₅ B₆ : Finset ℕ}
    (h : ∑ s ∈ sts X₆ X₅ X₄ X₃ X₂ X₁, GU 6 w s
      ≤ ∑ s ∈ sts X₆ X₅ X₄ X₃ X₂ X₁, GB w B₆ B₅ B₄ B₃ B₂ B₁ s) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, GU 6 w s
      ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, GB w B₁ B₂ B₃ B₄ B₅ B₆ s := by
  rw [sum_sts_rev X₁, sum_sts_rev X₁ X₂ X₃ X₄ X₅ X₆ (GB w B₁ B₂ B₃ B₄ B₅ B₆)]
  have e1 : ∑ t ∈ sts X₆ X₅ X₄ X₃ X₂ X₁, GU 6 w (rev6 t) = ∑ t ∈ sts X₆ X₅ X₄ X₃ X₂ X₁, GU 6 w t :=
    Finset.sum_congr rfl fun t ht => GU_rev w (proper_of_mem_sts ht)
  have e2 : ∑ t ∈ sts X₆ X₅ X₄ X₃ X₂ X₁, GB w B₁ B₂ B₃ B₄ B₅ B₆ (rev6 t)
      = ∑ t ∈ sts X₆ X₅ X₄ X₃ X₂ X₁, GB w B₆ B₅ B₄ B₃ B₂ B₁ t :=
    Finset.sum_congr rfl fun t _ => by rw [← GB_rev w B₆ B₅ B₄ B₃ B₂ B₁ t]
  rw [e1, e2]; exact h

/-! ### Weights on the cone -/

theorem G_nonneg {w : Wt6} (hw : InCone6 w) (A B C D E F : Finset ℕ) : 0 ≤ G w A B C D E F :=
  Finset.sum_nonneg fun t _ => cone_nonneg hw _

theorem GU_nonneg {w : Wt6} (hw : InCone6 w) (s : T6) : 0 ≤ GU 6 w s := G_nonneg hw _ _ _ _ _ _

theorem GB_nonneg {w : Wt6} (hw : InCone6 w) (B₁ B₂ B₃ B₄ B₅ B₆ : Finset ℕ) (s : T6) :
    0 ≤ GB w B₁ B₂ B₃ B₄ B₅ B₆ s := G_nonneg hw _ _ _ _ _ _

end GridGen.Six
