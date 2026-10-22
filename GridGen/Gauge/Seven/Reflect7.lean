/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Seven.MoveB7

/-!
# Reflecting the rows of a slab

Reversing the rows (`rf`) maps the slab of `(P, A, M)` to the slab of the reversed data
(`rvP`, `rvM`), solution for solution. The two-cell path through rows `v + 1` and `v` reverses into
the two-cell path through the reflected rows, with the phase moved to the other end. So the box
bound of a two-cell path against a star in its head row (`AbsHBound`) gives the bound against a
star in its last row (`absD_of_absH`).
-/

open Finset
open scoped Classical

set_option linter.unusedSectionVars false

namespace GridGen.Gauge

variable {c m : ℕ}

/-- The row reflection of a cell. -/
def rf (z : Cell c m) : Cell c m := (z.1, z.2.rev)

@[simp] theorem rf_rf (z : Cell c m) : rf (rf z) = z := by simp [rf]

@[simp] theorem comp_rf_rf (g : Cell c m → ℕ) : (g ∘ rf) ∘ rf = g := by
  funext z; simp

theorem slabAdj_rf {x y : Cell c m} : slabAdj (rf x) (rf y) ↔ slabAdj x y := by
  rw [adj_iff_coords, adj_iff_coords]
  simp only [rf, Fin.val_rev]
  have := x.2.isLt; have := y.2.isLt
  omega

/-- The reversed row data. -/
def rvP (P : Fin m → Finset ℕ) : Fin m → Finset ℕ := fun v => P v.rev

/-- The reversed keys. -/
def rvM (M : Fin m → ℕ → ℕ) : Fin m → ℕ → ℕ := fun v => M v.rev

variable {k : ℕ} {P A : Fin m → Finset ℕ} {M : Fin m → ℕ → ℕ}

theorem valid_rf {g : Cell c m → ℕ} :
    (slab c m k (rvP P) (rvP A) (rvM M)).Valid g ↔ (slab c m k P A M).Valid (g ∘ rf) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun x => ?_, fun x y hxy => ?_⟩
    · have := h1 (rf x); simpa [slab, rf, rvP] using this
    · have := h2 (rf x) (rf y) (slabAdj_rf.mpr hxy); simpa [slab, rf, rvM] using this
  · rintro ⟨h1, h2⟩
    refine ⟨fun x => ?_, fun x y hxy => ?_⟩
    · have := h1 (rf x); simpa [slab, rf, rvP] using this
    · have := h2 (rf x) (rf y) (slabAdj_rf.mpr (show slabAdj x y from hxy))
      simpa [slab, rf, rvM] using this

/-- **Counts in the reflected slab.** -/
theorem card_rf (Q : (Cell c m → ℕ) → Prop) [DecidablePred Q] :
    ((slab c m k (rvP P) (rvP A) (rvM M)).Ω.filter Q).card =
      ((slab c m k P A M).Ω.filter (fun f => Q (f ∘ rf))).card := by
  refine card_nbij' (fun g => g ∘ rf) (fun f => f ∘ rf) ?_ ?_ ?_ ?_
  · intro g hg
    rw [mem_coe, mem_filter, CSP.mem_Ω] at hg ⊢
    exact ⟨valid_rf.mp hg.1, by simpa using hg.2⟩
  · intro f hf
    rw [mem_coe, mem_filter, CSP.mem_Ω] at hf ⊢
    exact ⟨valid_rf.mpr (by simpa using hf.1), hf.2⟩
  · intro g _; simp
  · intro f _; simp

theorem keyInj_rv (hK : KeyInj k A M) : KeyInj k (rvP A) (rvM M) := fun v => hK v.rev

/-! ### The two-cell event -/

theorem event_vert2_iff {hc : 1 ≤ c} {x y ℓ₀ v : ℕ} (hv : v + 1 < m) (f : Cell c m → ℕ) :
    Event (A := A) M x y (vert2 hc v hv) ℓ₀ f ↔
      (f (1, ⟨v + 1, hv⟩) ∈ A ⟨v + 1, hv⟩ ∧ M ⟨v + 1, hv⟩ (f (1, ⟨v + 1, hv⟩)) = oth x y ℓ₀) ∧
        f (fut0 hc, ⟨v + 1, hv⟩) = ℓ₀ ∧ f (fut0 hc, ⟨v, by omega⟩) = oth x y ℓ₀ ∧
          (f (1, ⟨v, by omega⟩) ∈ A ⟨v, by omega⟩ ∧
            M ⟨v, by omega⟩ (f (1, ⟨v, by omega⟩)) = oth x y (oth x y ℓ₀)) := by
  have h1 : (vert2 hc v hv).head? = some (fut0 hc, ⟨v + 1, hv⟩) := rfl
  have h2 : (vert2 hc v hv).getLast? = some (fut0 hc, ⟨v, by omega⟩) := rfl
  have hne : ((fut0 hc, ⟨v + 1, hv⟩) : Cell c m) ≠ (fut0 hc, ⟨v, by omega⟩) := by
    intro e; have := congrArg (fun z : Cell c m => z.2.val) e; simp at this
  have hne' : (⟨v, by omega⟩ : Fin m) ≠ ⟨v + 1, hv⟩ := by simp
  have hf2 : (fut0 hc).val ≠ 1 := by simp [fut0]
  have h3 : chainOf (vert2 hc v hv) =
      [(1, ⟨v + 1, hv⟩), (fut0 hc, ⟨v + 1, hv⟩), (fut0 hc, ⟨v, by omega⟩), (1, ⟨v, by omega⟩)] := by
    rw [chainOf_eq h1 h2]; rfl
  have p1 : presc (A := A) M x y (vert2 hc v hv) ℓ₀ (1, ⟨v + 1, hv⟩) =
      (A ⟨v + 1, hv⟩).filter (fun a => M ⟨v + 1, hv⟩ a = oth x y ℓ₀) := by
    unfold presc; rw [ite_eq_left (Fin.val_one _)]; simp [vert2]
  have p2 : presc (A := A) M x y (vert2 hc v hv) ℓ₀ (fut0 hc, ⟨v + 1, hv⟩) = {ℓ₀} := by
    unfold presc; rw [ite_eq_right hf2]; simp [vert2, lab]
  have p3 : presc (A := A) M x y (vert2 hc v hv) ℓ₀ (fut0 hc, ⟨v, by omega⟩) = {oth x y ℓ₀} := by
    unfold presc; rw [ite_eq_right hf2]
    simp only [vert2]
    rw [List.idxOf_cons_ne _ hne, List.idxOf_cons_self]
    simp [lab]
  have p4 : presc (A := A) M x y (vert2 hc v hv) ℓ₀ (1, ⟨v, by omega⟩) =
      (A ⟨v, by omega⟩).filter (fun a => M ⟨v, by omega⟩ a = oth x y (oth x y ℓ₀)) := by
    unfold presc
    rw [ite_eq_left (Fin.val_one _)]
    simp [vert2, lab]
  unfold Event
  rw [h3]
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true,
    p1, p2, p3, p4, mem_filter, mem_singleton]

/-! ### The reflected box bound -/

/-- The box bound of the two-cell path against a star in its head row. -/
def AbsHBound : Prop :=
  ∀ {c m : ℕ} {P A : Fin m → Finset ℕ} {M : Fin m → ℕ → ℕ}, KeyInj 7 A M →
    (∀ v, (A v).card = 7) → (∀ v a, a ∈ A v → 6 ≤ (P v).card ∨ a ∉ P v) → ∀ (hc : 1 ≤ c)
    {x y h : ℕ}, x ≠ y → x < 7 → y < 7 → (h = x ∨ h = y) → ∀ (v : ℕ) (hv : v + 1 < m),
      (∀ a ∈ A ⟨v + 1, hv⟩, M ⟨v + 1, hv⟩ a ≠ h) → ∀ {a₀ : ℕ}, a₀ ∈ A ⟨v + 1, hv⟩ →
        7 ≤ M ⟨v + 1, hv⟩ a₀ →
      ((slab c m 7 P A M).Ω.filter (Event (A := A) M x y
        (vert2 hc v hv) h)).card * 100 ≤
        13 * ((slab c m 7 P A M).Ω.filter (Hit hc ⟨v + 1, hv⟩ a₀ h)).card

/-- The box bound of the two-cell path against a star in its last row. -/
def AbsDBound : Prop :=
  ∀ {c m : ℕ} {P A : Fin m → Finset ℕ} {M : Fin m → ℕ → ℕ}, KeyInj 7 A M →
    (∀ v, (A v).card = 7) → (∀ v a, a ∈ A v → 6 ≤ (P v).card ∨ a ∉ P v) → ∀ (hc : 1 ≤ c)
    {x y h : ℕ}, x ≠ y → x < 7 → y < 7 → (h = x ∨ h = y) → ∀ (v : ℕ) (hv : v + 1 < m),
      (∀ a ∈ A ⟨v, by omega⟩, M ⟨v, by omega⟩ a ≠ h) → ∀ {a₀ : ℕ}, a₀ ∈ A ⟨v, by omega⟩ →
        7 ≤ M ⟨v, by omega⟩ a₀ →
      ((slab c m 7 P A M).Ω.filter (Event (A := A) M x y
        (vert2 hc v hv) (oth x y h))).card * 100 ≤
        13 * ((slab c m 7 P A M).Ω.filter (Hit hc ⟨v, by omega⟩ a₀ h)).card

/-- **The last-row bound is the head-row bound reflected.** -/
theorem absD_of_absH (H : AbsHBound) : AbsDBound := by
  intro c m P A M hK hA hP hc x y h hxy hx hy hh v hv hhole a₀ ha₀ h7
  -- the reflected rows: `v ↦ v'' + 1`, `v + 1 ↦ v''`
  set v'' := m - 2 - v with hv''
  have hv2 : v'' + 1 < m := by omega
  have er1 : (⟨v'' + 1, hv2⟩ : Fin m).rev = ⟨v, by omega⟩ := Fin.ext (by simp [Fin.val_rev]; omega)
  have er0 : (⟨v'', by omega⟩ : Fin m).rev = ⟨v + 1, hv⟩ := Fin.ext (by simp [Fin.val_rev]; omega)
  have hb := H (P := rvP P) (A := rvP A) (M := rvM M) (keyInj_rv hK) (fun w => hA w.rev)
    (fun w a ha => hP w.rev a ha) hc hxy hx hy hh v'' hv2
    (fun a ha => by simp only [rvM, rvP] at ha ⊢; rw [er1] at ha ⊢; exact hhole a ha)
    (a₀ := a₀) (by simp only [rvP]; rw [er1]; exact ha₀) (by simp only [rvM]; rw [er1]; exact h7)
  rw [card_rf, card_rf] at hb
  have hoth := oth_oth hxy hh
  have eE : (slab c m 7 P A M).Ω.filter
        (fun f => Event (A := rvP A) (rvM M) x y (vert2 hc v'' hv2) h (f ∘ rf)) =
      (slab c m 7 P A M).Ω.filter (Event (A := A) M x y (vert2 hc v hv) (oth x y h)) := by
    refine filter_congr fun f _ => ?_
    rw [event_vert2_iff, event_vert2_iff]
    simp only [Function.comp, rf, rvP, rvM, er0, er1, hoth]
    tauto
  have eH : (slab c m 7 P A M).Ω.filter (fun f => Hit hc ⟨v'' + 1, hv2⟩ a₀ h (f ∘ rf)) =
      (slab c m 7 P A M).Ω.filter (Hit hc ⟨v, by omega⟩ a₀ h) := by
    refine filter_congr fun f _ => ?_
    simp only [Hit, Function.comp, rf, er1]
  rw [eE, eH] at hb
  exact hb

end GridGen.Gauge
