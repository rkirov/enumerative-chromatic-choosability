/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Eight.Bad8

/-!
# Chordless witnesses

A bad solution of a lower-part move realizes the prescribed event of a crossing path
(`bad_event`). A witness of least length is *chordless*: two cells that are not consecutive on the
path are not adjacent. A chord joins two `{x, y}`-cells, so it is an edge of the `{x, y}`-graph and
shortens the witness (`witn_shortcut`). Hence a bad solution realizes the event of a chordless
crossing path (`bad_event_chordless`).

Through a hole, the phase of a path with its head at the hole row is forced: the head's seam cell
needs a colour keyed with the other label of the head, and there is none if that label is the hole
(`event_head_hole`). Likewise at the last cell (`event_last_hole`).
-/

open Finset
open scoped Classical

set_option linter.unusedSectionVars false

namespace GridGen.Gauge

variable {c m k : ℕ} {P A : Fin m → Finset ℕ} {M : Fin m → ℕ → ℕ}

/-- No two non-consecutive cells of the list are adjacent. -/
def Chordless (l : List (Cell c m)) : Prop :=
  ∀ i j (hi : i < l.length) (hj : j < l.length), i + 1 < j → ¬ slabAdj l[i] l[j]

section Witness

variable {hc : 1 ≤ c} {w x y : ℕ}

variable (hc M w x y) in
/-- A witness of the bad event: a duplicate-free chain of `{x, y}`-cells from a first future cell
below the cut to one above it, both next to seam cells keyed in `{x, y}`. -/
def Witn (f : Cell c m → ℕ) (l : List (Cell c m)) : Prop :=
  l.Nodup ∧ l.IsChain slabAdj ∧ (∀ z ∈ l, XY x y f z) ∧
    (∃ v₁ : Fin m, w < v₁.val ∧ l.head? = some (fut0 hc, v₁) ∧
      (M v₁ (f (1, v₁)) = x ∨ M v₁ (f (1, v₁)) = y)) ∧
    (∃ v₂ : Fin m, v₂.val ≤ w ∧ l.getLast? = some (fut0 hc, v₂) ∧
      (M v₂ (f (1, v₂)) = x ∨ M v₂ (f (1, v₂)) = y))

/-- A bad solution has a witness. -/
theorem witn_of_bad {f : Cell c m → ℕ} (hb : Bad hc M w x y f) : ∃ l, Witn M hc w x y f l := by
  obtain ⟨s, ⟨v₁, hw₁, rfl, hk₁, hxy₁⟩, v₂, hw₂, hk₂, hr⟩ := hb
  obtain ⟨p⟩ := hr
  set q := p.bypass
  have hq : q.IsPath := p.bypass_isPath
  refine ⟨q.support, hq.support_nodup, (q.isChain_adj_support).imp fun _ _ h => h.1,
    fun z hz => xy_of_reachable hxy₁ ⟨q.takeUntil z hz⟩, ⟨v₁, hw₁, ?_, hk₁⟩, ⟨v₂, hw₂, ?_, hk₂⟩⟩
  · rw [List.head?_eq_some_head (SimpleGraph.Walk.support_ne_nil _), SimpleGraph.Walk.head_support]
  · rw [List.getLast?_eq_some_getLast (SimpleGraph.Walk.support_ne_nil _),
      SimpleGraph.Walk.getLast_support]

/-- A witness realizes the prescribed event of a crossing path, with the head's label as phase. -/
theorem event_of_witn (hxy : x ≠ y) {f : Cell c m → ℕ} (hf : (slab c m k P A M).Valid f)
    {l : List (Cell c m)} (hl : Witn M hc w x y f l) :
    l ∈ crossPaths hc w ∧ ∃ ℓ₀ ∈ ({x, y} : Finset ℕ), Event (A := A) M x y l ℓ₀ f := by
  obtain ⟨hnd, hch, hxyl, ⟨v₁, hw₁, hhead, hk₁⟩, ⟨v₂, hw₂, hlast, hk₂⟩⟩ := hl
  have hne : l ≠ [] := by rintro rfl; simp at hhead
  have hv : v₁ ≠ v₂ := fun h => by rw [h] at hw₁; omega
  have hkch : l.IsChain (kG x y f).Adj := by
    rw [List.IsChain.iff_mem] at hch
    exact hch.imp fun a b h => ⟨h.2.2, hxyl a h.1, hxyl b h.2.1⟩
  have hxy₁ : XY x y f (fut0 hc, v₁) := hxyl _ (List.mem_of_mem_head? hhead)
  refine ⟨?_, f (fut0 hc, v₁), ?_, ?_⟩
  · unfold crossPaths
    rw [mem_filter]
    exact ⟨mem_allLists hnd, hnd, hch, fun z hz => (hxyl z hz).1, ⟨v₁, hw₁, hhead⟩,
      ⟨v₂, hw₂, hlast⟩⟩
  · rcases hxy₁.2 with h | h <;> simp [h]
  · have hℓ := hxy₁.2
    have halt := alt_of_chain hxy hf l (f (fut0 hc, v₁)) hkch
      (fun a ha => by rw [hhead] at ha; simp at ha; rw [ha]) hℓ
    have hseam : ∀ v : Fin m, M v (f (1, v)) ≠ f (fut0 hc, v) := fun v => by
      have := hf.2 (1, v) (fut0 hc, v) (slabAdj_seam (fut0 hc, v) rfl)
      rwa [slab_conf_seam (Fin.val_one _) rfl] at this
    have hA1 : ∀ v : Fin m, f (1, v) ∈ A v := fun v => by
      have := hf.1 (1, v); rwa [slab_D_one (Fin.val_one _)] at this
    intro z hz
    unfold chainOf at hz
    rw [hhead, hlast] at hz
    simp only [Option.toList_some, List.map_cons, List.map_nil, List.mem_append,
      List.mem_singleton] at hz
    unfold presc
    rcases hz with (rfl | hz) | rfl
    · rw [ite_eq_left (seamOf_fst _), ite_eq_left (by rw [hhead]; rfl), mem_filter]
      exact ⟨hA1 v₁, eq_oth hxy hℓ hk₁ (hseam v₁)⟩
    · have h2 := (hxyl z hz).1
      rw [ite_eq_right (by omega), mem_singleton]
      have hi := List.idxOf_lt_length_of_mem hz
      have := halt _ hi
      rwa [List.getElem_idxOf] at this
    · rw [ite_eq_left (seamOf_fst _), ite_eq_right (by rw [hhead]; simp [seamOf]; exact Ne.symm hv),
        mem_filter]
      refine ⟨hA1 v₂, eq_oth hxy (lab_mem hℓ _) hk₂ ?_⟩
      have hlen : l.length - 1 < l.length := by
        have := List.length_pos_of_ne_nil hne; omega
      have e1 : l[l.length - 1] = (fut0 hc, v₂) := by
        have := List.getLast_eq_getElem hne
        rw [← this]
        have h' := hlast
        rw [List.getLast?_eq_some_getLast hne] at h'
        exact Option.some.inj h'
      rw [← halt _ hlen, e1]
      exact hseam v₂

/-- **Shortcut along a chord.** -/
theorem witn_shortcut {f : Cell c m → ℕ} {l : List (Cell c m)} (hl : Witn M hc w x y f l)
    {i j : ℕ} (hij : i + 1 < j) (hj : j < l.length) (hadj : slabAdj l[i] l[j]) :
    Witn M hc w x y f (l.take (i + 1) ++ l.drop j) ∧
      (l.take (i + 1) ++ l.drop j).length < l.length := by
  obtain ⟨hnd, hch, hxyl, ⟨v₁, hw₁, hhead, hk₁⟩, ⟨v₂, hw₂, hlast, hk₂⟩⟩ := hl
  have hi : i < l.length := by omega
  have hsub : (l.take (i + 1) ++ l.drop j).Sublist l := by
    have := (List.Sublist.refl (l.take (i + 1))).append
      (List.drop_sublist_drop_left l (show i + 1 ≤ j by omega))
    rwa [List.take_append_drop] at this
  have hlen : (l.take (i + 1) ++ l.drop j).length = i + 1 + (l.length - j) := by
    simp only [List.length_append, List.length_take, List.length_drop]; omega
  refine ⟨⟨hnd.sublist hsub, ?_, fun z hz => hxyl z (hsub.subset hz), ⟨v₁, hw₁, ?_, hk₁⟩,
    ⟨v₂, hw₂, ?_, hk₂⟩⟩, by omega⟩
  · rw [List.isChain_append]
    refine ⟨hch.take _, hch.drop _, fun a ha b hb => ?_⟩
    rw [List.getLast?_eq_getElem?] at ha
    rw [List.head?_eq_getElem?] at hb
    simp only [List.length_take, List.getElem?_take, List.getElem?_drop] at ha hb
    rw [show min (i + 1) l.length - 1 = i by omega, ite_eq_left (by omega),
      List.getElem?_eq_getElem hi, Option.mem_def, Option.some.injEq] at ha
    rw [add_zero, List.getElem?_eq_getElem hj, Option.mem_def, Option.some.injEq] at hb
    rw [← ha, ← hb]; exact hadj
  · rw [List.head?_eq_getElem?] at hhead ⊢
    rw [List.getElem?_append_left (by simp; omega), List.getElem?_take]
    rw [ite_eq_left (by omega)]; exact hhead
  · rw [List.getLast?_eq_getElem?] at hlast ⊢
    rw [hlen, List.getElem?_append_right (by simp; omega), List.getElem?_drop]
    have e : j + (i + 1 + (l.length - j) - 1 - (l.take (i + 1)).length) = l.length - 1 := by
      simp only [List.length_take]; omega
    rw [e]; exact hlast

/-- **A witness of least length is chordless.** -/
theorem exists_chordless_witn {f : Cell c m → ℕ} (hb : Bad hc M w x y f) :
    ∃ l, Witn M hc w x y f l ∧ Chordless l := by
  have hex : ∃ n, ∃ l, Witn M hc w x y f l ∧ l.length = n := by
    obtain ⟨l, hl⟩ := witn_of_bad hb
    exact ⟨l.length, l, hl, rfl⟩
  obtain ⟨l, hl, hlen⟩ := Nat.find_spec hex
  refine ⟨l, hl, fun i j hi hj hij hadj => ?_⟩
  obtain ⟨hl', hlt⟩ := witn_shortcut hl hij hj hadj
  exact Nat.find_min hex (by omega) ⟨_, hl', rfl⟩

/-- **A bad solution realizes the event of a chordless crossing path.** -/
theorem bad_event_chordless (hxy : x ≠ y) {f : Cell c m → ℕ} (hf : (slab c m k P A M).Valid f)
    (hb : Bad hc M w x y f) :
    ∃ l ∈ crossPaths hc w, Chordless l ∧ ∃ ℓ₀ ∈ ({x, y} : Finset ℕ), Event (A := A) M x y l ℓ₀ f := by
  obtain ⟨l, hl, hch⟩ := exists_chordless_witn hb
  obtain ⟨hmem, ℓ₀, hℓ, he⟩ := event_of_witn (P := P) hxy hf hl
  exact ⟨l, hmem, hch, ℓ₀, hℓ, he⟩

end Witness

/-! ### The forced phase at a hole -/

section Hole

variable {hc : 1 ≤ c} {x y : ℕ}

/-- If no colour of the head's row is keyed `h`, the phase `oth h` is impossible. -/
theorem event_head_hole (hxy : x ≠ y) {h : ℕ} (hh : h = x ∨ h = y) {l : List (Cell c m)}
    {v₁ : Fin m} (hhead : l.head? = some (fut0 hc, v₁)) (hhole : ∀ a ∈ A v₁, M v₁ a ≠ h)
    (f : Cell c m → ℕ) : ¬ Event (A := A) M x y l (oth x y h) f := by
  intro he
  have hz := he (1, v₁) (by unfold chainOf; rw [hhead]; simp [seamOf])
  unfold presc at hz
  rw [ite_eq_left (Fin.val_one _), ite_eq_left (by rw [hhead]; rfl), mem_filter,
    oth_oth hxy hh] at hz
  exact hhole _ hz.1 hz.2

/-- If no colour of the last cell's row is keyed `h`, the phase putting `oth h` on the last cell
is impossible. -/
theorem event_last_hole {h ℓ₀ : ℕ} (hxy : x ≠ y) (hh : h = x ∨ h = y) {l : List (Cell c m)}
    {v₁ v₂ : Fin m} (hv : v₁ ≠ v₂) (hhead : l.head? = some (fut0 hc, v₁))
    (hlast : l.getLast? = some (fut0 hc, v₂)) (hhole : ∀ a ∈ A v₂, M v₂ a ≠ h)
    (hlab : lab x y ℓ₀ (l.length - 1) = oth x y h) (f : Cell c m → ℕ) :
    ¬ Event (A := A) M x y l ℓ₀ f := by
  intro he
  have hz := he (1, v₂) (by unfold chainOf; rw [hlast]; simp [seamOf])
  unfold presc at hz
  rw [ite_eq_left (Fin.val_one _), ite_eq_right (by rw [hhead]; simp; exact Ne.symm hv),
    mem_filter, hlab, oth_oth hxy hh] at hz
  exact hhole _ hz.1 hz.2

end Hole

end GridGen.Gauge
