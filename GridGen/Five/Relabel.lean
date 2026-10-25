/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.Statement
import GridGen.Four.Relabel

/-!
# Height five: relabelling colours

`GridGen/Four/Relabel.lean` with five rows. The pattern-weighted count `G w A B C D E` does not
see the names of the colours. Applying one map `f`, injective on the colours in play, to all five
lists maps the proper colourings bijectively onto the proper colourings of the image lists, and
it preserves the six non-consecutive equalities `r1 = r3`, `r2 = r4`, `r3 = r5`, `r1 = r4`,
`r2 = r5`, `r1 = r5` that the orbit `orb` reads (`orb_congr`, `gw_congr`).

The consequence used by the uniform transfer and the bridge is the *realisation* lemma
(`G_erase_eq`): the weighted number of successors of a proper column `s` inside a palette `P`,
`G w (P.erase (r1 s)) … (P.erase (r5 s))`, depends only on `|P|` and the equality pattern of
`s`. With `P = range k` and `s' = canon s` it is `GU k w s` (`G_erase_eq_GU`).
-/

namespace GridGen.Five

open Finset

/-! ### Properness, patterns, and the weight -/

/-- A column is proper when consecutive rows differ. -/
def Proper (t : T5) : Prop := r1 t ≠ r2 t ∧ r2 t ≠ r3 t ∧ r3 t ≠ r4 t ∧ r4 t ≠ r5 t

/-- Two columns have the same equality pattern: the six non-consecutive equalities agree. -/
def SamePat (s t : T5) : Prop :=
  (r1 s = r3 s ↔ r1 t = r3 t) ∧ (r2 s = r4 s ↔ r2 t = r4 t) ∧ (r3 s = r5 s ↔ r3 t = r5 t) ∧
    (r1 s = r4 s ↔ r1 t = r4 t) ∧ (r2 s = r5 s ↔ r2 t = r5 t) ∧ (r1 s = r5 s ↔ r1 t = r5 t)

/-- The rows of a column lie in a palette. -/
def RowsIn (t : T5) (P : Finset ℕ) : Prop :=
  r1 t ∈ P ∧ r2 t ∈ P ∧ r3 t ∈ P ∧ r4 t ∈ P ∧ r5 t ∈ P

theorem proper_of_mem_sts {A B C D E : Finset ℕ} {t : T5} (h : t ∈ sts A B C D E) :
    Proper t := by
  rw [mem_sts] at h
  exact ⟨h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

/-- The orbit reads only the equality pattern. -/
theorem orb_congr {s t : T5} (h : SamePat s t) : orb s = orb t := by
  obtain ⟨h13, h24, h35, h14, h25, h15⟩ := h
  simp only [orb, h13, h24, h35, h14, h25, h15]

/-- The weight reads only the equality pattern. -/
theorem gw_congr (w : Wt5) {s t : T5} (h : SamePat s t) : gw w s = gw w t := by
  unfold gw; rw [orb_congr h]

/-! ### Relabelling by a map injective on the colours in play -/

/-- Apply a colour map to every row. -/
def mapT (f : ℕ → ℕ) (t : T5) : T5 := (f (r1 t), f (r2 t), f (r3 t), f (r4 t), f (r5 t))

/-- Relabelling preserves the equality pattern of a column whose colours lie where the map is
injective. -/
theorem samePat_mapT {f : ℕ → ℕ} {S : Finset ℕ} (hf : Set.InjOn f S) {t : T5}
    (ht : RowsIn t S) : SamePat (mapT f t) t := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := ht
  refine ⟨⟨fun h => hf h1 h3 h, fun h => by simp [mapT, h]⟩,
    ⟨fun h => hf h2 h4 h, fun h => by simp [mapT, h]⟩,
    ⟨fun h => hf h3 h5 h, fun h => by simp [mapT, h]⟩,
    ⟨fun h => hf h1 h4 h, fun h => by simp [mapT, h]⟩,
    ⟨fun h => hf h2 h5 h, fun h => by simp [mapT, h]⟩,
    ⟨fun h => hf h1 h5 h, fun h => by simp [mapT, h]⟩⟩

/-- **Relabelling invariance**: a map injective on the union of the lists preserves `G w`. -/
theorem G_image (w : Wt5) {f : ℕ → ℕ} {A B C D E : Finset ℕ}
    (hf : Set.InjOn f ↑(A ∪ B ∪ C ∪ D ∪ E)) :
    G w (A.image f) (B.image f) (C.image f) (D.image f) (E.image f) = G w A B C D E := by
  symm
  unfold G
  have hrows : ∀ t ∈ sts A B C D E, RowsIn t (A ∪ B ∪ C ∪ D ∪ E) := by
    intro t ht
    rw [mem_sts] at ht
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2.1]
  refine Finset.sum_bij (fun t _ => mapT f t) ?_ ?_ ?_ ?_
  · intro t ht
    have hr := hrows t ht
    rw [mem_sts] at ht ⊢
    obtain ⟨h1, h2, h3, h4, h5, p1, p2, p3, p4⟩ := ht
    refine ⟨mem_image_of_mem f h1, mem_image_of_mem f h2, mem_image_of_mem f h3,
      mem_image_of_mem f h4, mem_image_of_mem f h5, fun h => p1 (hf hr.1 hr.2.1 h),
      fun h => p2 (hf hr.2.1 hr.2.2.1 h), fun h => p3 (hf hr.2.2.1 hr.2.2.2.1 h),
      fun h => p4 (hf hr.2.2.2.1 hr.2.2.2.2 h)⟩
  · intro t ht u hu h
    have ht' := hrows t ht
    have hu' := hrows u hu
    simp only [mapT, Prod.mk.injEq] at h
    obtain ⟨e1, e2, e3, e4, e5⟩ := h
    have c1 := hf ht'.1 hu'.1 e1
    have c2 := hf ht'.2.1 hu'.2.1 e2
    have c3 := hf ht'.2.2.1 hu'.2.2.1 e3
    have c4 := hf ht'.2.2.2.1 hu'.2.2.2.1 e4
    have c5 := hf ht'.2.2.2.2 hu'.2.2.2.2 e5
    obtain ⟨t1, t2, t3, t4, t5⟩ := t
    obtain ⟨u1, u2, u3, u4, u5⟩ := u
    simp only [r1, r2, r3, r4, r5] at c1 c2 c3 c4 c5
    rw [c1, c2, c3, c4, c5]
  · intro t ht
    rw [mem_sts] at ht
    obtain ⟨h1, h2, h3, h4, h5, p1, p2, p3, p4⟩ := ht
    obtain ⟨x1, hx1, e1⟩ := Finset.mem_image.mp h1
    obtain ⟨x2, hx2, e2⟩ := Finset.mem_image.mp h2
    obtain ⟨x3, hx3, e3⟩ := Finset.mem_image.mp h3
    obtain ⟨x4, hx4, e4⟩ := Finset.mem_image.mp h4
    obtain ⟨x5, hx5, e5⟩ := Finset.mem_image.mp h5
    refine ⟨(x1, x2, x3, x4, x5), ?_, ?_⟩
    · rw [mem_sts]
      refine ⟨hx1, hx2, hx3, hx4, hx5, fun h => p1 ?_, fun h => p2 ?_, fun h => p3 ?_,
        fun h => p4 ?_⟩
      · simp only [r1, r2] at h; rw [← e1, ← e2, h]
      · simp only [r2, r3] at h; rw [← e2, ← e3, h]
      · simp only [r3, r4] at h; rw [← e3, ← e4, h]
      · simp only [r4, r5] at h; rw [← e4, ← e5, h]
    · obtain ⟨t1, t2, t3, t4, t5⟩ := t
      simp only [mapT, r1, r2, r3, r4, r5] at e1 e2 e3 e4 e5 ⊢
      rw [e1, e2, e3, e4, e5]
  · intro t ht
    exact (gw_congr w (samePat_mapT hf (hrows t ht))).symm

/-! ### Realisation of a pattern inside a palette -/

/-- Equalities between rows of two columns with the same pattern, both proper, agree for every
pair of rows. -/
theorem samePat_rows {s s' : T5} (hs : Proper s) (hs' : Proper s') (h : SamePat s s') :
    (r1 s = r2 s ↔ r1 s' = r2 s') ∧ (r1 s = r3 s ↔ r1 s' = r3 s') ∧
    (r1 s = r4 s ↔ r1 s' = r4 s') ∧ (r1 s = r5 s ↔ r1 s' = r5 s') ∧
    (r2 s = r3 s ↔ r2 s' = r3 s') ∧ (r2 s = r4 s ↔ r2 s' = r4 s') ∧
    (r2 s = r5 s ↔ r2 s' = r5 s') ∧ (r3 s = r4 s ↔ r3 s' = r4 s') ∧
    (r3 s = r5 s ↔ r3 s' = r5 s') ∧ (r4 s = r5 s ↔ r4 s' = r5 s') := by
  obtain ⟨p1, p2, p3, p4⟩ := hs
  obtain ⟨q1, q2, q3, q4⟩ := hs'
  obtain ⟨h13, h24, h35, h14, h25, h15⟩ := h
  exact ⟨iff_of_false p1 q1, h13, h14, h15, iff_of_false p2 q2, h24, h25, iff_of_false p3 q3,
    h35, iff_of_false p4 q4⟩

/-- The colour map sending the rows of `s` to the rows of `s'`. -/
def rowMap (s s' : T5) (x : ℕ) : ℕ :=
  if x = r1 s then r1 s' else if x = r2 s then r2 s' else if x = r3 s then r3 s'
  else if x = r4 s then r4 s' else r5 s'

/-- The five colours of a column. -/
def rowSet (s : T5) : Finset ℕ := {r1 s, r2 s, r3 s, r4 s, r5 s}

theorem rowMap_rows {s s' : T5} (hs : Proper s) (hs' : Proper s') (h : SamePat s s') :
    rowMap s s' (r1 s) = r1 s' ∧ rowMap s s' (r2 s) = r2 s' ∧ rowMap s s' (r3 s) = r3 s' ∧
      rowMap s s' (r4 s) = r4 s' ∧ rowMap s s' (r5 s) = r5 s' := by
  obtain ⟨e12, e13, e14, e15, e23, e24, e25, e34, e35, e45⟩ := samePat_rows hs hs' h
  unfold rowMap
  refine ⟨ite_eq_left rfl, ?_, ?_, ?_, ?_⟩
  · by_cases h1 : r2 s = r1 s
    · rw [ite_eq_left h1]; exact e12.mp h1.symm
    · rw [ite_eq_right h1, ite_eq_left rfl]
  · by_cases h1 : r3 s = r1 s
    · rw [ite_eq_left h1]; exact e13.mp h1.symm
    by_cases h2 : r3 s = r2 s
    · rw [ite_eq_right h1, ite_eq_left h2]; exact e23.mp h2.symm
    · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left rfl]
  · by_cases h1 : r4 s = r1 s
    · rw [ite_eq_left h1]; exact e14.mp h1.symm
    by_cases h2 : r4 s = r2 s
    · rw [ite_eq_right h1, ite_eq_left h2]; exact e24.mp h2.symm
    by_cases h3 : r4 s = r3 s
    · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3]; exact e34.mp h3.symm
    · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_left rfl]
  · by_cases h1 : r5 s = r1 s
    · rw [ite_eq_left h1]; exact e15.mp h1.symm
    by_cases h2 : r5 s = r2 s
    · rw [ite_eq_right h1, ite_eq_left h2]; exact e25.mp h2.symm
    by_cases h3 : r5 s = r3 s
    · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3]; exact e35.mp h3.symm
    by_cases h4 : r5 s = r4 s
    · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_left h4]; exact e45.mp h4.symm
    · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4]

theorem rowMap_injOn {s s' : T5} (hs : Proper s) (hs' : Proper s') (h : SamePat s s') :
    Set.InjOn (rowMap s s') ↑(rowSet s) := by
  obtain ⟨m1, m2, m3, m4, m5⟩ := rowMap_rows hs hs' h
  obtain ⟨e12, e13, e14, e15, e23, e24, e25, e34, e35, e45⟩ := samePat_rows hs hs' h
  intro x hx y hy hxy
  simp only [rowSet, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl | rfl <;>
    simp only [m1, m2, m3, m4, m5] at hxy <;> first
      | rfl | exact e12.mpr hxy | exact (e12.mpr hxy.symm).symm | exact e13.mpr hxy
      | exact (e13.mpr hxy.symm).symm | exact e14.mpr hxy | exact (e14.mpr hxy.symm).symm
      | exact e15.mpr hxy | exact (e15.mpr hxy.symm).symm
      | exact e23.mpr hxy | exact (e23.mpr hxy.symm).symm | exact e24.mpr hxy
      | exact (e24.mpr hxy.symm).symm | exact e25.mpr hxy | exact (e25.mpr hxy.symm).symm
      | exact e34.mpr hxy | exact (e34.mpr hxy.symm).symm
      | exact e35.mpr hxy | exact (e35.mpr hxy.symm).symm
      | exact e45.mpr hxy | exact (e45.mpr hxy.symm).symm

/-- A bijection of palettes of equal size that extends the row map: as a map `ℕ → ℕ` (identity
off `P`), injective on `P`, onto `P'`, and sending the rows of `s` to those of `s'`. -/
theorem exists_palette_map {s s' : T5} (hs : Proper s) (hs' : Proper s') (h : SamePat s s')
    {P P' : Finset ℕ} (hc : P.card = P'.card) (hP : RowsIn s P) (hP' : RowsIn s' P') :
    ∃ g : ℕ → ℕ, Set.InjOn g ↑P ∧ P.image g = P' ∧ g (r1 s) = r1 s' ∧ g (r2 s) = r2 s' ∧
      g (r3 s) = r3 s' ∧ g (r4 s) = r4 s' ∧ g (r5 s) = r5 s' := by
  classical
  obtain ⟨m1, m2, m3, m4, m5⟩ := rowMap_rows hs hs' h
  have hinj := rowMap_injOn hs hs' h
  let f : {x // x ∈ P} → ℕ := fun x => rowMap s s' x.1
  let S : Finset {x // x ∈ P} := Finset.univ.filter (fun x => x.1 ∈ rowSet s)
  have hfS : S.image f ⊆ P' := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    have hx' : x.1 ∈ rowSet s := (Finset.mem_filter.mp hx).2
    simp only [rowSet, Finset.mem_insert, Finset.mem_singleton] at hx'
    simp only [f]
    rcases hx' with e | e | e | e | e <;> rw [e]
    · rw [m1]; exact hP'.1
    · rw [m2]; exact hP'.2.1
    · rw [m3]; exact hP'.2.2.1
    · rw [m4]; exact hP'.2.2.2.1
    · rw [m5]; exact hP'.2.2.2.2
  have hfinj : Set.InjOn f ↑S := by
    intro x hx y hy hxy
    exact Subtype.ext (hinj (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2 hxy)
  obtain ⟨e, he⟩ :=
    Finset.exists_equiv_extend_of_card_eq (by rw [Fintype.card_coe, hc]) hfS hfinj
  let g : ℕ → ℕ := fun x => if hx : x ∈ P then (e ⟨x, hx⟩ : ℕ) else x
  have hg : ∀ x (hx : x ∈ P), g x = e ⟨x, hx⟩ := fun x hx => dite_eq_left hx
  have hrow : ∀ x, x ∈ rowSet s → x ∈ P → g x = rowMap s s' x := by
    intro x hxs hxP
    rw [hg x hxP]
    exact he ⟨x, hxP⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxs⟩)
  have hrs : ∀ {x}, x = r1 s ∨ x = r2 s ∨ x = r3 s ∨ x = r4 s ∨ x = r5 s → x ∈ rowSet s := by
    intro x hx; simp only [rowSet, Finset.mem_insert, Finset.mem_singleton]; exact hx
  refine ⟨g, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    rw [hg x hx, hg y hy] at hxy
    exact congrArg Subtype.val (e.injective (Subtype.ext hxy))
  · ext y
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩; rw [hg x hx]; exact (e ⟨x, hx⟩).2
    · intro hy
      refine ⟨(e.symm ⟨y, hy⟩ : ℕ), (e.symm ⟨y, hy⟩).2, ?_⟩
      rw [hg _ (e.symm ⟨y, hy⟩).2]
      simp
  · rw [hrow _ (hrs (Or.inl rfl)) hP.1, m1]
  · rw [hrow _ (hrs (Or.inr (Or.inl rfl))) hP.2.1, m2]
  · rw [hrow _ (hrs (Or.inr (Or.inr (Or.inl rfl)))) hP.2.2.1, m3]
  · rw [hrow _ (hrs (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hP.2.2.2.1, m4]
  · rw [hrow _ (hrs (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) hP.2.2.2.2, m5]

/-- **Realisation.** The weighted number of successors of a proper column inside a palette
depends only on the size of the palette and the equality pattern of the column. -/
theorem G_erase_eq (w : Wt5) {s s' : T5} (hs : Proper s) (hs' : Proper s') (h : SamePat s s')
    {P P' : Finset ℕ} (hc : P.card = P'.card) (hP : RowsIn s P) (hP' : RowsIn s' P') :
    G w (P.erase (r1 s)) (P.erase (r2 s)) (P.erase (r3 s)) (P.erase (r4 s)) (P.erase (r5 s))
      = G w (P'.erase (r1 s')) (P'.erase (r2 s')) (P'.erase (r3 s')) (P'.erase (r4 s'))
          (P'.erase (r5 s')) := by
  obtain ⟨g, hg, hgP, g1, g2, g3, g4, g5⟩ := exists_palette_map hs hs' h hc hP hP'
  have hU : Set.InjOn g ↑(P.erase (r1 s) ∪ P.erase (r2 s) ∪ P.erase (r3 s) ∪ P.erase (r4 s) ∪
      P.erase (r5 s)) := by
    refine hg.mono ?_
    intro x hx
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_erase] at hx
    simp only [Finset.mem_coe]
    rcases hx with (((h | h) | h) | h) | h <;> exact h.2
  rw [← G_image w hU, Four.image_erase_of_injOn hg hP.1, Four.image_erase_of_injOn hg hP.2.1,
    Four.image_erase_of_injOn hg hP.2.2.1, Four.image_erase_of_injOn hg hP.2.2.2.1,
    Four.image_erase_of_injOn hg hP.2.2.2.2, hgP, g1, g2, g3, g4, g5]

/-! ### The canonical realisation -/

theorem proper_canon {s : T5} (hs : Proper s) : Proper (canon s) := by
  obtain ⟨p1, p2, p3, p4⟩ := hs
  unfold canon Proper
  simp only [r1, r2, r3, r4, r5] at *
  refine ⟨by decide, ?_, ?_, ?_⟩ <;> split_ifs <;> simp_all

theorem samePat_canon {s : T5} (hs : Proper s) : SamePat s (canon s) := by
  obtain ⟨p1, p2, p3, p4⟩ := hs
  unfold canon SamePat
  simp only [r1, r2, r3, r4, r5] at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> split_ifs <;> simp_all <;> omega

theorem rowsIn_canon {k : ℕ} (hk : 5 ≤ k) (s : T5) : RowsIn (canon s) (range k) := by
  unfold canon RowsIn
  simp only [r1, r2, r3, r4, r5, Finset.mem_range]
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩ <;> split_ifs <;> omega

/-- `canon` reads only the equality pattern. -/
theorem canon_congr {s t : T5} (h : SamePat s t) : canon s = canon t := by
  obtain ⟨h13, h24, h35, h14, h25, h15⟩ := h
  have e1 : (r3 s = r1 s) ↔ (r3 t = r1 t) := by rw [eq_comm, h13, eq_comm]
  have e2 : (r4 s = r2 s) ↔ (r4 t = r2 t) := by rw [eq_comm, h24, eq_comm]
  have e3 : (r4 s = r1 s) ↔ (r4 t = r1 t) := by rw [eq_comm, h14, eq_comm]
  have e4 : (r5 s = r3 s) ↔ (r5 t = r3 t) := by rw [eq_comm, h35, eq_comm]
  have e5 : (r5 s = r2 s) ↔ (r5 t = r2 t) := by rw [eq_comm, h25, eq_comm]
  have e6 : (r5 s = r1 s) ↔ (r5 t = r1 t) := by rw [eq_comm, h15, eq_comm]
  simp only [canon, e1, e2, e3, e4, e5, e6]

/-- **The uniform successors, realised in any palette of `k` colours.** -/
theorem G_erase_eq_GU (w : Wt5) {k : ℕ} (hk : 5 ≤ k) {s : T5} (hs : Proper s) {P : Finset ℕ}
    (hc : P.card = k) (hP : RowsIn s P) :
    G w (P.erase (r1 s)) (P.erase (r2 s)) (P.erase (r3 s)) (P.erase (r4 s)) (P.erase (r5 s))
      = GU k w s :=
  G_erase_eq w hs (proper_canon hs) (samePat_canon hs) (by rw [hc, card_range])
    hP (rowsIn_canon hk s)

/-- `GU` reads only the equality pattern. -/
theorem GU_congr (k : ℕ) (w : Wt5) {s t : T5} (h : canon s = canon t) :
    GU k w s = GU k w t := by
  unfold GU; rw [h]

end GridGen.Five
