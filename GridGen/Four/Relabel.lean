/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.Statement

/-!
# Height four: relabelling colours

The pattern-weighted count `G w A B C D` does not see the names of the colours. Applying one map
`f`, injective on the colours in play, to all four lists maps the proper colourings bijectively
onto the proper colourings of the image lists, and it preserves the three equalities `r1 = r3`, `r2 = r4`, `r1 = r4` the weight `gw` reads
(`gw_congr`). In particular every permutation of `ℕ` preserves `G w` (`G_perm`).

The consequence used by the uniform transfer and the bridge is a *realisation* lemma
(`G_erase_eq`): the weighted number of successors of a proper column `s` inside a palette `P`,
`G w (P.erase (r1 s)) … (P.erase (r4 s))`, depends only on `|P|` and the equality pattern of
`s`. A bijection `P ≃ P'` sending the colours of `s` to those of `s'` is obtained from
`Finset.exists_equiv_extend_of_card_eq`. With `P = range k` and `s' = canon s` it is `GU k w s`
(`G_erase_eq_GU`). The same holds for the plain number of colourings (`card_erase_eq`), which
is `G` at the weight `(1, 1, 1)`.
-/

namespace GridGen.Four

open Finset GridGen.Lookback

/-! ### Properness, patterns, and the weight -/

/-- A column is proper when consecutive rows differ. -/
def Proper (t : T4) : Prop := r1 t ≠ r2 t ∧ r2 t ≠ r3 t ∧ r3 t ≠ r4 t

/-- Two columns have the same equality pattern: the three non-consecutive equalities agree. -/
def SamePat (s t : T4) : Prop :=
  (r1 s = r3 s ↔ r1 t = r3 t) ∧ (r2 s = r4 s ↔ r2 t = r4 t) ∧ (r1 s = r4 s ↔ r1 t = r4 t)

/-- The rows of a column lie in a palette. -/
def RowsIn (t : T4) (P : Finset ℕ) : Prop := r1 t ∈ P ∧ r2 t ∈ P ∧ r3 t ∈ P ∧ r4 t ∈ P

theorem proper_of_mem_sts {A B C D : Finset ℕ} {t : T4} (h : t ∈ sts A B C D) : Proper t := by
  rw [mem_sts] at h
  exact ⟨h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-- The weight reads only the equality pattern. -/
theorem gw_congr (w : Wt) {s t : T4} (h : SamePat s t) : gw w s = gw w t := by
  obtain ⟨h13, h24, h14⟩ := h
  simp only [gw, h13, h24, h14]

/-- At the weight `(1, 1, 1)` every column weighs one. -/
theorem gw_one (t : T4) : gw ⟨1, 1, 1⟩ t = 1 := by
  unfold gw; split_ifs <;> rfl

/-- The number of proper colourings is `G` at the weight `(1, 1, 1)`. -/
theorem card_sts_eq_G (A B C D : Finset ℕ) :
    ((sts A B C D).card : ℝ) = G ⟨1, 1, 1⟩ A B C D := by
  unfold G
  simp only [gw_one, Finset.sum_const, nsmul_eq_mul, mul_one]

/-! ### Relabelling by a map injective on the colours in play -/

/-- Apply a colour map to every row. -/
def mapT (f : ℕ → ℕ) (t : T4) : T4 := (f (r1 t), f (r2 t), f (r3 t), f (r4 t))

/-- Relabelling preserves the equality pattern of a column whose colours lie where the map is
injective. -/
theorem samePat_mapT {f : ℕ → ℕ} {S : Finset ℕ} (hf : Set.InjOn f S) {t : T4} (ht : RowsIn t S) :
    SamePat (mapT f t) t := by
  obtain ⟨h1, h2, h3, h4⟩ := ht
  refine ⟨⟨fun h => hf h1 h3 h, fun h => by simp [mapT, h]⟩,
    ⟨fun h => hf h2 h4 h, fun h => by simp [mapT, h]⟩,
    ⟨fun h => hf h1 h4 h, fun h => by simp [mapT, h]⟩⟩

/-- **Relabelling invariance**: a map injective on the union of the lists preserves `G w`. -/
theorem G_image (w : Wt) {f : ℕ → ℕ} {A B C D : Finset ℕ} (hf : Set.InjOn f ↑(A ∪ B ∪ C ∪ D)) :
    G w (A.image f) (B.image f) (C.image f) (D.image f) = G w A B C D := by
  symm
  unfold G
  have hrows : ∀ t ∈ sts A B C D, RowsIn t (A ∪ B ∪ C ∪ D) := by
    intro t ht
    rw [mem_sts] at ht
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1]
  refine Finset.sum_bij (fun t _ => mapT f t) ?_ ?_ ?_ ?_
  · intro t ht
    have hr := hrows t ht
    have hs := samePat_mapT hf hr
    rw [mem_sts] at ht ⊢
    obtain ⟨h1, h2, h3, h4, p1, p2, p3⟩ := ht
    refine ⟨mem_image_of_mem f h1, mem_image_of_mem f h2, mem_image_of_mem f h3,
      mem_image_of_mem f h4, fun h => p1 (hf hr.1 hr.2.1 h), fun h => p2 (hf hr.2.1 hr.2.2.1 h),
      fun h => p3 (hf hr.2.2.1 hr.2.2.2 h)⟩
  · intro t ht u hu h
    have ht' := hrows t ht
    have hu' := hrows u hu
    simp only [mapT, Prod.mk.injEq] at h
    obtain ⟨e1, e2, e3, e4⟩ := h
    have c1 := hf ht'.1 hu'.1 e1
    have c2 := hf ht'.2.1 hu'.2.1 e2
    have c3 := hf ht'.2.2.1 hu'.2.2.1 e3
    have c4 := hf ht'.2.2.2 hu'.2.2.2 e4
    obtain ⟨t1, t2, t3, t4⟩ := t
    obtain ⟨u1, u2, u3, u4⟩ := u
    simp only [r1, r2, r3, r4] at c1 c2 c3 c4
    rw [c1, c2, c3, c4]
  · intro t ht
    rw [mem_sts] at ht
    obtain ⟨h1, h2, h3, h4, p1, p2, p3⟩ := ht
    obtain ⟨x1, hx1, e1⟩ := Finset.mem_image.mp h1
    obtain ⟨x2, hx2, e2⟩ := Finset.mem_image.mp h2
    obtain ⟨x3, hx3, e3⟩ := Finset.mem_image.mp h3
    obtain ⟨x4, hx4, e4⟩ := Finset.mem_image.mp h4
    refine ⟨(x1, x2, x3, x4), ?_, ?_⟩
    · rw [mem_sts]
      refine ⟨hx1, hx2, hx3, hx4, fun h => p1 ?_, fun h => p2 ?_, fun h => p3 ?_⟩
      · simp only [r1, r2] at h; rw [← e1, ← e2, h]
      · simp only [r2, r3] at h; rw [← e2, ← e3, h]
      · simp only [r3, r4] at h; rw [← e3, ← e4, h]
    · obtain ⟨t1, t2, t3, t4⟩ := t
      simp only [mapT, r1, r2, r3, r4] at e1 e2 e3 e4 ⊢
      rw [e1, e2, e3, e4]
  · intro t ht
    exact (gw_congr w (samePat_mapT hf (hrows t ht))).symm

/-- **Every permutation of the colours preserves `G w`.** -/
theorem G_perm (w : Wt) (σ : Equiv.Perm ℕ) (A B C D : Finset ℕ) :
    G w (A.image σ) (B.image σ) (C.image σ) (D.image σ) = G w A B C D :=
  G_image w (σ.injective.injOn)

/-! ### Realisation of a pattern inside a palette -/

/-- Equalities between rows of two columns with the same pattern, both proper, agree for every
pair of rows. -/
theorem samePat_rows {s s' : T4} (hs : Proper s) (hs' : Proper s') (h : SamePat s s') :
    (r1 s = r2 s ↔ r1 s' = r2 s') ∧ (r1 s = r3 s ↔ r1 s' = r3 s') ∧
    (r1 s = r4 s ↔ r1 s' = r4 s') ∧ (r2 s = r3 s ↔ r2 s' = r3 s') ∧
    (r2 s = r4 s ↔ r2 s' = r4 s') ∧ (r3 s = r4 s ↔ r3 s' = r4 s') := by
  obtain ⟨p1, p2, p3⟩ := hs
  obtain ⟨q1, q2, q3⟩ := hs'
  obtain ⟨h13, h24, h14⟩ := h
  exact ⟨iff_of_false p1 q1, h13, h14, iff_of_false p2 q2, h24, iff_of_false p3 q3⟩

/-- The colour map sending the rows of `s` to the rows of `s'`. -/
def rowMap (s s' : T4) (x : ℕ) : ℕ :=
  if x = r1 s then r1 s' else if x = r2 s then r2 s' else if x = r3 s then r3 s' else r4 s'

/-- The four colours of a column. -/
def rowSet (s : T4) : Finset ℕ := {r1 s, r2 s, r3 s, r4 s}

theorem rowMap_rows {s s' : T4} (hs : Proper s) (hs' : Proper s') (h : SamePat s s') :
    rowMap s s' (r1 s) = r1 s' ∧ rowMap s s' (r2 s) = r2 s' ∧ rowMap s s' (r3 s) = r3 s' ∧
      rowMap s s' (r4 s) = r4 s' := by
  obtain ⟨e12, e13, e14, e23, e24, e34⟩ := samePat_rows hs hs' h
  obtain ⟨p1, p2, p3⟩ := hs
  unfold rowMap
  refine ⟨ite_eq_left rfl, ?_, ?_, ?_⟩
  · rw [ite_eq_right (Ne.symm p1), ite_eq_left rfl]
  · by_cases h1 : r3 s = r1 s
    · rw [ite_eq_left h1]; exact e13.mp h1.symm
    · rw [ite_eq_right h1, ite_eq_right (Ne.symm p2), ite_eq_left rfl]
  · by_cases h1 : r4 s = r1 s
    · rw [ite_eq_left h1]; exact e14.mp h1.symm
    · rw [ite_eq_right h1]
      by_cases h2 : r4 s = r2 s
      · rw [ite_eq_left h2]; exact e24.mp h2.symm
      · rw [ite_eq_right h2, ite_eq_right (Ne.symm p3)]

theorem rowMap_injOn {s s' : T4} (hs : Proper s) (hs' : Proper s') (h : SamePat s s') :
    Set.InjOn (rowMap s s') ↑(rowSet s) := by
  obtain ⟨m1, m2, m3, m4⟩ := rowMap_rows hs hs' h
  obtain ⟨e12, e13, e14, e23, e24, e34⟩ := samePat_rows hs hs' h
  intro x hx y hy hxy
  simp only [rowSet, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    simp only [m1, m2, m3, m4] at hxy <;> first
      | rfl | exact e12.mpr hxy | exact (e12.mpr hxy.symm).symm | exact e13.mpr hxy
      | exact (e13.mpr hxy.symm).symm | exact e14.mpr hxy | exact (e14.mpr hxy.symm).symm
      | exact e23.mpr hxy | exact (e23.mpr hxy.symm).symm | exact e24.mpr hxy
      | exact (e24.mpr hxy.symm).symm | exact e34.mpr hxy | exact (e34.mpr hxy.symm).symm

/-- A bijection of palettes of equal size that extends the row map: as a map `ℕ → ℕ` (identity
off `P`), injective on `P`, onto `P'`, and sending the rows of `s` to those of `s'`. -/
theorem exists_palette_map {s s' : T4} (hs : Proper s) (hs' : Proper s') (h : SamePat s s')
    {P P' : Finset ℕ} (hc : P.card = P'.card) (hP : RowsIn s P) (hP' : RowsIn s' P') :
    ∃ g : ℕ → ℕ, Set.InjOn g ↑P ∧ P.image g = P' ∧ g (r1 s) = r1 s' ∧ g (r2 s) = r2 s' ∧
      g (r3 s) = r3 s' ∧ g (r4 s) = r4 s' := by
  classical
  obtain ⟨m1, m2, m3, m4⟩ := rowMap_rows hs hs' h
  have hinj := rowMap_injOn hs hs' h
  let f : {x // x ∈ P} → ℕ := fun x => rowMap s s' x.1
  let S : Finset {x // x ∈ P} := Finset.univ.filter (fun x => x.1 ∈ rowSet s)
  have hfS : S.image f ⊆ P' := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    have hx' : x.1 ∈ rowSet s := (Finset.mem_filter.mp hx).2
    simp only [rowSet, Finset.mem_insert, Finset.mem_singleton] at hx'
    simp only [f]
    rcases hx' with e | e | e | e <;> rw [e]
    · rw [m1]; exact hP'.1
    · rw [m2]; exact hP'.2.1
    · rw [m3]; exact hP'.2.2.1
    · rw [m4]; exact hP'.2.2.2
  have hfinj : Set.InjOn f ↑S := by
    intro x hx y hy hxy
    exact Subtype.ext (hinj (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2 hxy)
  obtain ⟨e, he⟩ := Finset.exists_equiv_extend_of_card_eq (by rw [Fintype.card_coe, hc]) hfS hfinj
  let g : ℕ → ℕ := fun x => if hx : x ∈ P then (e ⟨x, hx⟩ : ℕ) else x
  have hg : ∀ x (hx : x ∈ P), g x = e ⟨x, hx⟩ := fun x hx => dite_eq_left hx
  have hrow : ∀ x, x ∈ rowSet s → x ∈ P → g x = rowMap s s' x := by
    intro x hxs hxP
    rw [hg x hxP]
    exact he ⟨x, hxP⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxs⟩)
  have hrs : ∀ {x}, x = r1 s ∨ x = r2 s ∨ x = r3 s ∨ x = r4 s → x ∈ rowSet s := by
    intro x hx; simp only [rowSet, Finset.mem_insert, Finset.mem_singleton]; exact hx
  refine ⟨g, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · rw [hrow _ (hrs (Or.inr (Or.inr (Or.inr rfl)))) hP.2.2.2, m4]

/-- **Realisation.** The weighted number of successors of a proper column inside a palette
depends only on the size of the palette and the equality pattern of the column. -/
theorem G_erase_eq (w : Wt) {s s' : T4} (hs : Proper s) (hs' : Proper s') (h : SamePat s s')
    {P P' : Finset ℕ} (hc : P.card = P'.card) (hP : RowsIn s P) (hP' : RowsIn s' P') :
    G w (P.erase (r1 s)) (P.erase (r2 s)) (P.erase (r3 s)) (P.erase (r4 s))
      = G w (P'.erase (r1 s')) (P'.erase (r2 s')) (P'.erase (r3 s')) (P'.erase (r4 s')) := by
  obtain ⟨g, hg, hgP, g1, g2, g3, g4⟩ := exists_palette_map hs hs' h hc hP hP'
  have hU : Set.InjOn g ↑(P.erase (r1 s) ∪ P.erase (r2 s) ∪ P.erase (r3 s) ∪ P.erase (r4 s)) := by
    refine hg.mono ?_
    intro x hx
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_erase] at hx
    simp only [Finset.mem_coe]
    rcases hx with ((h | h) | h) | h <;> exact h.2
  rw [← G_image w hU, image_erase_of_injOn hg hP.1, image_erase_of_injOn hg hP.2.1,
    image_erase_of_injOn hg hP.2.2.1, image_erase_of_injOn hg hP.2.2.2, hgP, g1, g2, g3, g4]

/-- The same for the number of proper colourings. -/
theorem card_erase_eq {s s' : T4} (hs : Proper s) (hs' : Proper s') (h : SamePat s s')
    {P P' : Finset ℕ} (hc : P.card = P'.card) (hP : RowsIn s P) (hP' : RowsIn s' P') :
    (sts (P.erase (r1 s)) (P.erase (r2 s)) (P.erase (r3 s)) (P.erase (r4 s))).card
      = (sts (P'.erase (r1 s')) (P'.erase (r2 s')) (P'.erase (r3 s')) (P'.erase (r4 s'))).card := by
  have h' := G_erase_eq ⟨1, 1, 1⟩ hs hs' h hc hP hP'
  rw [← card_sts_eq_G, ← card_sts_eq_G] at h'
  exact_mod_cast h'

/-! ### The canonical realisation -/

theorem proper_canon {s : T4} (hs : Proper s) : Proper (canon s) := by
  obtain ⟨p1, p2, p3⟩ := hs
  unfold canon Proper
  simp only [r1, r2, r3, r4] at *
  refine ⟨by decide, ?_, ?_⟩ <;> split_ifs <;> simp_all

theorem samePat_canon {s : T4} (hs : Proper s) : SamePat s (canon s) := by
  obtain ⟨p1, p2, p3⟩ := hs
  unfold canon SamePat
  simp only [r1, r2, r3, r4] at *
  refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> simp_all <;> omega

theorem rowsIn_canon {k : ℕ} (hk : 4 ≤ k) (s : T4) : RowsIn (canon s) (range k) := by
  unfold canon RowsIn
  simp only [r1, r2, r3, r4, Finset.mem_range]
  refine ⟨by omega, by omega, ?_, ?_⟩ <;> split_ifs <;> omega

/-- **The uniform successors, realised in any palette of `k` colours.** -/
theorem G_erase_eq_GU (w : Wt) {k : ℕ} (hk : 4 ≤ k) {s : T4} (hs : Proper s) {P : Finset ℕ}
    (hc : P.card = k) (hP : RowsIn s P) :
    G w (P.erase (r1 s)) (P.erase (r2 s)) (P.erase (r3 s)) (P.erase (r4 s)) = GU k w s :=
  G_erase_eq w hs (proper_canon hs) (samePat_canon hs) (by rw [hc, card_range])
    hP (rowsIn_canon hk s)

/-- The same for the number of proper colourings. -/
theorem card_erase_eq_canon {k : ℕ} (hk : 4 ≤ k) {s : T4} (hs : Proper s) {P : Finset ℕ}
    (hc : P.card = k) (hP : RowsIn s P) :
    (sts (P.erase (r1 s)) (P.erase (r2 s)) (P.erase (r3 s)) (P.erase (r4 s))).card
      = (sts ((range k).erase (r1 (canon s))) ((range k).erase (r2 (canon s)))
          ((range k).erase (r3 (canon s))) ((range k).erase (r4 (canon s)))).card :=
  card_erase_eq hs (proper_canon hs) (samePat_canon hs) (by rw [hc, card_range])
    hP (rowsIn_canon hk s)

/-- `GU` reads only the equality pattern. -/
theorem GU_congr (k : ℕ) (w : Wt) {s t : T4} (h : canon s = canon t) : GU k w s = GU k w t := by
  unfold GU; rw [h]

end GridGen.Four
