/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.K4.Defs

/-!
# Height four at `k = 4`: the seam vector under renaming and reversal

The seam vector `dvec Y B` is unchanged when the colours are renamed by a map injective on all
colours of `Y` and `B` (`dvec_image`), and when the four rows are reversed (`dvec_rev`). These
are the two symmetries ("renaming of used colours and reversal of the four rows") under which
Codex's classification of the negative seams is stated
(`ai_research_notes/cx/h4k4b/NOTE.md`).
-/

namespace GridGen.Four.K4

open Finset

/-- All colours of the lists of a column. -/
def uni (Y : Col) : Finset ℕ := Y.1 ∪ Y.2.1 ∪ Y.2.2.1 ∪ Y.2.2.2

/-- Rename the colours of every list. -/
def imgC (f : ℕ → ℕ) (Y : Col) : Col :=
  (Y.1.image f, Y.2.1.image f, Y.2.2.1.image f, Y.2.2.2.image f)

theorem ce_congr {s t : T4} (h : SamePat s t) : ce s = ce t := by
  obtain ⟨h13, h24, h14⟩ := h
  simp only [ce, h13, h24, h14]

theorem hrow_congr {s t : T4} (h : SamePat s t) : hrow s = hrow t := by
  obtain ⟨h13, h24, h14⟩ := h
  simp only [hrow, h13, h24, h14]

theorem rowsIn_uni {Y : Col} {t : T4} (ht : t ∈ stsC Y) : RowsIn t (uni Y) := by
  unfold stsC at ht
  rw [mem_sts] at ht
  unfold uni RowsIn
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1]

theorem stsC_image {f : ℕ → ℕ} {Y : Col} (hf : Set.InjOn f ↑(uni Y)) :
    stsC (imgC f Y) = (stsC Y).image (mapT f) := by
  ext t
  simp only [Finset.mem_image]
  constructor
  · intro ht
    unfold stsC imgC at ht
    rw [mem_sts] at ht
    obtain ⟨h1, h2, h3, h4, p1, p2, p3⟩ := ht
    obtain ⟨x1, hx1, e1⟩ := Finset.mem_image.mp h1
    obtain ⟨x2, hx2, e2⟩ := Finset.mem_image.mp h2
    obtain ⟨x3, hx3, e3⟩ := Finset.mem_image.mp h3
    obtain ⟨x4, hx4, e4⟩ := Finset.mem_image.mp h4
    refine ⟨(x1, x2, x3, x4), ?_, ?_⟩
    · unfold stsC
      rw [mem_sts]
      refine ⟨hx1, hx2, hx3, hx4, fun h => p1 ?_, fun h => p2 ?_, fun h => p3 ?_⟩
      · simp only [r1, r2] at h; rw [← e1, ← e2, h]
      · simp only [r2, r3] at h; rw [← e2, ← e3, h]
      · simp only [r3, r4] at h; rw [← e3, ← e4, h]
    · obtain ⟨t1, t2, t3, t4⟩ := t
      simp only [mapT, r1, r2, r3, r4] at e1 e2 e3 e4 ⊢
      rw [e1, e2, e3, e4]
  · rintro ⟨s, hs, rfl⟩
    have hr := rowsIn_uni hs
    unfold stsC at hs
    unfold stsC imgC
    rw [mem_sts] at hs ⊢
    obtain ⟨h1, h2, h3, h4, p1, p2, p3⟩ := hs
    exact ⟨mem_image_of_mem f h1, mem_image_of_mem f h2, mem_image_of_mem f h3,
      mem_image_of_mem f h4, fun h => p1 (hf hr.1 hr.2.1 h), fun h => p2 (hf hr.2.1 hr.2.2.1 h),
      fun h => p3 (hf hr.2.2.1 hr.2.2.2 h)⟩

theorem mapT_injOn {f : ℕ → ℕ} {Y : Col} (hf : Set.InjOn f ↑(uni Y)) :
    Set.InjOn (mapT f) ↑(stsC Y) := by
  intro t ht u hu h
  have ht' := rowsIn_uni (Finset.mem_coe.mp ht)
  have hu' := rowsIn_uni (Finset.mem_coe.mp hu)
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

theorem sum_stsC_image {β : Type*} [AddCommMonoid β] {f : ℕ → ℕ} {Y : Col}
    (hf : Set.InjOn f ↑(uni Y)) (φ : T4 → β) :
    ∑ t ∈ stsC (imgC f Y), φ t = ∑ t ∈ stsC Y, φ (mapT f t) := by
  rw [stsC_image hf, Finset.sum_image (mapT_injOn hf)]

theorem cnt_image {f : ℕ → ℕ} {Y : Col} (hf : Set.InjOn f ↑(uni Y)) :
    cnt (imgC f Y) = cnt Y := by
  unfold cnt
  rw [sum_stsC_image hf]
  exact Finset.sum_congr rfl fun t ht => ce_congr (samePat_mapT hf (rowsIn_uni ht))

theorem image_erase_injOn {g : ℕ → ℕ} {P : Finset ℕ} {x : ℕ} (hg : Set.InjOn g ↑(insert x P)) :
    (P.erase x).image g = (P.image g).erase (g x) := by
  ext y
  simp only [Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨z, ⟨hzx, hz⟩, rfl⟩
    refine ⟨fun h => hzx (hg (by simp [hz]) (by simp) h), z, hz, rfl⟩
  · rintro ⟨hy, z, hz, rfl⟩
    exact ⟨z, ⟨fun h => hy (by rw [h]), hz⟩, rfl⟩

theorem uni_ers_subset (B : Col) (s : T4) : uni (ers B s) ⊆ uni B := by
  intro c hc
  simp only [uni, ers, Finset.mem_union, Finset.mem_erase] at hc ⊢
  tauto

theorem ers_image {f : ℕ → ℕ} {B : Col} {s : T4} {P : Finset ℕ} (hf : Set.InjOn f ↑P)
    (hB : uni B ⊆ P) (hs : RowsIn s P) : ers (imgC f B) (mapT f s) = imgC f (ers B s) := by
  have sub : ∀ (x : ℕ) (L : Finset ℕ), x ∈ P → L ⊆ uni B → (↑(insert x L) : Set ℕ) ⊆ ↑P := by
    intro x L hx hL c hc
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hc
    rcases hc with rfl | hc
    · exact hx
    · exact hB (hL hc)
  have l1 : B.1 ⊆ uni B := fun c hc => by simp [uni, hc]
  have l2 : B.2.1 ⊆ uni B := fun c hc => by simp [uni, hc]
  have l3 : B.2.2.1 ⊆ uni B := fun c hc => by simp [uni, hc]
  have l4 : B.2.2.2 ⊆ uni B := fun c hc => by simp [uni, hc]
  simp only [ers, imgC, mapT, r1, r2, r3, r4]
  rw [image_erase_injOn (hf.mono (sub _ _ hs.1 l1)),
    image_erase_injOn (hf.mono (sub _ _ hs.2.1 l2)),
    image_erase_injOn (hf.mono (sub _ _ hs.2.2.1 l3)),
    image_erase_injOn (hf.mono (sub _ _ hs.2.2.2 l4))]

/-- **Renaming invariance of the seam vector.** -/
theorem dvec_image {f : ℕ → ℕ} {Y B : Col} (hf : Set.InjOn f ↑(uni Y ∪ uni B)) :
    dvec (imgC f Y) (imgC f B) = dvec Y B := by
  have hY : Set.InjOn f ↑(uni Y) := hf.mono (Finset.coe_subset.mpr subset_union_left)
  unfold dvec
  rw [sum_stsC_image hY]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hr : RowsIn s (uni Y ∪ uni B) := by
    obtain ⟨h1, h2, h3, h4⟩ := rowsIn_uni hs
    exact ⟨mem_union_left _ h1, mem_union_left _ h2, mem_union_left _ h3, mem_union_left _ h4⟩
  rw [ers_image hf subset_union_right hr,
    cnt_image (hf.mono (by
      intro c hc
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]
      exact Or.inr (uni_ers_subset B s hc))),
    hrow_congr (samePat_mapT hY (rowsIn_uni hs))]

/-! ### Reversal of the rows -/

/-- Reverse the rows of a column. -/
def revT (t : T4) : T4 := (r4 t, r3 t, r2 t, r1 t)

/-- Reverse the lists of a column. -/
def revC (Y : Col) : Col := (Y.2.2.2, Y.2.2.1, Y.2.1, Y.1)

theorem revT_revT (t : T4) : revT (revT t) = t := by
  obtain ⟨a, b, c, d⟩ := t; rfl

theorem revC_revC (Y : Col) : revC (revC Y) = Y := by
  obtain ⟨a, b, c, d⟩ := Y; rfl

theorem stsC_rev (Y : Col) : stsC (revC Y) = (stsC Y).image revT := by
  ext t
  simp only [Finset.mem_image]
  constructor
  · intro ht
    refine ⟨revT t, ?_, revT_revT t⟩
    unfold stsC revC at ht
    unfold stsC
    rw [mem_sts] at ht ⊢
    obtain ⟨h1, h2, h3, h4, p1, p2, p3⟩ := ht
    exact ⟨h4, h3, h2, h1, Ne.symm p3, Ne.symm p2, Ne.symm p1⟩
  · rintro ⟨s, hs, rfl⟩
    unfold stsC at hs
    unfold stsC revC
    rw [mem_sts] at hs ⊢
    obtain ⟨h1, h2, h3, h4, p1, p2, p3⟩ := hs
    exact ⟨h4, h3, h2, h1, Ne.symm p3, Ne.symm p2, Ne.symm p1⟩

theorem ce_rev (t : T4) : ce (revT t) = ce t := by
  obtain ⟨a, b, c, d⟩ := t
  simp only [ce, revT, r1, r2, r3, r4]
  by_cases h1 : a = c <;> by_cases h2 : b = d <;> by_cases h3 : a = d <;>
    simp [h1, h2, h3, eq_comm]

theorem hrow_rev (t : T4) : hrow (revT t) = hrow t := by
  obtain ⟨a, b, c, d⟩ := t
  simp only [hrow, revT, r1, r2, r3, r4]
  by_cases h1 : a = c <;> by_cases h2 : b = d <;> by_cases h3 : a = d <;>
    simp [h1, h2, h3, eq_comm]

theorem sum_stsC_rev {β : Type*} [AddCommMonoid β] (Y : Col) (φ : T4 → β) :
    ∑ t ∈ stsC (revC Y), φ t = ∑ t ∈ stsC Y, φ (revT t) := by
  rw [stsC_rev, Finset.sum_image (fun s _ t _ h => by rw [← revT_revT s, h, revT_revT])]

theorem cnt_rev (Y : Col) : cnt (revC Y) = cnt Y := by
  unfold cnt
  rw [sum_stsC_rev]
  exact Finset.sum_congr rfl fun t _ => ce_rev t

theorem ers_rev (B : Col) (s : T4) : ers (revC B) (revT s) = revC (ers B s) := rfl

/-- **Reversal invariance of the seam vector.** -/
theorem dvec_rev (Y B : Col) : dvec (revC Y) (revC B) = dvec Y B := by
  unfold dvec
  rw [sum_stsC_rev]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [ers_rev, cnt_rev, hrow_rev]

end GridGen.Four.K4
