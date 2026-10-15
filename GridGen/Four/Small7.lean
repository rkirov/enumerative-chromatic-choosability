/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.Exact

/-!
# Height four, `k = 7`: exact certificates for the five smallest mismatches

The mismatch triples `(μ₂, μ₃, μ₄) = (0,1,0), (0,2,0), (1,0,0), (0,0,1), (0,1,1)` determine the
lists up to relabelling, except `(0,1,1)`, which has four shapes. For each of the eight shapes,
a `Spec` lists the Venn sizes, the atoms a row of a state can lie in, and the multipliers of the
pins (rows in small atoms, `s₁ = s₃`, `s₂ = s₄`); `allOk` checks `(1 - y)·GB ≥ GU` on the box
for every column type by kernel evaluation, and `specOk` that the averaged gain is nonnegative.
The multipliers come from a linear program (`ai_research_notes/cx/h4loc/k7/gen7.py`), but only the checks
matter here.
-/

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace GridGen.Four

/-- The certificate for the mismatch shape `010`. -/
def s010 : Spec where
  venn := ⟨7, 7, 7, 7, 7, 6, 7, 6, 6, 6, 6, 6, 6, 6, 6⟩
  atoms := [(true, true, false, false), (true, true, true, true), (false, false, true, true)]
  pins := [(1, (true, true, false, false), 248, 1), (2, (false, false, true, true), 236, 1)]
  l13 := 4
  l24 := 4
  K := 125
  D := 8000

/-- The certificate for the mismatch shape `020`. -/
def s020 : Spec where
  venn := ⟨7, 7, 7, 7, 7, 5, 7, 5, 5, 5, 5, 5, 5, 5, 5⟩
  atoms := [(true, true, false, false), (true, true, true, true), (false, false, true, true)]
  pins := [(1, (true, true, false, false), 14514, 2), (2, (false, false, true, true), 13530, 2)]
  l13 := 246
  l24 := 246
  K := 14375
  D := 492000

/-- The certificate for the mismatch shape `100`. -/
def s100 : Spec where
  venn := ⟨7, 7, 7, 7, 6, 7, 7, 6, 7, 6, 6, 7, 6, 6, 6⟩
  atoms := [(false, true, true, true), (true, true, true, true), (true, false, false, false)]
  pins := [(0, (true, false, false, false), 31980, 1), (1, (false, true, true, true), 30504, 1), (3, (false, true, true, true), 984, 1)]
  l13 := 492
  l24 := 492
  K := 16375
  D := 984000

/-- The certificate for the mismatch shape `001`. -/
def s001 : Spec where
  venn := ⟨7, 7, 7, 7, 7, 7, 6, 7, 6, 6, 7, 6, 6, 6, 6⟩
  atoms := [(true, true, true, false), (true, true, true, true), (false, false, false, true)]
  pins := [(0, (true, true, true, false), 164, 1), (2, (true, true, true, false), 2706, 1), (3, (false, false, false, true), 2460, 1)]
  l13 := 41
  l24 := 41
  K := 1375
  D := 82000

/-- The certificate for the mismatch shape `011_76`. -/
def s011a : Spec where
  venn := ⟨7, 7, 7, 7, 7, 6, 6, 6, 7, 7, 6, 6, 7, 6, 6⟩
  atoms := [(true, true, false, true), (true, true, true, true), (false, false, true, false)]
  pins := [(1, (true, true, false, true), 12956, 1), (2, (false, false, true, false), 20664, 1), (3, (true, true, false, true), 10824, 1)]
  l13 := 164
  l24 := 164
  K := 11375
  D := 328000

/-- The certificate for the mismatch shape `011_66`. -/
def s011b : Spec where
  venn := ⟨7, 7, 7, 7, 7, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6⟩
  atoms := [(true, true, false, false), (true, true, true, true), (false, false, true, false), (false, false, false, true)]
  pins := [(1, (true, true, false, false), 7134, 1), (2, (false, false, true, false), 17712, 1), (3, (false, false, false, true), 6888, 1)]
  l13 := 123
  l24 := 123
  K := 8125
  D := 246000

/-- The certificate for the mismatch shape `011_65`. -/
def s011c : Spec where
  venn := ⟨7, 7, 7, 7, 7, 6, 6, 6, 6, 6, 6, 5, 6, 5, 5⟩
  atoms := [(true, true, false, true), (true, true, true, false), (true, true, true, true), (false, false, true, true)]
  pins := [(0, (true, true, true, false), 492, 1), (1, (true, true, false, true), 14514, 1), (2, (false, false, true, true), 13530, 1), (2, (true, true, true, false), 14514, 1), (3, (true, true, false, true), 18942, 1)]
  l13 := 246
  l24 := 246
  K := 15875
  D := 492000

/-- The certificate for the mismatch shape `011_55`. -/
def s011d : Spec where
  venn := ⟨7, 7, 7, 7, 7, 6, 6, 6, 5, 5, 6, 5, 5, 5, 5⟩
  atoms := [(true, true, false, false), (true, true, true, false), (true, true, true, true), (false, false, true, true), (false, false, false, true)]
  pins := [(0, (true, true, true, false), 123, 1), (1, (true, true, false, false), 2542, 1), (2, (false, false, true, true), 2255, 1), (2, (true, true, true, false), 2378, 1), (3, (false, false, false, true), 2460, 1)]
  l13 := 41
  l24 := 41
  K := 2500
  D := 82000


theorem ok_s010 : allOk s010 = true ∧ specOk s010 = true := by decide +kernel
theorem ok_s020 : allOk s020 = true ∧ specOk s020 = true := by decide +kernel
theorem ok_s100 : allOk s100 = true ∧ specOk s100 = true := by decide +kernel
theorem ok_s001 : allOk s001 = true ∧ specOk s001 = true := by decide +kernel
theorem ok_s011a : allOk s011a = true ∧ specOk s011a = true := by decide +kernel
theorem ok_s011b : allOk s011b = true ∧ specOk s011b = true := by decide +kernel
theorem ok_s011c : allOk s011c = true ∧ specOk s011c = true := by decide +kernel
theorem ok_s011d : allOk s011d = true ∧ specOk s011d = true := by decide +kernel


/-! ### Shapes -/

open Finset

/-- The Venn sizes of the shape `(C, C, C', C'')`. -/
theorem venn_shapeA (C C' C'' : Finset ℕ) :
    vennOf C C C' C'' = ⟨C.card, C.card, C'.card, C''.card, C.card, (C ∩ C').card, (C' ∩ C'').card,
      (C ∩ C').card, (C ∩ C'').card, (C ∩ C'').card, (C ∩ C').card, (C ∩ C' ∩ C'').card,
      (C ∩ C'').card, (C ∩ C' ∩ C'').card, (C ∩ C' ∩ C'').card⟩ := by
  simp only [vennOf, Finset.inter_self]

/-- The Venn sizes of the shape `(C', C, C, C)`. -/
theorem venn_shapeB (C' C : Finset ℕ) :
    vennOf C' C C C = ⟨C'.card, C.card, C.card, C.card, (C' ∩ C).card, C.card, C.card,
      (C' ∩ C).card, C.card, (C' ∩ C).card, (C' ∩ C).card, C.card, (C' ∩ C).card, (C' ∩ C).card,
      (C' ∩ C).card⟩ := by
  simp only [vennOf, Finset.inter_self, Finset.inter_assoc]

/-- Inclusion–exclusion for the atoms of three sets. -/
theorem atoms3 (C C' C'' : Finset ℕ) :
    ((C \ (C' ∪ C'')).card : ℤ) = C.card - (C ∩ C').card - (C ∩ C'').card + (C ∩ C' ∩ C'').card ∧
    ((C' \ (C ∪ C'')).card : ℤ) = C'.card - (C ∩ C').card - (C' ∩ C'').card + (C ∩ C' ∩ C'').card ∧
    ((C'' \ (C ∪ C')).card : ℤ) = C''.card - (C ∩ C'').card - (C' ∩ C'').card
      + (C ∩ C' ∩ C'').card ∧
    (((C ∩ C') \ C'').card : ℤ) = (C ∩ C').card - (C ∩ C' ∩ C'').card ∧
    (((C ∩ C'') \ C').card : ℤ) = (C ∩ C'').card - (C ∩ C' ∩ C'').card ∧
    (((C' ∩ C'') \ C).card : ℤ) = (C' ∩ C'').card - (C ∩ C' ∩ C'').card := by
  have sd : ∀ X Y : Finset ℕ, ((X \ Y).card : ℤ) = X.card - (X ∩ Y).card := fun X Y => by
    have := Finset.card_sdiff_add_card_inter X Y; omega
  have un : ∀ X Y Z : Finset ℕ, ((X ∩ (Y ∪ Z)).card : ℤ)
      = (X ∩ Y).card + (X ∩ Z).card - (X ∩ Y ∩ Z).card := fun X Y Z => by
    have h := Finset.card_union_add_card_inter (X ∩ Y) (X ∩ Z)
    rw [← Finset.inter_union_distrib_left] at h
    have e : X ∩ Y ∩ (X ∩ Z) = X ∩ Y ∩ Z := by ext x; simp only [Finset.mem_inter]; tauto
    rw [e] at h; omega
  have e1 : C' ∩ C = C ∩ C' := Finset.inter_comm _ _
  have e2 : C'' ∩ C = C ∩ C'' := Finset.inter_comm _ _
  have e3 : C'' ∩ C' = C' ∩ C'' := Finset.inter_comm _ _
  have t1 : C' ∩ C ∩ C'' = C ∩ C' ∩ C'' := by rw [e1]
  have t2 : C'' ∩ C ∩ C' = C ∩ C' ∩ C'' := by
    ext x; simp only [Finset.mem_inter]; tauto
  have t3 : C ∩ C' ∩ C'' = C ∩ C' ∩ C'' := rfl
  have t4 : C ∩ C'' ∩ C' = C ∩ C' ∩ C'' := by ext x; simp only [Finset.mem_inter]; tauto
  have t5 : C' ∩ C'' ∩ C = C ∩ C' ∩ C'' := by ext x; simp only [Finset.mem_inter]; tauto
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sd, un]; ring
  · rw [sd, un, e1]; ring
  · rw [sd, un, e2, e3, t4]; ring
  · rw [sd]
  · rw [sd, t4]
  · rw [sd, t5]

/-- The atom of three sets with membership `(u, v, w)`. -/
def atom3 (C C' C'' : Finset ℕ) : Bool → Bool → Bool → Finset ℕ
  | true, true, true => C ∩ C' ∩ C''
  | true, true, false => (C ∩ C') \ C''
  | true, false, true => (C ∩ C'') \ C'
  | false, true, true => (C' ∩ C'') \ C
  | true, false, false => C \ (C' ∪ C'')
  | false, true, false => C' \ (C ∪ C'')
  | false, false, true => C'' \ (C ∪ C')
  | false, false, false => ∅

theorem mem_atom3 {C C' C'' : Finset ℕ} {u v w : Bool} {c : ℕ}
    (h : decide (c ∈ C) = u ∧ decide (c ∈ C') = v ∧ decide (c ∈ C'') = w)
    (hne : (u, v, w) ≠ (false, false, false)) : c ∈ atom3 C C' C'' u v w := by
  obtain ⟨rfl, rfl, rfl⟩ := h
  by_cases h1 : c ∈ C <;> by_cases h2 : c ∈ C' <;> by_cases h3 : c ∈ C'' <;>
    simp_all [atom3]

theorem atomSet_A_le (C C' C'' : Finset ℕ) (u v w : Bool) (hne : (u, v, w) ≠ (false, false, false)) :
    (atomSet C C C' C'' (u, u, v, w)).card ≤ (atom3 C C' C'' u v w).card := by
  apply Finset.card_le_card
  intro c hc
  simp only [atomSet, Finset.mem_filter, memv, Prod.mk.injEq] at hc
  exact mem_atom3 ⟨hc.2.1, hc.2.2.2.1, hc.2.2.2.2⟩ hne

/-- Every colour of the shape `(C, C, C', C'')` lies in a listed atom, if the unlisted atoms are
empty. -/
theorem hat_A (sp : Spec) {C C' C'' : Finset ℕ}
    (h : ∀ u v w : Bool, (u, v, w) ≠ (false, false, false) → (u, u, v, w) ∉ sp.atoms →
      atom3 C C' C'' u v w = ∅) :
    ∀ c, memv C C C' C'' c ∈ sp.atoms ∨ memv C C C' C'' c = (false, false, false, false) := by
  intro c
  by_cases h0 : (decide (c ∈ C), decide (c ∈ C'), decide (c ∈ C'')) = (false, false, false)
  · right; simp only [Prod.mk.injEq] at h0; simp [memv, h0]
  · left
    by_contra hn
    have he := h _ _ _ h0 hn
    have hm := mem_atom3 (C := C) (C' := C') (C'' := C'') ⟨rfl, rfl, rfl⟩ h0
    rw [he] at hm; simp at hm

/-- The shape `(C', C, C, C)`: every colour lies in a listed atom. -/
theorem hat_B (sp : Spec) {C' C : Finset ℕ}
    (h : (true, true, true, true) ∈ sp.atoms ∧ (true, false, false, false) ∈ sp.atoms ∧
      (false, true, true, true) ∈ sp.atoms) :
    ∀ c, memv C' C C C c ∈ sp.atoms ∨ memv C' C C C c = (false, false, false, false) := by
  intro c
  by_cases h1 : c ∈ C' <;> by_cases h2 : c ∈ C <;> simp_all [memv]

theorem card_eq_zero_iff_int {X : Finset ℕ} (h : (X.card : ℤ) = 0) : X = ∅ := by
  exact Finset.card_eq_zero.mp (by exact_mod_cast h)

/-- **The seam inequality for the shape `(C, C, C', C'')`** from a certificate. -/
theorem seam_A (sp : Spec) (hok : allOk sp = true ∧ specOk sp = true) {C C' C'' : Finset ℕ}
    (hv : sp.venn = vennOf C C C' C'')
    (hemp : ∀ u v w : Bool, (u, v, w) ≠ (false, false, false) → (u, u, v, w) ∉ sp.atoms →
      atom3 C C' C'' u v w = ∅)
    (hsz : ∀ p ∈ sp.pins, ∃ u v w : Bool, p.2.1 = (u, u, v, w) ∧ (u, v, w) ≠ (false, false, false)
      ∧ ((atom3 C C' C'' u v w).card : ℤ) ≤ p.2.2.2)
    {w : Wt} (hw : InBox 7 w) {X₁ X₂ X₃ X₄ : Finset ℕ}
    (hX₁ : 7 - 1 ≤ X₁.card) (hX₂ : 7 - 1 ≤ X₂.card) (hX₃ : 7 - 1 ≤ X₃.card)
    (hX₄ : 7 - 1 ≤ X₄.card) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄, GU 7 w s ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄, GB w C C C' C'' s := by
  refine exact_seam sp hok.1 hok.2 hv (hat_A sp hemp) ?_ hw hX₁ hX₂ hX₃ hX₄
  intro p hp
  obtain ⟨u, v, w', hpm, hne, hle⟩ := hsz p hp
  rw [hpm]
  have := atomSet_A_le C C' C'' u v w' hne
  have : ((atomSet C C C' C'' (u, u, v, w')).card : ℤ) ≤ (atom3 C C' C'' u v w').card := by
    exact_mod_cast this
  linarith

/-- **The seam inequality for the shape `(C', C, C, C)`** from a certificate. -/
theorem seam_B (sp : Spec) (hok : allOk sp = true ∧ specOk sp = true) {C' C : Finset ℕ}
    (hv : sp.venn = vennOf C' C C C)
    (hatoms : (true, true, true, true) ∈ sp.atoms ∧ (true, false, false, false) ∈ sp.atoms ∧
      (false, true, true, true) ∈ sp.atoms)
    (hsz : ∀ p ∈ sp.pins, (p.2.1 = (true, false, false, false) ∧ ((C' \ C).card : ℤ) ≤ p.2.2.2)
      ∨ (p.2.1 = (false, true, true, true) ∧ ((C \ C').card : ℤ) ≤ p.2.2.2))
    {w : Wt} (hw : InBox 7 w) {X₁ X₂ X₃ X₄ : Finset ℕ}
    (hX₁ : 7 - 1 ≤ X₁.card) (hX₂ : 7 - 1 ≤ X₂.card) (hX₃ : 7 - 1 ≤ X₃.card)
    (hX₄ : 7 - 1 ≤ X₄.card) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄, GU 7 w s ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄, GB w C' C C C s := by
  refine exact_seam sp hok.1 hok.2 hv (hat_B sp hatoms) ?_ hw hX₁ hX₂ hX₃ hX₄
  intro p hp
  rcases hsz p hp with ⟨hm, hle⟩ | ⟨hm, hle⟩
  · rw [hm]
    have : (atomSet C' C C C (true, false, false, false)).card ≤ (C' \ C).card := by
      apply Finset.card_le_card; intro c hc
      simp only [atomSet, Finset.mem_filter, memv, Prod.mk.injEq, decide_eq_true_eq,
        decide_eq_false_iff_not] at hc
      exact Finset.mem_sdiff.mpr ⟨hc.2.1, hc.2.2.1⟩
    have : ((atomSet C' C C C (true, false, false, false)).card : ℤ) ≤ (C' \ C).card := by
      exact_mod_cast this
    linarith
  · rw [hm]
    have : (atomSet C' C C C (false, true, true, true)).card ≤ (C \ C').card := by
      apply Finset.card_le_card; intro c hc
      simp only [atomSet, Finset.mem_filter, memv, Prod.mk.injEq, decide_eq_true_eq,
        decide_eq_false_iff_not] at hc
      exact Finset.mem_sdiff.mpr ⟨hc.2.2.1, hc.2.1⟩
    have : ((atomSet C' C C C (false, true, true, true)).card : ℤ) ≤ (C \ C').card := by
      exact_mod_cast this
    linarith

theorem seam_s010 {C C' C'' : Finset ℕ} (hC : C.card = 7) (hC' : C'.card = 7)
    (hC'' : C''.card = 7) (ha : (C ∩ C').card = 6) (hb : (C' ∩ C'').card = 7)
    (hx : (C ∩ C'').card = 6) (hy : (C ∩ C' ∩ C'').card = 6)
    {w : Wt} (hw : InBox 7 w) {X₁ X₂ X₃ X₄ : Finset ℕ}
    (hX₁ : 7 - 1 ≤ X₁.card) (hX₂ : 7 - 1 ≤ X₂.card) (hX₃ : 7 - 1 ≤ X₃.card)
    (hX₄ : 7 - 1 ≤ X₄.card) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄, GU 7 w s ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄, GB w C C C' C'' s := by
  obtain ⟨o1, o2, o3, o12, o13, o23⟩ := atoms3 C C' C''
  simp only [hC, hC', hC'', ha, hb, hx, hy] at o1 o2 o3 o12 o13 o23
  refine seam_A s010 ok_s010 ?_ ?_ ?_ hw hX₁ hX₂ hX₃ hX₄
  · rw [venn_shapeA, hC, hC', hC'', ha, hb, hx, hy]; rfl
  · intro u v w' hne hnot
    cases u <;> cases v <;> cases w'
    all_goals first
      | exact absurd rfl hne
      | (exfalso; apply hnot; simp [s010]; done)
      | (apply card_eq_zero_iff_int; simp only [atom3]; omega)
  · intro p hp
    simp only [s010, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (refine ⟨true, false, false, rfl, by decide, ?_⟩; simp only [atom3]; omega)
      | (refine ⟨false, true, true, rfl, by decide, ?_⟩; simp only [atom3]; omega)
      | (refine ⟨true, true, false, rfl, by decide, ?_⟩; simp only [atom3]; omega)
      | (refine ⟨true, false, true, rfl, by decide, ?_⟩; simp only [atom3]; omega)
      | (refine ⟨false, true, false, rfl, by decide, ?_⟩; simp only [atom3]; omega)
      | (refine ⟨false, false, true, rfl, by decide, ?_⟩; simp only [atom3]; omega)

theorem seam_s020 {C C' C'' : Finset ℕ} (hC : C.card = 7) (hC' : C'.card = 7)
    (hC'' : C''.card = 7) (ha : (C ∩ C').card = 5) (hb : (C' ∩ C'').card = 7)
    (hx : (C ∩ C'').card = 5) (hy : (C ∩ C' ∩ C'').card = 5)
    {w : Wt} (hw : InBox 7 w) {X₁ X₂ X₃ X₄ : Finset ℕ}
    (hX₁ : 7 - 1 ≤ X₁.card) (hX₂ : 7 - 1 ≤ X₂.card) (hX₃ : 7 - 1 ≤ X₃.card)
    (hX₄ : 7 - 1 ≤ X₄.card) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄, GU 7 w s ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄, GB w C C C' C'' s := by
  obtain ⟨o1, o2, o3, o12, o13, o23⟩ := atoms3 C C' C''
  simp only [hC, hC', hC'', ha, hb, hx, hy] at o1 o2 o3 o12 o13 o23
  refine seam_A s020 ok_s020 ?_ ?_ ?_ hw hX₁ hX₂ hX₃ hX₄
  · rw [venn_shapeA, hC, hC', hC'', ha, hb, hx, hy]; rfl
  · intro u v w' hne hnot
    cases u <;> cases v <;> cases w'
    all_goals first
      | exact absurd rfl hne
      | (exfalso; apply hnot; simp [s020]; done)
      | (apply card_eq_zero_iff_int; simp only [atom3]; omega)
  · intro p hp
    simp only [s020, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (refine ⟨true, false, false, rfl, by decide, ?_⟩; simp only [atom3]; omega)
      | (refine ⟨false, true, true, rfl, by decide, ?_⟩; simp only [atom3]; omega)
      | (refine ⟨true, true, false, rfl, by decide, ?_⟩; simp only [atom3]; omega)
      | (refine ⟨true, false, true, rfl, by decide, ?_⟩; simp only [atom3]; omega)
      | (refine ⟨false, true, false, rfl, by decide, ?_⟩; simp only [atom3]; omega)
      | (refine ⟨false, false, true, rfl, by decide, ?_⟩; simp only [atom3]; omega)

theorem seam_s001 {C C' C'' : Finset ℕ} (hC : C.card = 7) (hC' : C'.card = 7)
    (hC'' : C''.card = 7) (ha : (C ∩ C').card = 7) (hb : (C' ∩ C'').card = 6)
    (hx : (C ∩ C'').card = 6) (hy : (C ∩ C' ∩ C'').card = 6)
    {w : Wt} (hw : InBox 7 w) {X₁ X₂ X₃ X₄ : Finset ℕ}
    (hX₁ : 7 - 1 ≤ X₁.card) (hX₂ : 7 - 1 ≤ X₂.card) (hX₃ : 7 - 1 ≤ X₃.card)
    (hX₄ : 7 - 1 ≤ X₄.card) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄, GU 7 w s ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄, GB w C C C' C'' s := by
  obtain ⟨o1, o2, o3, o12, o13, o23⟩ := atoms3 C C' C''
  simp only [hC, hC', hC'', ha, hb, hx, hy] at o1 o2 o3 o12 o13 o23
  refine seam_A s001 ok_s001 ?_ ?_ ?_ hw hX₁ hX₂ hX₃ hX₄
  · rw [venn_shapeA, hC, hC', hC'', ha, hb, hx, hy]; rfl
  · intro u v w' hne hnot
    cases u <;> cases v <;> cases w'
    all_goals first
      | exact absurd rfl hne
      | (exfalso; apply hnot; simp [s001]; done)
      | (apply card_eq_zero_iff_int; simp only [atom3]; omega)
  · intro p hp
    simp only [s001, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (refine ⟨true, false, false, rfl, by decide, ?_⟩; simp only [atom3]; omega)
      | (refine ⟨false, true, true, rfl, by decide, ?_⟩; simp only [atom3]; omega)
      | (refine ⟨true, true, false, rfl, by decide, ?_⟩; simp only [atom3]; omega)
      | (refine ⟨true, false, true, rfl, by decide, ?_⟩; simp only [atom3]; omega)
      | (refine ⟨false, true, false, rfl, by decide, ?_⟩; simp only [atom3]; omega)
      | (refine ⟨false, false, true, rfl, by decide, ?_⟩; simp only [atom3]; omega)

theorem seam_s011a {C C' C'' : Finset ℕ} (hC : C.card = 7) (hC' : C'.card = 7)
    (hC'' : C''.card = 7) (ha : (C ∩ C').card = 6) (hb : (C' ∩ C'').card = 6)
    (hx : (C ∩ C'').card = 7) (hy : (C ∩ C' ∩ C'').card = 6)
    {w : Wt} (hw : InBox 7 w) {X₁ X₂ X₃ X₄ : Finset ℕ}
    (hX₁ : 7 - 1 ≤ X₁.card) (hX₂ : 7 - 1 ≤ X₂.card) (hX₃ : 7 - 1 ≤ X₃.card)
    (hX₄ : 7 - 1 ≤ X₄.card) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄, GU 7 w s ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄, GB w C C C' C'' s := by
  obtain ⟨o1, o2, o3, o12, o13, o23⟩ := atoms3 C C' C''
  simp only [hC, hC', hC'', ha, hb, hx, hy] at o1 o2 o3 o12 o13 o23
  refine seam_A s011a ok_s011a ?_ ?_ ?_ hw hX₁ hX₂ hX₃ hX₄
  · rw [venn_shapeA, hC, hC', hC'', ha, hb, hx, hy]; rfl
  · intro u v w' hne hnot
    cases u <;> cases v <;> cases w'
    all_goals first
      | exact absurd rfl hne
      | (exfalso; apply hnot; simp [s011a]; done)
      | (apply card_eq_zero_iff_int; simp only [atom3]; omega)
  · intro p hp
    simp only [s011a, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (refine ⟨true, false, false, rfl, by decide, ?_⟩; simp only [atom3]; omega)
      | (refine ⟨false, true, true, rfl, by decide, ?_⟩; simp only [atom3]; omega)
      | (refine ⟨true, true, false, rfl, by decide, ?_⟩; simp only [atom3]; omega)
      | (refine ⟨true, false, true, rfl, by decide, ?_⟩; simp only [atom3]; omega)
      | (refine ⟨false, true, false, rfl, by decide, ?_⟩; simp only [atom3]; omega)
      | (refine ⟨false, false, true, rfl, by decide, ?_⟩; simp only [atom3]; omega)

theorem seam_s011b {C C' C'' : Finset ℕ} (hC : C.card = 7) (hC' : C'.card = 7)
    (hC'' : C''.card = 7) (ha : (C ∩ C').card = 6) (hb : (C' ∩ C'').card = 6)
    (hx : (C ∩ C'').card = 6) (hy : (C ∩ C' ∩ C'').card = 6)
    {w : Wt} (hw : InBox 7 w) {X₁ X₂ X₃ X₄ : Finset ℕ}
    (hX₁ : 7 - 1 ≤ X₁.card) (hX₂ : 7 - 1 ≤ X₂.card) (hX₃ : 7 - 1 ≤ X₃.card)
    (hX₄ : 7 - 1 ≤ X₄.card) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄, GU 7 w s ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄, GB w C C C' C'' s := by
  obtain ⟨o1, o2, o3, o12, o13, o23⟩ := atoms3 C C' C''
  simp only [hC, hC', hC'', ha, hb, hx, hy] at o1 o2 o3 o12 o13 o23
  refine seam_A s011b ok_s011b ?_ ?_ ?_ hw hX₁ hX₂ hX₃ hX₄
  · rw [venn_shapeA, hC, hC', hC'', ha, hb, hx, hy]; rfl
  · intro u v w' hne hnot
    cases u <;> cases v <;> cases w'
    all_goals first
      | exact absurd rfl hne
      | (exfalso; apply hnot; simp [s011b]; done)
      | (apply card_eq_zero_iff_int; simp only [atom3]; omega)
  · intro p hp
    simp only [s011b, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (refine ⟨true, false, false, rfl, by decide, ?_⟩; simp only [atom3]; omega)
      | (refine ⟨false, true, true, rfl, by decide, ?_⟩; simp only [atom3]; omega)
      | (refine ⟨true, true, false, rfl, by decide, ?_⟩; simp only [atom3]; omega)
      | (refine ⟨true, false, true, rfl, by decide, ?_⟩; simp only [atom3]; omega)
      | (refine ⟨false, true, false, rfl, by decide, ?_⟩; simp only [atom3]; omega)
      | (refine ⟨false, false, true, rfl, by decide, ?_⟩; simp only [atom3]; omega)

theorem seam_s011c {C C' C'' : Finset ℕ} (hC : C.card = 7) (hC' : C'.card = 7)
    (hC'' : C''.card = 7) (ha : (C ∩ C').card = 6) (hb : (C' ∩ C'').card = 6)
    (hx : (C ∩ C'').card = 6) (hy : (C ∩ C' ∩ C'').card = 5)
    {w : Wt} (hw : InBox 7 w) {X₁ X₂ X₃ X₄ : Finset ℕ}
    (hX₁ : 7 - 1 ≤ X₁.card) (hX₂ : 7 - 1 ≤ X₂.card) (hX₃ : 7 - 1 ≤ X₃.card)
    (hX₄ : 7 - 1 ≤ X₄.card) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄, GU 7 w s ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄, GB w C C C' C'' s := by
  obtain ⟨o1, o2, o3, o12, o13, o23⟩ := atoms3 C C' C''
  simp only [hC, hC', hC'', ha, hb, hx, hy] at o1 o2 o3 o12 o13 o23
  refine seam_A s011c ok_s011c ?_ ?_ ?_ hw hX₁ hX₂ hX₃ hX₄
  · rw [venn_shapeA, hC, hC', hC'', ha, hb, hx, hy]; rfl
  · intro u v w' hne hnot
    cases u <;> cases v <;> cases w'
    all_goals first
      | exact absurd rfl hne
      | (exfalso; apply hnot; simp [s011c]; done)
      | (apply card_eq_zero_iff_int; simp only [atom3]; omega)
  · intro p hp
    simp only [s011c, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (refine ⟨true, false, false, rfl, by decide, ?_⟩; simp only [atom3]; omega)
      | (refine ⟨false, true, true, rfl, by decide, ?_⟩; simp only [atom3]; omega)
      | (refine ⟨true, true, false, rfl, by decide, ?_⟩; simp only [atom3]; omega)
      | (refine ⟨true, false, true, rfl, by decide, ?_⟩; simp only [atom3]; omega)
      | (refine ⟨false, true, false, rfl, by decide, ?_⟩; simp only [atom3]; omega)
      | (refine ⟨false, false, true, rfl, by decide, ?_⟩; simp only [atom3]; omega)

theorem seam_s011d {C C' C'' : Finset ℕ} (hC : C.card = 7) (hC' : C'.card = 7)
    (hC'' : C''.card = 7) (ha : (C ∩ C').card = 6) (hb : (C' ∩ C'').card = 6)
    (hx : (C ∩ C'').card = 5) (hy : (C ∩ C' ∩ C'').card = 5)
    {w : Wt} (hw : InBox 7 w) {X₁ X₂ X₃ X₄ : Finset ℕ}
    (hX₁ : 7 - 1 ≤ X₁.card) (hX₂ : 7 - 1 ≤ X₂.card) (hX₃ : 7 - 1 ≤ X₃.card)
    (hX₄ : 7 - 1 ≤ X₄.card) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄, GU 7 w s ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄, GB w C C C' C'' s := by
  obtain ⟨o1, o2, o3, o12, o13, o23⟩ := atoms3 C C' C''
  simp only [hC, hC', hC'', ha, hb, hx, hy] at o1 o2 o3 o12 o13 o23
  refine seam_A s011d ok_s011d ?_ ?_ ?_ hw hX₁ hX₂ hX₃ hX₄
  · rw [venn_shapeA, hC, hC', hC'', ha, hb, hx, hy]; rfl
  · intro u v w' hne hnot
    cases u <;> cases v <;> cases w'
    all_goals first
      | exact absurd rfl hne
      | (exfalso; apply hnot; simp [s011d]; done)
      | (apply card_eq_zero_iff_int; simp only [atom3]; omega)
  · intro p hp
    simp only [s011d, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (refine ⟨true, false, false, rfl, by decide, ?_⟩; simp only [atom3]; omega)
      | (refine ⟨false, true, true, rfl, by decide, ?_⟩; simp only [atom3]; omega)
      | (refine ⟨true, true, false, rfl, by decide, ?_⟩; simp only [atom3]; omega)
      | (refine ⟨true, false, true, rfl, by decide, ?_⟩; simp only [atom3]; omega)
      | (refine ⟨false, true, false, rfl, by decide, ?_⟩; simp only [atom3]; omega)
      | (refine ⟨false, false, true, rfl, by decide, ?_⟩; simp only [atom3]; omega)

theorem seam_s100 {C' C : Finset ℕ} (hC' : C'.card = 7) (hC : C.card = 7)
    (ha : (C' ∩ C).card = 6)
    {w : Wt} (hw : InBox 7 w) {X₁ X₂ X₃ X₄ : Finset ℕ}
    (hX₁ : 7 - 1 ≤ X₁.card) (hX₂ : 7 - 1 ≤ X₂.card) (hX₃ : 7 - 1 ≤ X₃.card)
    (hX₄ : 7 - 1 ≤ X₄.card) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄, GU 7 w s ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄, GB w C' C C C s := by
  have d1 : ((C' \ C).card : ℤ) = 1 := by
    have := Finset.card_sdiff_add_card_inter C' C; omega
  have d2 : ((C \ C').card : ℤ) = 1 := by
    have := Finset.card_sdiff_add_card_inter C C'; rw [Finset.inter_comm] at this; omega
  refine seam_B s100 ok_s100 ?_ (by simp [s100]) ?_ hw hX₁ hX₂ hX₃ hX₄
  · rw [venn_shapeB, hC', hC, ha]; rfl
  · intro p hp
    simp only [s100, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · left; exact ⟨rfl, by rw [d1]; norm_num⟩
    · right; exact ⟨rfl, by rw [d2]; norm_num⟩
    · right; exact ⟨rfl, by rw [d2]; norm_num⟩


end GridGen.Four
