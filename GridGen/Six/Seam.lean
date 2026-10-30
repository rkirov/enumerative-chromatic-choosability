/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Six.CoverData
import GridGen.Six.Bridge
import GridGen.Six.Zero
import GridGen.Six.ExData.A3
import GridGen.Six.ExData.A4
import GridGen.Six.ExData.A5

/-!
# Height six at `k = 6`: the seam inequality

The mismatches `μᵣ = 6 - |Bᵣ ∩ Bᵣ₊₁|` form a vector in `[0, 6]⁵`. Up to row reflection
(`seam_of_rev`) every vector is `0` (relabelling, `seam_zero66`), one of the three
single-mismatch shapes (exact certificates, `seam_shape3/4/5`), a class closed by a dual
certificate over the state bits (`lpAll`, `ppAll`) or a pointwise class (`pwAll`): Codex's
(OpenAI) split, `ai_research_notes/cx/h6k6/NOTE.md`, checked in
`ai_research_notes/H6_K6_REVIEW_2026-10-29.md`. The covering is a kernel check over the
`7⁵` vectors with a bit mask of the representatives (`coverA`, `repMask_eq`).
-/

namespace GridGen.Six

open Finset

/-! ### The representatives -/

/-- The exactly certified shapes. -/
def exL : List (List ℕ) := [[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]]

/-- All certified representatives. -/
def allReps : List (List ℕ) := exL ++ lpAll.map BCert6.mu ++ ppAll.map BCert6.mu ++ pwAll

/-- The key of a mismatch vector. -/
def mkey (m : List ℕ) : ℕ :=
  (((m.getD 0 0 * 7 + m.getD 1 0) * 7 + m.getD 2 0) * 7 + m.getD 3 0) * 7 + m.getD 4 0

/-- The mask of a list of vectors. -/
def mmask (L : List (List ℕ)) : ℕ := L.foldr (fun m acc => 2 ^ mkey m ||| acc) 0

theorem mmask_testBit : ∀ (L : List (List ℕ)) (k : ℕ), (mmask L).testBit k = true →
    ∃ m ∈ L, mkey m = k
  | [], k, h => by simp [mmask] at h
  | m :: L, k, h => by
    simp only [mmask, List.foldr_cons, Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow,
      decide_eq_true_eq] at h
    rcases h with h | h
    · exact ⟨m, List.mem_cons_self, h⟩
    · obtain ⟨m', hm', e⟩ := mmask_testBit L k h
      exact ⟨m', List.mem_cons_of_mem _ hm', e⟩

theorem repMask_eq : mmask allReps = repMaskL := by decide +kernel

theorem reps_ok : allReps.all (fun m => decide (m.length = 5 ∧ ∀ x ∈ m, x < 7)) = true := by
  decide +kernel

/-- **The covering of the vectors with first entry `a`**: zero, or a representative up to
reflection. -/
def coverA (a : ℕ) : Bool :=
  (List.range 7).all fun b => (List.range 7).all fun c =>
    (List.range 7).all fun d => (List.range 7).all fun e =>
      (a == 0 && b == 0 && c == 0 && d == 0 && e == 0) ||
      repMaskL.testBit (mkey [a, b, c, d, e]) || repMaskL.testBit (mkey [e, d, c, b, a])

theorem coverA0 : coverA 0 = true := by decide +kernel
theorem coverA1 : coverA 1 = true := by decide +kernel
theorem coverA2 : coverA 2 = true := by decide +kernel
theorem coverA3 : coverA 3 = true := by decide +kernel
theorem coverA4 : coverA 4 = true := by decide +kernel
theorem coverA5 : coverA 5 = true := by decide +kernel
theorem coverA6 : coverA 6 = true := by decide +kernel

theorem coverA_ok {a : ℕ} (ha : a < 7) : coverA a = true := by
  interval_cases a
  exacts [coverA0, coverA1, coverA2, coverA3, coverA4, coverA5, coverA6]

theorem mem_allReps_of {a b c d e : ℕ} (ha : a < 7) (hb : b < 7) (hc : c < 7) (hd : d < 7)
    (he : e < 7) (h : repMaskL.testBit (mkey [a, b, c, d, e]) = true) :
    [a, b, c, d, e] ∈ allReps := by
  rw [← repMask_eq] at h
  obtain ⟨m, hm, hk⟩ := mmask_testBit allReps _ h
  have hc6 := reps_ok
  simp only [List.all_eq_true, decide_eq_true_eq] at hc6
  obtain ⟨hl, hlt⟩ := hc6 m hm
  match m, hl with
  | [x1, x2, x3, x4, x5], _ =>
    have l1 := hlt x1 (by simp)
    have l2 := hlt x2 (by simp)
    have l3 := hlt x3 (by simp)
    have l4 := hlt x4 (by simp)
    have l5 := hlt x5 (by simp)
    simp only [mkey, List.getD_cons_zero, List.getD_cons_succ] at hk
    have : x1 = a ∧ x2 = b ∧ x3 = c ∧ x4 = d ∧ x5 = e := by omega
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := this
    exact hm

/-! ### The seam on a representative -/

section seams

variable {w : Wt6} {X₁ X₂ X₃ X₄ X₅ X₆ B₁ B₂ B₃ B₄ B₅ B₆ : Finset ℕ}

theorem eq_of_inter_card {A B : Finset ℕ} (hA : A.card = 6) (hB : B.card = 6)
    (h : (A ∩ B).card = 6) : A = B := by
  have h1 : A ∩ B = A := Finset.eq_of_subset_of_card_le inter_subset_left (by omega)
  have h2 : A ∩ B = B := Finset.eq_of_subset_of_card_le inter_subset_right (by omega)
  rw [← h1, h2]

/-- The seam on a certified representative. -/
theorem seam_rep (hw : InCone6 w) (h₁ : 5 ≤ X₁.card) (h₂ : 5 ≤ X₂.card) (h₃ : 5 ≤ X₃.card)
    (h₄ : 5 ≤ X₄.card) (h₅ : 5 ≤ X₅.card) (h₆ : 5 ≤ X₆.card) (hB₁ : B₁.card = 6)
    (hB₂ : B₂.card = 6) (hB₃ : B₃.card = 6) (hB₄ : B₄.card = 6) (hB₅ : B₅.card = 6)
    (hB₆ : B₆.card = 6) {m1 m2 m3 m4 m5 : ℕ}
    (hm : MOK B₁ B₂ B₃ B₄ B₅ B₆ [m1, m2, m3, m4, m5]) (hr : [m1, m2, m3, m4, m5] ∈ allReps) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, GU 6 w s
      ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, GB w B₁ B₂ B₃ B₄ B₅ B₆ s := by
  simp only [allReps, List.mem_append] at hr
  rcases hr with ((hr | hr) | hr) | hr
  · -- the three exact shapes
    obtain ⟨c1, c2, c3, c4, c5⟩ := hm
    simp only [exL, List.mem_cons, List.not_mem_nil, or_false, List.cons.injEq, and_true] at hr
    simp only [List.getD_cons_zero, List.getD_cons_succ] at c1 c2 c3 c4 c5
    rcases hr with ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩
    · obtain rfl := eq_of_inter_card hB₁ hB₂ (by omega)
      obtain rfl := eq_of_inter_card hB₂ hB₃ (by omega)
      obtain rfl := eq_of_inter_card hB₄ hB₅ (by omega)
      obtain rfl := eq_of_inter_card hB₅ hB₆ (by omega)
      exact seam_shape3 hw h₁ h₂ h₃ h₄ h₅ h₆ hB₁ hB₄ (by omega)
    · obtain rfl := eq_of_inter_card hB₁ hB₂ (by omega)
      obtain rfl := eq_of_inter_card hB₂ hB₃ (by omega)
      obtain rfl := eq_of_inter_card hB₃ hB₄ (by omega)
      obtain rfl := eq_of_inter_card hB₅ hB₆ (by omega)
      exact seam_shape4 hw h₁ h₂ h₃ h₄ h₅ h₆ hB₁ hB₅ (by omega)
    · obtain rfl := eq_of_inter_card hB₁ hB₂ (by omega)
      obtain rfl := eq_of_inter_card hB₂ hB₃ (by omega)
      obtain rfl := eq_of_inter_card hB₃ hB₄ (by omega)
      obtain rfl := eq_of_inter_card hB₄ hB₅ (by omega)
      exact seam_shape5 hw h₁ h₂ h₃ h₄ h₅ h₆ hB₁ hB₆ (by omega)
  · obtain ⟨C, hC, he⟩ := List.mem_map.mp hr
    rw [← he] at hm
    exact seam_certc hw h₁ h₂ h₃ h₄ h₅ h₆ hB₁ hB₂ hB₃ hB₄ hB₅ hB₆ hm (lpAll_ok C hC)
  · obtain ⟨C, hC, he⟩ := List.mem_map.mp hr
    rw [← he] at hm
    obtain ⟨s1, s2, s3, s4, s5⟩ := ppAll_ok C hC
    exact seam_certp hw h₁ h₂ h₃ h₄ h₅ h₆ hB₁ hB₂ hB₃ hB₄ hB₅ hB₆ hm s1 s2 s3 s4 s5
  · have h := pwAll_ok [m1, m2, m3, m4, m5] hr
    simp only [List.getD_cons_zero, List.getD_cons_succ] at h
    exact seam_point hw hB₁ hB₂ hB₃ hB₄ hB₅ hB₆ hm h

end seams

/-! ### The seam inequality -/

/-- **The height-six seam inequality at `k = 6`.** -/
theorem seam66Holds : Seam66Holds := by
  intro w hw X₁ X₂ X₃ X₄ X₅ X₆ B₁ B₂ B₃ B₄ B₅ B₆ hX₁ hX₂ hX₃ hX₄ hX₅ hX₆ hB₁ hB₂ hB₃ hB₄ hB₅ hB₆
  have k2 : (B₁ ∩ B₂).card ≤ 6 := hB₁ ▸ card_le_card inter_subset_left
  have k3 : (B₂ ∩ B₃).card ≤ 6 := hB₂ ▸ card_le_card inter_subset_left
  have k4 : (B₃ ∩ B₄).card ≤ 6 := hB₃ ▸ card_le_card inter_subset_left
  have k5 : (B₄ ∩ B₅).card ≤ 6 := hB₄ ▸ card_le_card inter_subset_left
  have k6 : (B₅ ∩ B₆).card ≤ 6 := hB₅ ▸ card_le_card inter_subset_left
  set m1 := 6 - (B₁ ∩ B₂).card
  set m2 := 6 - (B₂ ∩ B₃).card
  set m3 := 6 - (B₃ ∩ B₄).card
  set m4 := 6 - (B₄ ∩ B₅).card
  set m5 := 6 - (B₅ ∩ B₆).card
  have hm : MOK B₁ B₂ B₃ B₄ B₅ B₆ [m1, m2, m3, m4, m5] := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [List.getD_cons_zero, List.getD_cons_succ] <;> omega
  have hmr : MOK B₆ B₅ B₄ B₃ B₂ B₁ [m5, m4, m3, m2, m1] := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [List.getD_cons_zero, List.getD_cons_succ] <;>
      rw [Finset.inter_comm] <;> omega
  have hc := coverA_ok (a := m1) (by omega)
  simp only [coverA, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq] at hc
  rcases hc m2 (by omega) m3 (by omega) m4 (by omega) m5 (by omega) with
    (⟨⟨⟨⟨z1, z2⟩, z3⟩, z4⟩, z5⟩ | h) | h
  · -- `0`: all lists are equal
    obtain rfl := eq_of_inter_card hB₁ hB₂ (by omega)
    obtain rfl := eq_of_inter_card hB₁ hB₃ (by omega)
    obtain rfl := eq_of_inter_card hB₁ hB₄ (by omega)
    obtain rfl := eq_of_inter_card hB₁ hB₅ (by omega)
    obtain rfl := eq_of_inter_card hB₁ hB₆ (by omega)
    exact seam_zero66 hw hB₁
  · exact seam_rep hw hX₁.1 hX₂.1 hX₃.1 hX₄.1 hX₅.1 hX₆.1 hB₁ hB₂ hB₃ hB₄ hB₅ hB₆ hm
      (mem_allReps_of (by omega) (by omega) (by omega) (by omega) (by omega) h)
  · exact seam_of_rev (seam_rep hw hX₆.1 hX₅.1 hX₄.1 hX₃.1 hX₂.1 hX₁.1 hB₆ hB₅ hB₄ hB₃ hB₂ hB₁ hmr
      (mem_allReps_of (by omega) (by omega) (by omega) (by omega) (by omega) h))

end GridGen.Six
