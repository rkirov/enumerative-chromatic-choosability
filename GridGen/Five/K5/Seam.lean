/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.K5.BitAll
import GridGen.Five.K5.Zero
import GridGen.Five.K5.ExClass.All

/-!
# Height five at `k = 5`: the seam inequality

The mismatches `μⱼ = 5 - |Bⱼ₋₁ ∩ Bⱼ|` form a quad of integers in `[0, 5]`. Up to row reflection
(`seam_of_rev55`) every quad is `(0,0,0,0)` (relabelling, `seam_zero55`), one of the sixteen
residual classes (exact certificates, `seam_exactQ`), a class closed by a dual certificate over
the state bits (`seam_lpQ`) or a pointwise class (`seam_ptQ`): the review's split
493 + 156 + 16 (`H5_K5_REVIEW_2026-10-28.md` (c)). The covering is a kernel check over the 1296
quads with a bit mask of the representatives (`cover55`).
-/

namespace GridGen.Five.K5

open Finset GridGen.Five GridGen.Five.Ex5

/-- The residual classes, certified exactly. -/
def exQ : List (ℕ × ℕ × ℕ × ℕ) :=
  [(0, 0, 0, 1), (0, 0, 1, 0), (0, 0, 0, 2), (0, 0, 1, 1), (0, 0, 2, 0), (0, 1, 0, 1), (0, 1, 1, 0),
   (1, 0, 0, 1), (0, 0, 1, 2), (0, 0, 2, 1), (0, 1, 0, 2), (0, 1, 1, 1), (0, 1, 2, 0), (0, 2, 0, 1),
   (1, 0, 1, 1), (1, 1, 1, 1)]

section seams

variable {w : Wt5} {X₁ X₂ X₃ X₄ X₅ B₁ B₂ B₃ B₄ B₅ : Finset ℕ} {m2 m3 m4 m5 : ℕ}

/-- The seam on a residual class. -/
theorem seam_exactQ (hw : InCone5 w) (h₁ : 4 ≤ X₁.card) (h₂ : 4 ≤ X₂.card) (h₃ : 4 ≤ X₃.card)
    (h₄ : 4 ≤ X₄.card) (h₅ : 4 ≤ X₅.card) (hB₁ : B₁.card = 5) (hB₂ : B₂.card = 5)
    (hB₃ : B₃.card = 5) (hB₄ : B₄.card = 5) (hB₅ : B₅.card = 5)
    (c2 : (B₁ ∩ B₂).card + m2 = 5) (c3 : (B₂ ∩ B₃).card + m3 = 5)
    (c4 : (B₃ ∩ B₄).card + m4 = 5) (c5 : (B₄ ∩ B₅).card + m5 = 5)
    (hq : (m2, m3, m4, m5) ∈ exQ) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 5 w s ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GB w B₁ B₂ B₃ B₄ B₅ s := by
  simp only [exQ, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hq
  rcases hq with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩
  · exact seam_cls_0001 hw h₁ h₂ h₃ h₄ h₅ hB₁ hB₂ hB₃ hB₄ hB₅ c2 c3 c4 c5
  · exact seam_cls_0010 hw h₁ h₂ h₃ h₄ h₅ hB₁ hB₂ hB₃ hB₄ hB₅ c2 c3 c4 c5
  · exact seam_cls_0002 hw h₁ h₂ h₃ h₄ h₅ hB₁ hB₂ hB₃ hB₄ hB₅ c2 c3 c4 c5
  · exact seam_cls_0011 hw h₁ h₂ h₃ h₄ h₅ hB₁ hB₂ hB₃ hB₄ hB₅ c2 c3 c4 c5
  · exact seam_cls_0020 hw h₁ h₂ h₃ h₄ h₅ hB₁ hB₂ hB₃ hB₄ hB₅ c2 c3 c4 c5
  · exact seam_cls_0101 hw h₁ h₂ h₃ h₄ h₅ hB₁ hB₂ hB₃ hB₄ hB₅ c2 c3 c4 c5
  · exact seam_cls_0110 hw h₁ h₂ h₃ h₄ h₅ hB₁ hB₂ hB₃ hB₄ hB₅ c2 c3 c4 c5
  · exact seam_cls_1001 hw h₁ h₂ h₃ h₄ h₅ hB₁ hB₂ hB₃ hB₄ hB₅ c2 c3 c4 c5
  · exact seam_cls_0012 hw h₁ h₂ h₃ h₄ h₅ hB₁ hB₂ hB₃ hB₄ hB₅ c2 c3 c4 c5
  · exact seam_cls_0021 hw h₁ h₂ h₃ h₄ h₅ hB₁ hB₂ hB₃ hB₄ hB₅ c2 c3 c4 c5
  · exact seam_cls_0102 hw h₁ h₂ h₃ h₄ h₅ hB₁ hB₂ hB₃ hB₄ hB₅ c2 c3 c4 c5
  · exact seam_cls_0111 hw h₁ h₂ h₃ h₄ h₅ hB₁ hB₂ hB₃ hB₄ hB₅ c2 c3 c4 c5
  · exact seam_cls_0120 hw h₁ h₂ h₃ h₄ h₅ hB₁ hB₂ hB₃ hB₄ hB₅ c2 c3 c4 c5
  · exact seam_cls_0201 hw h₁ h₂ h₃ h₄ h₅ hB₁ hB₂ hB₃ hB₄ hB₅ c2 c3 c4 c5
  · exact seam_cls_1011 hw h₁ h₂ h₃ h₄ h₅ hB₁ hB₂ hB₃ hB₄ hB₅ c2 c3 c4 c5
  · exact seam_cls_1111 hw h₁ h₂ h₃ h₄ h₅ hB₁ hB₂ hB₃ hB₄ hB₅ c2 c3 c4 c5

/-- The seam on a class with a dual certificate. -/
theorem seam_lpQ (hw : InCone5 w) (h₁ : 4 ≤ X₁.card) (h₂ : 4 ≤ X₂.card) (h₃ : 4 ≤ X₃.card)
    (h₄ : 4 ≤ X₄.card) (h₅ : 4 ≤ X₅.card) (hB₁ : B₁.card = 5) (hB₂ : B₂.card = 5)
    (hB₃ : B₃.card = 5) (hB₄ : B₄.card = 5) (hB₅ : B₅.card = 5)
    (c2 : (B₁ ∩ B₂).card + m2 = 5) (c3 : (B₂ ∩ B₃).card + m3 = 5)
    (c4 : (B₃ ∩ B₄).card + m4 = 5) (c5 : (B₄ ∩ B₅).card + m5 = 5)
    (hq : (m2, m3, m4, m5) ∈ lpAll.map Prod.fst) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 5 w s ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GB w B₁ B₂ B₃ B₄ B₅ s := by
  obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hq
  have hok := lpAll_ok x hx
  rw [hxe] at hok
  exact seam_of_bit55 hw h₁ h₂ h₃ h₄ h₅ hB₁ hB₂ hB₃ hB₄ hB₅ c2 c3 c4 c5 x.2 hok

/-- The seam on a pointwise class. -/
theorem seam_ptQ (hw : InCone5 w) (hB₁ : B₁.card = 5) (hB₂ : B₂.card = 5)
    (hB₃ : B₃.card = 5) (hB₄ : B₄.card = 5) (hB₅ : B₅.card = 5)
    (c2 : (B₁ ∩ B₂).card + m2 = 5) (c3 : (B₂ ∩ B₃).card + m3 = 5)
    (c4 : (B₃ ∩ B₄).card + m4 = 5) (c5 : (B₄ ∩ B₅).card + m5 = 5)
    (hq : (m2, m3, m4, m5) ∈ ptAll) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 5 w s ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GB w B₁ B₂ B₃ B₄ B₅ s :=
  seam_of_pt55 hw hB₁ hB₂ hB₃ hB₄ hB₅ c2 c3 c4 c5 (ptAll_ok (m2, m3, m4, m5) hq)

end seams

/-! ### The covering -/

/-- All certified class representatives. -/
def allReps : List (ℕ × ℕ × ℕ × ℕ) := exQ ++ lpAll.map Prod.fst ++ ptAll

/-- The key of a quad. -/
def qkey (q : ℕ × ℕ × ℕ × ℕ) : ℕ := q.1 * 216 + q.2.1 * 36 + q.2.2.1 * 6 + q.2.2.2

/-- The mask of a list of quads. -/
def qmask (L : List (ℕ × ℕ × ℕ × ℕ)) : ℕ := L.foldr (fun q acc => 2 ^ qkey q ||| acc) 0

theorem qmask_testBit : ∀ (L : List (ℕ × ℕ × ℕ × ℕ)) (k : ℕ), (qmask L).testBit k = true →
    ∃ q ∈ L, qkey q = k
  | [], k, h => by simp [qmask] at h
  | q :: L, k, h => by
    simp only [qmask, List.foldr_cons, Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow,
      decide_eq_true_eq] at h
    rcases h with h | h
    · exact ⟨q, List.mem_cons_self, h⟩
    · obtain ⟨q', hq', e⟩ := qmask_testBit L k h
      exact ⟨q', List.mem_cons_of_mem _ hq', e⟩

/-- **The covering**: every quad is zero or has a certified representative up to reflection. -/
def cover55 : Bool :=
  allReps.all (fun q => decide (q.1 < 6 ∧ q.2.1 < 6 ∧ q.2.2.1 < 6 ∧ q.2.2.2 < 6)) &&
  (List.range 6).all fun a => (List.range 6).all fun b => (List.range 6).all fun c =>
    (List.range 6).all fun d => (a == 0 && b == 0 && c == 0 && d == 0) ||
      (qmask allReps).testBit (qkey (a, b, c, d)) || (qmask allReps).testBit (qkey (d, c, b, a))

theorem cover55_ok : cover55 = true := by decide +kernel

theorem mem_allReps_of {a b c d : ℕ} (ha : a < 6) (hb : b < 6) (hc : c < 6) (hd : d < 6)
    (h : (qmask allReps).testBit (qkey (a, b, c, d)) = true) : (a, b, c, d) ∈ allReps := by
  obtain ⟨q, hq, e⟩ := qmask_testBit allReps _ h
  have hc6 := cover55_ok
  simp only [cover55, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc6
  obtain ⟨q1, q2, q3, q4⟩ := hc6.1 q hq
  obtain ⟨x1, x2, x3, x4⟩ := q
  simp only [qkey] at e q1 q2 q3 q4
  have : x1 = a ∧ x2 = b ∧ x3 = c ∧ x4 = d := by omega
  obtain ⟨rfl, rfl, rfl, rfl⟩ := this
  exact hq

/-- **The height-five seam inequality at `k = 5`.** -/
theorem seam55Holds : Seam55Holds := by
  intro w hw X₁ X₂ X₃ X₄ X₅ B₁ B₂ B₃ B₄ B₅ hX₁ hX₂ hX₃ hX₄ hX₅ hB₁ hB₂ hB₃ hB₄ hB₅
  have k2 : (B₁ ∩ B₂).card ≤ 5 := hB₁ ▸ card_le_card inter_subset_left
  have k3 : (B₂ ∩ B₃).card ≤ 5 := hB₂ ▸ card_le_card inter_subset_left
  have k4 : (B₃ ∩ B₄).card ≤ 5 := hB₃ ▸ card_le_card inter_subset_left
  have k5 : (B₄ ∩ B₅).card ≤ 5 := hB₄ ▸ card_le_card inter_subset_left
  set m2 := 5 - (B₁ ∩ B₂).card
  set m3 := 5 - (B₂ ∩ B₃).card
  set m4 := 5 - (B₃ ∩ B₄).card
  set m5 := 5 - (B₄ ∩ B₅).card
  have c2 : (B₁ ∩ B₂).card + m2 = 5 := by omega
  have c3 : (B₂ ∩ B₃).card + m3 = 5 := by omega
  have c4 : (B₃ ∩ B₄).card + m4 = 5 := by omega
  have c5 : (B₄ ∩ B₅).card + m5 = 5 := by omega
  have r2 : (B₂ ∩ B₁).card + m2 = 5 := by rw [Finset.inter_comm]; exact c2
  have r3 : (B₃ ∩ B₂).card + m3 = 5 := by rw [Finset.inter_comm]; exact c3
  have r4 : (B₄ ∩ B₃).card + m4 = 5 := by rw [Finset.inter_comm]; exact c4
  have r5 : (B₅ ∩ B₄).card + m5 = 5 := by rw [Finset.inter_comm]; exact c5
  have h₁ : 4 ≤ X₁.card := hX₁.1
  have h₂ : 4 ≤ X₂.card := hX₂.1
  have h₃ : 4 ≤ X₃.card := hX₃.1
  have h₄ : 4 ≤ X₄.card := hX₄.1
  have h₅ : 4 ≤ X₅.card := hX₅.1
  have hc := cover55_ok
  simp only [cover55, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    beq_iff_eq] at hc
  have hm2 : m2 < 6 := by omega
  have hm3 : m3 < 6 := by omega
  have hm4 : m4 < 6 := by omega
  have hm5 : m5 < 6 := by omega
  -- a representative gives the seam
  have rep : ∀ {Y₁ Y₂ Y₃ Y₄ Y₅ C₁ C₂ C₃ C₄ C₅ : Finset ℕ} {a b c d : ℕ},
      4 ≤ Y₁.card → 4 ≤ Y₂.card → 4 ≤ Y₃.card → 4 ≤ Y₄.card → 4 ≤ Y₅.card →
      C₁.card = 5 → C₂.card = 5 → C₃.card = 5 → C₄.card = 5 → C₅.card = 5 →
      (C₁ ∩ C₂).card + a = 5 → (C₂ ∩ C₃).card + b = 5 → (C₃ ∩ C₄).card + c = 5 →
      (C₄ ∩ C₅).card + d = 5 → (a, b, c, d) ∈ allReps →
      ∑ s ∈ sts Y₁ Y₂ Y₃ Y₄ Y₅, GU 5 w s ≤ ∑ s ∈ sts Y₁ Y₂ Y₃ Y₄ Y₅, GB w C₁ C₂ C₃ C₄ C₅ s := by
    intro Y₁ Y₂ Y₃ Y₄ Y₅ C₁ C₂ C₃ C₄ C₅ a b c d g₁ g₂ g₃ g₄ g₅ e₁ e₂ e₃ e₄ e₅ d2 d3 d4 d5 hm
    simp only [allReps, List.mem_append] at hm
    rcases hm with (hm | hm) | hm
    · exact seam_exactQ hw g₁ g₂ g₃ g₄ g₅ e₁ e₂ e₃ e₄ e₅ d2 d3 d4 d5 hm
    · exact seam_lpQ hw g₁ g₂ g₃ g₄ g₅ e₁ e₂ e₃ e₄ e₅ d2 d3 d4 d5 hm
    · exact seam_ptQ hw e₁ e₂ e₃ e₄ e₅ d2 d3 d4 d5 hm
  rcases hc.2 m2 hm2 m3 hm3 m4 hm4 m5 hm5 with (⟨⟨⟨z2, z3⟩, z4⟩, z5⟩ | h) | h
  · -- `(0,0,0,0)`: all lists are equal
    have eq : ∀ {U V : Finset ℕ}, U.card = 5 → V.card = 5 → (U ∩ V).card = 5 → U = V := by
      intro U V hU hV h
      have h1 : U ∩ V = U := Finset.eq_of_subset_of_card_le inter_subset_left (by omega)
      have h2 : U ∩ V = V := Finset.eq_of_subset_of_card_le inter_subset_right (by omega)
      rw [← h1, h2]
    have e12 := eq hB₁ hB₂ (by omega)
    have e23 := eq hB₂ hB₃ (by omega)
    have e34 := eq hB₃ hB₄ (by omega)
    have e45 := eq hB₄ hB₅ (by omega)
    subst e12 e23 e34 e45
    exact seam_zero55 hw hB₁
  · exact rep h₁ h₂ h₃ h₄ h₅ hB₁ hB₂ hB₃ hB₄ hB₅ c2 c3 c4 c5
      (mem_allReps_of hm2 hm3 hm4 hm5 h)
  · exact seam_of_rev55 (rep h₅ h₄ h₃ h₂ h₁ hB₅ hB₄ hB₃ hB₂ hB₁ r5 r4 r3 r2
      (mem_allReps_of hm5 hm4 hm3 hm2 h))

end GridGen.Five.K5
