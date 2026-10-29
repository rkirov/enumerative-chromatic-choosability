/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.K5.Block

/-!
# Height five at `k = 5`: pins

A pin is a block event (`Blk5`: none, or one to three consecutive rows each in a colour set) and
a peeling chain of factors (`Fac5`). Under the uniform weights `GU 5 w` on the proper columns of
lists of at least four colours (`w` in the cone), its event carries at most the product of the
factor bounds and the block bound of the total weight (`pin_sum5`). The fibre shares are
`q = 1000/2822` on an end row (three free colours) and `1000/1911` on a middle row (two), from
the uniform ratio `911/1000` (`fibOK_GU`); the block bounds are those of
`GridGen/Five/K5/Block.lean`, the blocks ending at row five by row reflection.
-/

namespace GridGen.Five.K5

open Finset GridGen.Five GridGen.Five.Ex5

/-- The fibre share of a row under the uniform weights. -/
def qX (r : ℕ) : ℚ := if r = 0 ∨ 4 ≤ r then 1000 / 2822 else 1000 / 1911

theorem qX_nonneg (r : ℕ) : 0 ≤ qX r := by unfold qX; split_ifs <;> norm_num

/-- **The fibre property of the uniform weights.** -/
theorem fibOK_GU {w : Wt5} (hw : InCone5 w) {X₁ X₂ X₃ X₄ X₅ : Finset ℕ} (h₁ : 4 ≤ X₁.card)
    (h₂ : 4 ≤ X₂.card) (h₃ : 4 ≤ X₃.card) (h₄ : 4 ≤ X₄.card) (h₅ : 4 ≤ X₅.card) :
    FibOK (sts X₁ X₂ X₃ X₄ X₅) (GU 5 w) qX := by
  refine fibOK_sts (fun _ => 4) (fun i hi => ?_) (fun i hi => ?_) (GU 5 w) (GU_nonneg55 hw)
    (R := 1000 / 911) (by norm_num) (fun t ht t' ht' => ?_) qX (fun i hi => ?_)
  · interval_cases i <;> simpa [bl]
  · interval_cases i <;> simp [frc]
  · rw [GU_five w (proper_of_mem_sts ht), GU_five w (proper_of_mem_sts ht')]
    have := rowV5_ratio hw (orb t') (orb t)
    push_cast
    linarith
  · interval_cases i <;> norm_num [qX, frc]

/-! ### Blocks -/

/-- A block event: none, or one to three consecutive rows from row `r`, each in a colour set
with a declared size. -/
inductive Blk5
  | none
  | one (r : ℕ) (D : Finset ℕ) (d : ℕ)
  | two (r : ℕ) (D D' : Finset ℕ) (d d' : ℕ)
  | three (r : ℕ) (D D' D'' : Finset ℕ) (d d' d'' : ℕ)

namespace Blk5

def ev : Blk5 → T5 → Bool
  | none, _ => true
  | one r D _, t => decide (rowAt r t ∈ D)
  | two r D D' _ _, t => decide (rowAt r t ∈ D) && decide (rowAt (r + 1) t ∈ D')
  | three r D D' D'' _ _ _, t =>
      decide (rowAt r t ∈ D) && decide (rowAt (r + 1) t ∈ D') && decide (rowAt (r + 2) t ∈ D'')

def reads : Blk5 → ℕ → Bool
  | none, _ => false
  | one r _ _, i => decide (r = i)
  | two r _ _ _ _, i => decide (r = i) || decide (r + 1 = i)
  | three r _ _ _ _ _ _, i => decide (r = i) || decide (r + 1 = i) || decide (r + 2 = i)

def ok : Blk5 → Prop
  | none => True
  | one r D d => r < 5 ∧ D.card ≤ d
  | two r D D' d d' => r < 4 ∧ D.card ≤ d ∧ D'.card ≤ d'
  | three r D D' D'' d d' d'' => r < 3 ∧ D.card ≤ d ∧ D'.card ≤ d' ∧ D''.card ≤ d''

def bnd : Blk5 → ℚ
  | none => 1
  | one r _ d => βQ5 d 4 (fsd r * fsd (4 - r))
  | two r _ _ d d' => βQ5 (d * d') 12 (fsd r * fsd (3 - r))
  | three r _ _ _ d d' d'' => βQ5 (d * d' * d'') 36 (fsd r * fsd (2 - r))

theorem ev_setAt {b : Blk5} (hb : b.ok) {i : ℕ} (hi : i < 5) (h : b.reads i = false) (t : T5)
    (x : ℕ) : b.ev (setAt i t x) = b.ev t := by
  cases b with
  | none => rfl
  | one r D d =>
    simp only [reads, decide_eq_false_iff_not] at h
    simp only [ev, rowAt_setAt_ne (Ne.symm h) hi hb.1]
  | two r D D' d d' =>
    simp only [reads, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
    simp only [ev, rowAt_setAt_ne (Ne.symm h.1) hi (by have := hb.1; omega),
      rowAt_setAt_ne (Ne.symm h.2) hi (by have := hb.1; omega)]
  | three r D D' D'' d d' d'' =>
    simp only [reads, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
    simp only [ev, rowAt_setAt_ne (Ne.symm h.1.1) hi (by have := hb.1; omega),
      rowAt_setAt_ne (Ne.symm h.1.2) hi (by have := hb.1; omega),
      rowAt_setAt_ne (Ne.symm h.2) hi (by have := hb.1; omega)]

end Blk5

section bound

variable {w : Wt5} {X₁ X₂ X₃ X₄ X₅ : Finset ℕ}

theorem sum_all_rev55 (w : Wt5) (X₁ X₂ X₃ X₄ X₅ : Finset ℕ) :
    ∑ t ∈ sts X₁ X₂ X₃ X₄ X₅, GU 5 w t = ∑ t ∈ sts X₅ X₄ X₃ X₂ X₁, GU 5 w t := by
  have h := sum_filter_rev55 w X₁ X₂ X₃ X₄ X₅ (fun _ => True)
  simp only [Finset.filter_true] at h
  exact h

theorem βQ5_comm (m M : ℕ) (a b : ℚ) : βQ5 m M (a * b) = βQ5 m M (b * a) := by rw [mul_comm]

/-- **The block bound.** -/
theorem blk_bound5 (hw : InCone5 w) (h₁ : 4 ≤ X₁.card) (h₂ : 4 ≤ X₂.card) (h₃ : 4 ≤ X₃.card)
    (h₄ : 4 ≤ X₄.card) (h₅ : 4 ≤ X₅.card) (b : Blk5) (hb : b.ok) :
    ∑ t ∈ (sts X₁ X₂ X₃ X₄ X₅).filter (fun t => b.ev t = true), GU 5 w t
      ≤ ((b.bnd : ℚ) : ℝ) * ∑ t ∈ sts X₁ X₂ X₃ X₄ X₅, GU 5 w t := by
  cases b with
  | none =>
    simp only [Blk5.ev, Blk5.bnd, Finset.filter_true_of_mem (fun _ _ => rfl)]; push_cast; simp
  | one r D d =>
    obtain ⟨hr, hd⟩ := hb
    simp only [Blk5.ev, decide_eq_true_eq, Blk5.bnd]
    interval_cases r
    · exact blk_one0 hw h₁ h₂ h₃ h₄ h₅ D hd
    · exact blk_one1 hw h₁ h₂ h₃ h₄ h₅ D hd
    · exact blk_one2 hw h₁ h₂ h₃ h₄ h₅ D hd
    · rw [sum_filter_rev55, sum_all_rev55]
      have := blk_one1 hw h₅ h₄ h₃ h₂ h₁ D hd
      rw [βQ5_comm] at this
      exact this
    · rw [sum_filter_rev55, sum_all_rev55]
      have := blk_one0 hw h₅ h₄ h₃ h₂ h₁ D hd
      rw [βQ5_comm] at this
      exact this
  | two r D D' d d' =>
    obtain ⟨hr, hd, hd'⟩ := hb
    simp only [Blk5.ev, Bool.and_eq_true, decide_eq_true_eq, Blk5.bnd]
    interval_cases r
    · have := blk_two0 hw h₁ h₂ h₃ h₄ h₅ D D' hd hd'
      simp only [Finset.mem_product] at this
      refine le_of_eq_of_le ?_ this
      refine Finset.sum_congr (Finset.filter_congr fun t _ => ?_) fun _ _ => rfl
      simp only [rowAt]; try tauto
    · have := blk_two1 hw h₁ h₂ h₃ h₄ h₅ D D' hd hd'
      simp only [Finset.mem_product] at this
      refine le_of_eq_of_le ?_ this
      refine Finset.sum_congr (Finset.filter_congr fun t _ => ?_) fun _ _ => rfl
      simp only [rowAt]; try tauto
    · rw [sum_filter_rev55, sum_all_rev55]
      have := blk_two1 hw h₅ h₄ h₃ h₂ h₁ D' D hd' hd
      rw [βQ5_comm, Nat.mul_comm] at this
      simp only [Finset.mem_product] at this
      refine le_of_eq_of_le ?_ this
      refine Finset.sum_congr (Finset.filter_congr fun t _ => ?_) fun _ _ => rfl
      simp only [rev5, rowAt, r1, r2, r3, r4, r5]; tauto
    · rw [sum_filter_rev55, sum_all_rev55]
      have := blk_two0 hw h₅ h₄ h₃ h₂ h₁ D' D hd' hd
      rw [βQ5_comm, Nat.mul_comm] at this
      simp only [Finset.mem_product] at this
      refine le_of_eq_of_le ?_ this
      refine Finset.sum_congr (Finset.filter_congr fun t _ => ?_) fun _ _ => rfl
      simp only [rev5, rowAt, r1, r2, r3, r4, r5]; tauto
  | three r D D' D'' d d' d'' =>
    obtain ⟨hr, hd, hd', hd''⟩ := hb
    simp only [Blk5.ev, Bool.and_eq_true, decide_eq_true_eq, Blk5.bnd]
    interval_cases r
    · have := blk_three0 hw h₁ h₂ h₃ h₄ h₅ D D' D'' hd hd' hd''
      simp only [Finset.mem_product] at this
      refine le_of_eq_of_le ?_ this
      refine Finset.sum_congr (Finset.filter_congr fun t _ => ?_) fun _ _ => rfl
      simp only [rowAt]; try tauto
    · have := blk_three1 hw h₁ h₂ h₃ h₄ h₅ D D' D'' hd hd' hd''
      simp only [Finset.mem_product] at this
      refine le_of_eq_of_le ?_ this
      refine Finset.sum_congr (Finset.filter_congr fun t _ => ?_) fun _ _ => rfl
      simp only [rowAt]; try tauto
    · rw [sum_filter_rev55, sum_all_rev55]
      have := blk_three0 hw h₅ h₄ h₃ h₂ h₁ D'' D' D hd'' hd' hd
      rw [βQ5_comm, show d'' * d' * d = d * d' * d'' by ring] at this
      simp only [Finset.mem_product] at this
      refine le_of_eq_of_le ?_ this
      refine Finset.sum_congr (Finset.filter_congr fun t _ => ?_) fun _ _ => rfl
      simp only [rev5, rowAt, r1, r2, r3, r4, r5]; tauto

/-! ### Pins -/

/-- A pin: a block and a peeling chain. -/
structure Pin5 where
  blk : Blk5
  peels : List Fac5

namespace Pin5

def ev (q : Pin5) (t : T5) : Bool := allEv5 q.peels t && q.blk.ev t

def bnd (q : Pin5) : ℚ := (q.peels.map (Fac5.bnd qX)).prod * q.blk.bnd

def OK (q : Pin5) : Prop := q.blk.ok ∧ PeelOK5 q.blk.reads q.peels

end Pin5

/-- **A pin carries at most its bound.** -/
theorem pin_sum5 (hw : InCone5 w) (h₁ : 4 ≤ X₁.card) (h₂ : 4 ≤ X₂.card) (h₃ : 4 ≤ X₃.card)
    (h₄ : 4 ≤ X₄.card) (h₅ : 4 ≤ X₅.card) (q : Pin5) (hq : q.OK) :
    ∑ t ∈ (sts X₁ X₂ X₃ X₄ X₅).filter (fun t => q.ev t = true), GU 5 w t
      ≤ ((q.bnd : ℚ) : ℝ) * ∑ t ∈ sts X₁ X₂ X₃ X₄ X₅, GU 5 w t := by
  have h1 := peel_chain5 (fibOK_GU hw h₁ h₂ h₃ h₄ h₅) (GU_nonneg55 hw) qX_nonneg q.blk.reads
    q.blk.ev (fun i hi hr t x => Blk5.ev_setAt hq.1 hi hr t x) q.peels hq.2
  have h2 := blk_bound5 hw h₁ h₂ h₃ h₄ h₅ q.blk hq.1
  have hp : (0 : ℝ) ≤ (((q.peels.map (Fac5.bnd qX)).prod : ℚ) : ℝ) := by
    have : (0 : ℚ) ≤ (q.peels.map (Fac5.bnd qX)).prod :=
      List.prod_nonneg (fun x hx => by
        obtain ⟨f, -, rfl⟩ := List.mem_map.mp hx; exact f.bnd_nonneg qX_nonneg)
    exact_mod_cast this
  calc _ ≤ (((q.peels.map (Fac5.bnd qX)).prod : ℚ) : ℝ)
        * ∑ t ∈ (sts X₁ X₂ X₃ X₄ X₅).filter (fun t => q.blk.ev t = true), GU 5 w t := h1
    _ ≤ (((q.peels.map (Fac5.bnd qX)).prod : ℚ) : ℝ)
        * (((q.blk.bnd : ℚ) : ℝ) * ∑ t ∈ sts X₁ X₂ X₃ X₄ X₅, GU 5 w t) :=
        mul_le_mul_of_nonneg_left h2 hp
    _ = _ := by unfold Pin5.bnd; push_cast; ring

end bound

end GridGen.Five.K5
