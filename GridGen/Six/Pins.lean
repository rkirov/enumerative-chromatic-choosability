/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Six.Block

/-!
# Height six at `k = 6`: pins

`GridGen/Five/K5/Pins.lean` with six rows. A pin is a block event (`Blk6`: none, or one to three
consecutive rows each in a colour set) and a peeling chain of factors (`Fac6`). Under the uniform
weights `GU 6 w` on the proper columns of lists of at least five colours (`w` in the cone), its
event carries at most the product of the factor bounds and the block bound of the total weight
(`pin_sum6`). The fibre shares are `q = 1/(1 + 3ρ) = 10000/38449` on an end row (four free
colours) and `1/(1 + 2ρ) = 10000/28966` on a middle row (three), `ρ = 9483/10000`
(`fibOK_GU`); the block bounds are those of `GridGen/Six/Block.lean`, the blocks ending in the
lower half by row reflection.
-/

namespace GridGen.Six

open Finset

/-- The fibre share of a row under the uniform weights. -/
def qX (r : ℕ) : ℚ := if r = 0 ∨ 5 ≤ r then 10000 / 38449 else 10000 / 28966

theorem qX_nonneg (r : ℕ) : 0 ≤ qX r := by unfold qX; split_ifs <;> norm_num

/-- **The fibre property of the uniform weights.** -/
theorem fibOK_GU {w : Wt6} (hw : InCone6 w) {X₁ X₂ X₃ X₄ X₅ X₆ : Finset ℕ} (h₁ : 5 ≤ X₁.card)
    (h₂ : 5 ≤ X₂.card) (h₃ : 5 ≤ X₃.card) (h₄ : 5 ≤ X₄.card) (h₅ : 5 ≤ X₅.card)
    (h₆ : 5 ≤ X₆.card) :
    FibOK (sts X₁ X₂ X₃ X₄ X₅ X₆) (GU 6 w) qX := by
  refine fibOK_sts (fun _ => 5) (fun i hi => ?_) (fun i hi => ?_) (GU 6 w) (GU_nonneg hw)
    (R := 10000 / 9483) (by norm_num) (fun t ht t' ht' => ?_) qX (fun i hi => ?_)
  · interval_cases i <;> simpa [bl]
  · interval_cases i <;> simp [frc]
  · rw [GU_six w (proper_of_mem_sts ht), GU_six w (proper_of_mem_sts ht')]
    have := rowV6_ratio hw (orb t') (orb t)
    push_cast
    linarith
  · interval_cases i <;> norm_num [qX, frc]

/-! ### Blocks -/

/-- A block event: none, or one to three consecutive rows from row `r`, each in a colour set
with a declared size. -/
inductive Blk6
  | none
  | one (r : ℕ) (D : Finset ℕ) (d : ℕ)
  | two (r : ℕ) (D D' : Finset ℕ) (d d' : ℕ)
  | three (r : ℕ) (D D' D'' : Finset ℕ) (d d' d'' : ℕ)

namespace Blk6

def ev : Blk6 → T6 → Bool
  | none, _ => true
  | one r D _, t => decide (rowAt r t ∈ D)
  | two r D D' _ _, t => decide (rowAt r t ∈ D) && decide (rowAt (r + 1) t ∈ D')
  | three r D D' D'' _ _ _, t =>
      decide (rowAt r t ∈ D) && decide (rowAt (r + 1) t ∈ D') && decide (rowAt (r + 2) t ∈ D'')

def reads : Blk6 → ℕ → Bool
  | none, _ => false
  | one r _ _, i => decide (r = i)
  | two r _ _ _ _, i => decide (r = i) || decide (r + 1 = i)
  | three r _ _ _ _ _ _, i => decide (r = i) || decide (r + 1 = i) || decide (r + 2 = i)

def ok : Blk6 → Prop
  | none => True
  | one r D d => r < 6 ∧ D.card ≤ d
  | two r D D' d d' => r < 5 ∧ D.card ≤ d ∧ D'.card ≤ d'
  | three r D D' D'' d d' d'' => r < 4 ∧ D.card ≤ d ∧ D'.card ≤ d' ∧ D''.card ≤ d''

def bnd : Blk6 → ℚ
  | none => 1
  | one r _ d => βQ6 d 5 (fsd r * fsd (5 - r))
  | two r _ _ d d' => βQ6 (d * d') 20 (fsd r * fsd (4 - r))
  | three r _ _ _ d d' d'' => βQ6 (d * d' * d'') 80 (fsd r * fsd (3 - r))

theorem ev_setAt {b : Blk6} (hb : b.ok) {i : ℕ} (hi : i < 6) (h : b.reads i = false) (t : T6)
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

end Blk6

section bound

variable {w : Wt6} {X₁ X₂ X₃ X₄ X₅ X₆ : Finset ℕ}

theorem sum_all_rev66 (w : Wt6) (X₁ X₂ X₃ X₄ X₅ X₆ : Finset ℕ) :
    ∑ t ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, GU 6 w t = ∑ t ∈ sts X₆ X₅ X₄ X₃ X₂ X₁, GU 6 w t := by
  have h := sum_filter_rev66 w X₁ X₂ X₃ X₄ X₅ X₆ (fun _ => True)
  simp only [Finset.filter_true] at h
  exact h

theorem βQ6_comm (m M : ℕ) (a b : ℚ) : βQ6 m M (a * b) = βQ6 m M (b * a) := by rw [mul_comm]

/-- **The block bound.** -/
theorem blk_bound6 (hw : InCone6 w) (h₁ : 5 ≤ X₁.card) (h₂ : 5 ≤ X₂.card) (h₃ : 5 ≤ X₃.card)
    (h₄ : 5 ≤ X₄.card) (h₅ : 5 ≤ X₅.card) (h₆ : 5 ≤ X₆.card) (b : Blk6) (hb : b.ok) :
    ∑ t ∈ (sts X₁ X₂ X₃ X₄ X₅ X₆).filter (fun t => b.ev t = true), GU 6 w t
      ≤ ((b.bnd : ℚ) : ℝ) * ∑ t ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, GU 6 w t := by
  cases b with
  | none =>
    simp only [Blk6.ev, Blk6.bnd, Finset.filter_true_of_mem (fun _ _ => rfl)]; push_cast; simp
  | one r D d =>
    obtain ⟨hr, hd⟩ := hb
    simp only [Blk6.ev, decide_eq_true_eq, Blk6.bnd]
    interval_cases r
    · exact blk_one0 hw h₁ h₂ h₃ h₄ h₅ h₆ D hd
    · exact blk_one1 hw h₁ h₂ h₃ h₄ h₅ h₆ D hd
    · exact blk_one2 hw h₁ h₂ h₃ h₄ h₅ h₆ D hd
    · rw [sum_filter_rev66, sum_all_rev66]
      have := blk_one2 hw h₆ h₅ h₄ h₃ h₂ h₁ D hd
      rw [βQ6_comm] at this
      exact this
    · rw [sum_filter_rev66, sum_all_rev66]
      have := blk_one1 hw h₆ h₅ h₄ h₃ h₂ h₁ D hd
      rw [βQ6_comm] at this
      exact this
    · rw [sum_filter_rev66, sum_all_rev66]
      have := blk_one0 hw h₆ h₅ h₄ h₃ h₂ h₁ D hd
      rw [βQ6_comm] at this
      exact this
  | two r D D' d d' =>
    obtain ⟨hr, hd, hd'⟩ := hb
    simp only [Blk6.ev, Bool.and_eq_true, decide_eq_true_eq, Blk6.bnd]
    interval_cases r
    · have := blk_two0 hw h₁ h₂ h₃ h₄ h₅ h₆ D D' hd hd'
      simp only [Finset.mem_product] at this
      refine le_of_eq_of_le ?_ this
      refine Finset.sum_congr (Finset.filter_congr fun t _ => ?_) fun _ _ => rfl
      simp only [rowAt]; try tauto
    · have := blk_two1 hw h₁ h₂ h₃ h₄ h₅ h₆ D D' hd hd'
      simp only [Finset.mem_product] at this
      refine le_of_eq_of_le ?_ this
      refine Finset.sum_congr (Finset.filter_congr fun t _ => ?_) fun _ _ => rfl
      simp only [rowAt]; try tauto
    · have := blk_two2 hw h₁ h₂ h₃ h₄ h₅ h₆ D D' hd hd'
      simp only [Finset.mem_product] at this
      refine le_of_eq_of_le ?_ this
      refine Finset.sum_congr (Finset.filter_congr fun t _ => ?_) fun _ _ => rfl
      simp only [rowAt]; try tauto
    · rw [sum_filter_rev66, sum_all_rev66]
      have := blk_two1 hw h₆ h₅ h₄ h₃ h₂ h₁ D' D hd' hd
      rw [βQ6_comm, Nat.mul_comm] at this
      simp only [Finset.mem_product] at this
      refine le_of_eq_of_le ?_ this
      refine Finset.sum_congr (Finset.filter_congr fun t _ => ?_) fun _ _ => rfl
      simp only [rev6, rowAt, r1, r2, r3, r4, r5, r6]; tauto
    · rw [sum_filter_rev66, sum_all_rev66]
      have := blk_two0 hw h₆ h₅ h₄ h₃ h₂ h₁ D' D hd' hd
      rw [βQ6_comm, Nat.mul_comm] at this
      simp only [Finset.mem_product] at this
      refine le_of_eq_of_le ?_ this
      refine Finset.sum_congr (Finset.filter_congr fun t _ => ?_) fun _ _ => rfl
      simp only [rev6, rowAt, r1, r2, r3, r4, r5, r6]; tauto
  | three r D D' D'' d d' d'' =>
    obtain ⟨hr, hd, hd', hd''⟩ := hb
    simp only [Blk6.ev, Bool.and_eq_true, decide_eq_true_eq, Blk6.bnd]
    interval_cases r
    · have := blk_three0 hw h₁ h₂ h₃ h₄ h₅ h₆ D D' D'' hd hd' hd''
      simp only [Finset.mem_product] at this
      refine le_of_eq_of_le ?_ this
      refine Finset.sum_congr (Finset.filter_congr fun t _ => ?_) fun _ _ => rfl
      simp only [rowAt]; try tauto
    · have := blk_three1 hw h₁ h₂ h₃ h₄ h₅ h₆ D D' D'' hd hd' hd''
      simp only [Finset.mem_product] at this
      refine le_of_eq_of_le ?_ this
      refine Finset.sum_congr (Finset.filter_congr fun t _ => ?_) fun _ _ => rfl
      simp only [rowAt]; try tauto
    · rw [sum_filter_rev66, sum_all_rev66]
      have := blk_three1 hw h₆ h₅ h₄ h₃ h₂ h₁ D'' D' D hd'' hd' hd
      rw [βQ6_comm, show d'' * d' * d = d * d' * d'' by ring] at this
      simp only [Finset.mem_product] at this
      refine le_of_eq_of_le ?_ this
      refine Finset.sum_congr (Finset.filter_congr fun t _ => ?_) fun _ _ => rfl
      simp only [rev6, rowAt, r1, r2, r3, r4, r5, r6]; tauto
    · rw [sum_filter_rev66, sum_all_rev66]
      have := blk_three0 hw h₆ h₅ h₄ h₃ h₂ h₁ D'' D' D hd'' hd' hd
      rw [βQ6_comm, show d'' * d' * d = d * d' * d'' by ring] at this
      simp only [Finset.mem_product] at this
      refine le_of_eq_of_le ?_ this
      refine Finset.sum_congr (Finset.filter_congr fun t _ => ?_) fun _ _ => rfl
      simp only [rev6, rowAt, r1, r2, r3, r4, r5, r6]; tauto

/-! ### Pins -/

/-- A pin: a block and a peeling chain. -/
structure Pin6 where
  blk : Blk6
  peels : List Fac6

namespace Pin6

def ev (q : Pin6) (t : T6) : Bool := allEv6 q.peels t && q.blk.ev t

def bnd (q : Pin6) : ℚ := (q.peels.map (Fac6.bnd qX)).prod * q.blk.bnd

def OK (q : Pin6) : Prop := q.blk.ok ∧ PeelOK6 q.blk.reads q.peels

end Pin6

/-- **A pin carries at most its bound.** -/
theorem pin_sum6 (hw : InCone6 w) (h₁ : 5 ≤ X₁.card) (h₂ : 5 ≤ X₂.card) (h₃ : 5 ≤ X₃.card)
    (h₄ : 5 ≤ X₄.card) (h₅ : 5 ≤ X₅.card) (h₆ : 5 ≤ X₆.card) (q : Pin6) (hq : q.OK) :
    ∑ t ∈ (sts X₁ X₂ X₃ X₄ X₅ X₆).filter (fun t => q.ev t = true), GU 6 w t
      ≤ ((q.bnd : ℚ) : ℝ) * ∑ t ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, GU 6 w t := by
  have h1 := peel_chain6 (fibOK_GU hw h₁ h₂ h₃ h₄ h₅ h₆) (GU_nonneg hw) qX_nonneg q.blk.reads
    q.blk.ev (fun i hi hr t x => Blk6.ev_setAt hq.1 hi hr t x) q.peels hq.2
  have h2 := blk_bound6 hw h₁ h₂ h₃ h₄ h₅ h₆ q.blk hq.1
  have hp : (0 : ℝ) ≤ (((q.peels.map (Fac6.bnd qX)).prod : ℚ) : ℝ) := by
    have : (0 : ℚ) ≤ (q.peels.map (Fac6.bnd qX)).prod :=
      List.prod_nonneg (fun x hx => by
        obtain ⟨f, -, rfl⟩ := List.mem_map.mp hx; exact f.bnd_nonneg qX_nonneg)
    exact_mod_cast this
  calc _ ≤ (((q.peels.map (Fac6.bnd qX)).prod : ℚ) : ℝ)
        * ∑ t ∈ (sts X₁ X₂ X₃ X₄ X₅ X₆).filter (fun t => q.blk.ev t = true), GU 6 w t := h1
    _ ≤ (((q.peels.map (Fac6.bnd qX)).prod : ℚ) : ℝ)
        * (((q.blk.bnd : ℚ) : ℝ) * ∑ t ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, GU 6 w t) :=
        mul_le_mul_of_nonneg_left h2 hp
    _ = _ := by unfold Pin6.bnd; push_cast; ring

end bound

end GridGen.Six
