/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.Uniform

/-!
# Height five: the uniform transfer at `k = 6` and its invariant box

`GridGen/Four/Cone.lean` with five rows, at the one list size `k = 6`.

**The uniform transfer.** A weighted count is a combination of orbit counts
(`G_eq_sum_orb`), so by the uniform orbit counts of `GridGen/Five/Uniform.lean` the weighted
number of uniform successors of a proper column in orbit `i` is the row `rowV i w` of the reduced
transfer matrix applied to `w` (`GU_six`). The uniform transfer of a pattern weight is again a
pattern weight: `GU 6 w s = rowV 0 w · gw (nextW w) s`, with `nextW w i = rowV i w / rowV 0 w`
(`GU_eq`).

**The box.** The transfer maps the per-orbit box `lo5 i ≤ w i ≤ 1` of
`GridGen/Five/Statement.lean` into itself (`nextW_inBox`). For each target orbit `i` the two
inequalities `lo5 i · rowV 0 w ≤ rowV i w ≤ rowV 0 w` are linear in `w`, and a linear form
`∑ cⱼ wⱼ` on a box is at least `∑ min (cⱼ · lo5 j) cⱼ` (`lin_ge`): each coordinate separately
sits at the lower or upper edge, by the sign of its coefficient. These separable corner values are
nonnegative for all eleven targets, an exact rational check (`box_checks`). The tightest is the
lower edge of `01230`, with corner value about `0.0014` against `rowV 0 w ≈ 1550`; every upper
edge has room (at least `14.7`).

**The uniform futures.** `Fu k i` — the weighted uniform futures of a column — is, at `k = 6`,
`fseq i · gw (wseq i)` on proper uniform columns, with `wseq i` in the box and `fseq i > 0`
(`Fu_eq`, `wseq_inBox`, `fseq_pos`), by induction from `Fu k 0 = 1`.
-/

namespace GridGen.Five

open Finset

/-! ### The weighted count by orbits -/

/-- **A weighted count is a combination of orbit counts.** -/
theorem G_eq_sum_orb (w : Wt5) (A B C D E : Finset ℕ) :
    G w A B C D E = ∑ o, (((sts A B C D E).filter (fun t => orb t = o)).card : ℝ) * w o := by
  unfold G gw
  rw [← Finset.sum_fiberwise (sts A B C D E) orb (fun t => w (orb t))]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [Finset.sum_congr rfl (fun t ht => by rw [(Finset.mem_filter.mp ht).2]), Finset.sum_const,
    nsmul_eq_mul]

/-! ### The uniform transfer at `k = 6` -/

/-- The reduced uniform transfer, row `i`, applied to the weights. -/
noncomputable def rowV (i : Fin 11) (w : Wt5) : ℝ := ∑ j, (Vmat i j : ℝ) * w j

/-- **The uniform successors at `k = 6`**: a proper column in orbit `i` has weighted uniform
successor count `rowV i w`. -/
theorem GU_six (w : Wt5) {s : T5} (hs : Proper s) : GU 6 w s = rowV (orb s) w := by
  have h := cntU_canons _ (canon_mem hs)
  unfold GU
  rw [G_eq_sum_orb, rowV, orb_congr (samePat_canon hs), ← h]
  rfl

/-- The next weights of the uniform transfer, normalised by the `01010` row. -/
noncomputable def nextW (w : Wt5) : Wt5 := fun i => rowV i w / rowV 0 w

/-- **The uniform transfer maps a pattern weight to a pattern weight**: the weighted number of
uniform successors of a proper column is `rowV 0 w · gw (nextW w)`. -/
theorem GU_eq (w : Wt5) (hA : rowV 0 w ≠ 0) {s : T5} (hs : Proper s) :
    GU 6 w s = rowV 0 w * gw (nextW w) s := by
  rw [GU_six w hs, gw, nextW, mul_div_cancel₀ _ hA]

/-! ### The invariant box -/

/-- A linear form in the weights, with rational coefficients. -/
noncomputable def lin (c : Fin 11 → ℚ) (w : Wt5) : ℝ := ∑ j, (c j : ℝ) * w j

/-- The separable corner value of a linear form on the box: each coordinate at the edge that
minimises its term. -/
def cornerMin (c : Fin 11 → ℚ) : ℚ := ∑ j, min (c j * lo5 j) (c j)

/-- **A linear form on the box is at least its separable corner value.** -/
theorem lin_ge {w : Wt5} (hw : InBox5 w) (c : Fin 11 → ℚ) : (cornerMin c : ℝ) ≤ lin c w := by
  unfold cornerMin lin
  push_cast
  refine Finset.sum_le_sum fun j _ => ?_
  obtain ⟨hl, hu⟩ := hw j
  rcases le_total 0 (c j : ℝ) with hc | hc
  · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hl hc)
  · exact (min_le_right _ _).trans (by nlinarith)

/-- The coefficients of `rowV i w - lo5 i · rowV 0 w`. -/
def lowCoef (i : Fin 11) (j : Fin 11) : ℚ := (Vmat i j : ℚ) - lo5 i * Vmat 0 j

/-- The coefficients of `rowV 0 w - rowV i w`. -/
def upCoef (i : Fin 11) (j : Fin 11) : ℚ := (Vmat 0 j : ℚ) - Vmat i j

/-- **The box checks**: exact rational separable corner values, all nonnegative, and the
`01010` row positive. -/
theorem box_checks :
    (∀ i : Fin 11, 0 ≤ cornerMin (lowCoef i) ∧ 0 ≤ cornerMin (upCoef i)) ∧
      0 < cornerMin (fun j => (Vmat 0 j : ℚ)) := by
  decide +kernel

theorem lin_lowCoef (i : Fin 11) (w : Wt5) :
    lin (lowCoef i) w = rowV i w - (lo5 i : ℝ) * rowV 0 w := by
  unfold lin lowCoef rowV
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem lin_upCoef (i : Fin 11) (w : Wt5) : lin (upCoef i) w = rowV 0 w - rowV i w := by
  unfold lin upCoef rowV
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The `01010` row is positive on the box. -/
theorem rowV_pos {w : Wt5} (hw : InBox5 w) : 0 < rowV 0 w := by
  have h := lin_ge hw (fun j => (Vmat 0 j : ℚ))
  have hp : (0 : ℝ) < (cornerMin (fun j => (Vmat 0 j : ℚ)) : ℝ) := by
    exact_mod_cast box_checks.2
  have e : lin (fun j => (Vmat 0 j : ℚ)) w = rowV 0 w := by
    unfold lin rowV; push_cast; rfl
  linarith

/-- **Box invariance**: at `k = 6` the uniform transfer maps the box into itself. -/
theorem nextW_inBox {w : Wt5} (hw : InBox5 w) : InBox5 (nextW w) := by
  have hpos := rowV_pos hw
  intro i
  obtain ⟨hl, hu⟩ := box_checks.1 i
  have hl' := lin_ge hw (lowCoef i)
  have hu' := lin_ge hw (upCoef i)
  rw [lin_lowCoef] at hl'
  rw [lin_upCoef] at hu'
  have hl'' : (0 : ℝ) ≤ (cornerMin (lowCoef i) : ℝ) := by exact_mod_cast hl
  have hu'' : (0 : ℝ) ≤ (cornerMin (upCoef i) : ℝ) := by exact_mod_cast hu
  unfold nextW
  constructor
  · rw [le_div_iff₀ hpos]; linarith
  · rw [div_le_one hpos]; linarith

/-- The constant weight `1` lies in the box. -/
theorem one_inBox : InBox5 (fun _ => 1) := by
  intro i
  refine ⟨?_, le_rfl⟩
  have h : ∀ i : Fin 11, lo5 i ≤ 1 := by decide +kernel
  show (lo5 i : ℝ) ≤ 1
  exact_mod_cast h i

/-! ### The uniform futures -/

/-- The weighted uniform futures of a column: `Fu k (i+1) s` sums `Fu k i` over the uniform
successors of `s`. -/
noncomputable def Fu (k : ℕ) : ℕ → T5 → ℝ
  | 0 => fun _ => 1
  | i + 1 => fun s => ∑ t ∈ sts ((range k).erase (r1 s)) ((range k).erase (r2 s))
      ((range k).erase (r3 s)) ((range k).erase (r4 s)) ((range k).erase (r5 s)), Fu k i t

/-- The pattern weights of the uniform futures at `k = 6`. -/
noncomputable def wseq : ℕ → Wt5
  | 0 => fun _ => 1
  | i + 1 => nextW (wseq i)

/-- The `01010` value of the uniform futures at `k = 6`. -/
noncomputable def fseq : ℕ → ℝ
  | 0 => 1
  | i + 1 => fseq i * rowV 0 (wseq i)

theorem wseq_inBox : ∀ i, InBox5 (wseq i)
  | 0 => one_inBox
  | i + 1 => nextW_inBox (wseq_inBox i)

theorem fseq_pos : ∀ i, 0 < fseq i
  | 0 => one_pos
  | i + 1 => mul_pos (fseq_pos i) (rowV_pos (wseq_inBox i))

theorem rowsIn_of_mem_sts_erase {k : ℕ} {s t : T5}
    (ht : t ∈ sts ((range k).erase (r1 s)) ((range k).erase (r2 s)) ((range k).erase (r3 s))
      ((range k).erase (r4 s)) ((range k).erase (r5 s))) : RowsIn t (range k) := by
  rw [mem_sts] at ht
  exact ⟨Finset.mem_of_mem_erase ht.1, Finset.mem_of_mem_erase ht.2.1,
    Finset.mem_of_mem_erase ht.2.2.1, Finset.mem_of_mem_erase ht.2.2.2.1,
    Finset.mem_of_mem_erase ht.2.2.2.2.1⟩

/-- **The uniform futures by pattern**: on proper uniform columns at `k = 6`,
`Fu 6 i = fseq i · gw (wseq i)`, with `wseq i` in the box and `fseq i > 0`. -/
theorem Fu_eq : ∀ i (s : T5), Proper s → RowsIn s (range 6) → Fu 6 i s = fseq i * gw (wseq i) s
  | 0, s, _, _ => by simp [Fu, fseq, wseq, gw]
  | i + 1, s, hs, hP => by
      have hA := (rowV_pos (wseq_inBox i)).ne'
      have hsum : Fu 6 (i + 1) s = fseq i * GU 6 (wseq i) s := by
        simp only [Fu]
        rw [Finset.sum_congr rfl (fun t ht => Fu_eq i t (proper_of_mem_sts ht)
          (rowsIn_of_mem_sts_erase ht)), ← Finset.mul_sum,
          ← G_erase_eq_GU (wseq i) (by norm_num) hs (card_range 6) hP]
        rfl
      rw [hsum, GU_eq _ hA hs]
      simp only [fseq, wseq]
      ring

/-- One step of the uniform futures, as the uniform successor count `GU`. -/
theorem Fu_succ_eq (i : ℕ) {s : T5} (hs : Proper s) (hP : RowsIn s (range 6)) :
    Fu 6 (i + 1) s = fseq i * GU 6 (wseq i) s := by
  rw [Fu_eq (i + 1) s hs hP, GU_eq _ (rowV_pos (wseq_inBox i)).ne' hs]
  simp only [fseq, wseq]
  ring

end GridGen.Five
