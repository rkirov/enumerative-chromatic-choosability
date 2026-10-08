/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.PolymerModel

/-!
# A degree-sensitive variant of the root induction: deletion ratios only where they are cheap

`positive_mono_of_root_recursion` proves positivity and monotonicity under *every* vertex
deletion, so its root budget has to absorb a root of full degree. Here monotonicity is claimed
only for deleting a vertex that is `small` in the current set (in the graph application: it has
at most `D - 1` neighbours there), while positivity is still claimed for every set.

Harmful blocks are compared with the root-deleted set through a `PeelChain`: a sequence of
single deletions of `small` vertices. For connected blocks such a chain always exists, because
deleting a block outward from its root removes, at every step, a vertex whose parent is already
gone. So the budget `a - 1` is needed only at small roots, and at any other root the weaker
`∑ b < a` keeps the sum positive.
-/

namespace GridGen.Polymer

open Finset

variable {V : Type*} [DecidableEq V]

/-- `PeelChain small B A`: `A` is reached from `B` by deleting one vertex at a time, each
deleted vertex `small` in the set it is deleted from. -/
inductive PeelChain (small : Finset V → V → Prop) : Finset V → Finset V → Prop
  | refl (A : Finset V) : PeelChain small A A
  | step {B A : Finset V} {u : V} : u ∈ B → small B u → PeelChain small (B.erase u) A →
      PeelChain small B A

theorem PeelChain.subset {small : Finset V → V → Prop} {B A : Finset V}
    (h : PeelChain small B A) : A ⊆ B := by
  induction h with
  | refl => exact subset_refl _
  | step _ _ _ ih => exact ih.trans (erase_subset _ _)

/-- A peel chain is monotone for any function that does not increase under small deletions
inside the chain's starting set. -/
theorem PeelChain.le {small : Finset V → V → Prop} (z : Finset V → ℝ) {B A : Finset V}
    (h : PeelChain small B A) :
    (∀ C u, C ⊆ B → u ∈ C → small C u → z (C.erase u) ≤ z C) → z A ≤ z B := by
  induction h with
  | refl => exact fun _ => le_rfl
  | @step B A u hu hs _ ih =>
    intro hz
    exact (ih fun C w hC hw hsw => hz C w (hC.trans (erase_subset _ _)) hw hsw).trans
      (hz B u (subset_refl _) hu hs)

/-- **Positivity everywhere, and the deletion ratio at small vertices.** The root recurrence
`z U = a z(U - v) + ∑ w S z(U ∖ S)` with harmful parts `b S` of the activities; each harmful
rooted block must be peelable from the root-deleted set. At every root the harmful mass stays
below `a` (positivity), and at a small root it fits inside `a - 1` (the ratio). -/
theorem positive_peel_of_root_recursion (z w b : Finset V → ℝ) (a : ℝ)
    (small : Finset V → V → Prop)
    (hz0 : z ∅ = 1)
    (hrec : ∀ U v, v ∈ U → z U = a * z (U.erase v) +
      ∑ S ∈ rootedBlocks U v, w S * z (U \ S))
    (hb : ∀ S, 0 ≤ b S)
    (hwb : ∀ S, -b S ≤ w S)
    (hpeel : ∀ U v S, v ∈ U → S ∈ rootedBlocks U v → b S ≠ 0 →
      PeelChain small (U.erase v) (U \ S))
    (hpos : ∀ U v, v ∈ U → ∑ S ∈ rootedBlocks U v, b S < a)
    (hsmall : ∀ U v, v ∈ U → small U v → ∑ S ∈ rootedBlocks U v, b S ≤ a - 1) :
    ∀ U, 0 < z U ∧ ∀ u, u ∈ U → small U u → z (U.erase u) ≤ z U := by
  intro U
  induction U using Finset.strongInductionOn with
  | _ U ih =>
    by_cases hU : U = ∅
    · subst U
      exact ⟨by rw [hz0]; norm_num, fun u hu => absurd hu (Finset.notMem_empty u)⟩
    -- the root recurrence at `v`, with the harmful part charged to `z (U - v)`
    have hroot : ∀ v, v ∈ U →
        (a - ∑ S ∈ rootedBlocks U v, b S) * z (U.erase v) ≤ z U := by
      intro v hv
      have hi := ih (U.erase v) (Finset.erase_ssubset hv)
      have hterm : ∀ S ∈ rootedBlocks U v,
          -b S * z (U.erase v) ≤ w S * z (U \ S) := by
        intro S hS
        have hsub := sdiff_subset_erase_of_mem (U := U) (mem_rootedBlocks hS).2.1
        have hproper : U \ S ⊂ U := lt_of_le_of_lt hsub (Finset.erase_ssubset hv)
        have hzS : 0 ≤ z (U \ S) := (ih _ hproper).1.le
        by_cases hb0 : b S = 0
        · rw [hb0, neg_zero, zero_mul]
          exact mul_nonneg (by have := hwb S; rw [hb0] at this; linarith) hzS
        · have hle : z (U \ S) ≤ z (U.erase v) :=
            (hpeel U v S hv hS hb0).le z fun C u hC hu hsu =>
              (ih C (lt_of_le_of_lt hC (Finset.erase_ssubset hv))).2 u hu hsu
          calc -b S * z (U.erase v) ≤ -b S * z (U \ S) :=
              mul_le_mul_of_nonpos_left hle (neg_nonpos.mpr (hb S))
            _ ≤ w S * z (U \ S) := mul_le_mul_of_nonneg_right (hwb S) hzS
      have hsum := Finset.sum_le_sum hterm
      rw [← Finset.sum_mul, Finset.sum_neg_distrib] at hsum
      rw [hrec U v hv]
      nlinarith
    obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hU
    have hzv := (ih _ (Finset.erase_ssubset hv)).1
    refine ⟨lt_of_lt_of_le (mul_pos (by linarith [hpos U v hv]) hzv) (hroot v hv), ?_⟩
    intro u hu hsu
    have hzu := (ih _ (Finset.erase_ssubset hu)).1
    have h1 : 1 ≤ a - ∑ S ∈ rootedBlocks U u, b S := by linarith [hsmall U u hu hsu]
    calc z (U.erase u) = 1 * z (U.erase u) := (one_mul _).symm
      _ ≤ (a - ∑ S ∈ rootedBlocks U u, b S) * z (U.erase u) :=
          mul_le_mul_of_nonneg_right h1 hzu.le
      _ ≤ z U := hroot u hu

/-- The partition-function form, as `partitionSum_positive_mono`. -/
theorem partitionSum_positive_peel (w b : Finset V → ℝ) (a : ℝ)
    (small : Finset V → V → Prop)
    (hsingle : ∀ v, w {v} = a)
    (hb : ∀ S, 0 ≤ b S) (hwb : ∀ S, -b S ≤ w S)
    (hpeel : ∀ U v S, v ∈ U → S ∈ rootedBlocks U v → b S ≠ 0 →
      PeelChain small (U.erase v) (U \ S))
    (hpos : ∀ U v, v ∈ U → ∑ S ∈ rootedBlocks U v, b S < a)
    (hsmall : ∀ U v, v ∈ U → small U v → ∑ S ∈ rootedBlocks U v, b S ≤ a - 1) :
    ∀ U, 0 < partitionSum w U ∧
      ∀ u, u ∈ U → small U u → partitionSum w (U.erase u) ≤ partitionSum w U := by
  apply positive_peel_of_root_recursion (partitionSum w) w b a small (partitionSum_empty w)
  · intro U v hv
    simpa only [hsingle] using partitionSum_root_split w v hv
  · exact hb
  · exact hwb
  · exact hpeel
  · exact hpos
  · exact hsmall

end GridGen.Polymer
