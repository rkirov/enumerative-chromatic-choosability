import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# A finite induction for normalized polymer partition functions

`positive_mono_of_root_recursion` proves positivity and monotonicity under vertex deletion
from a root recurrence and a local one-sided activity budget. This is the induction used by
the full-grid interpolation argument, independent of the number of vertices.

The normalized partition function is the unnormalized one divided by `q^|U|`. Thus its
monotonicity says that removing one vertex costs at least a factor `q` before normalization.
No positivity or ratio estimates are assumed: they are conclusions of the finite induction.
This module does not assert that graph-colouring partition functions meet its hypotheses.
-/

namespace GridGen.Polymer

open Finset

variable {V : Type*} [DecidableEq V]

def rootedBlocks (U : Finset V) (v : V) : Finset (Finset V) :=
  U.powerset.filter (fun S => v ∈ S ∧ 2 ≤ S.card)

theorem mem_rootedBlocks {U S : Finset V} {v : V} (h : S ∈ rootedBlocks U v) :
    S ⊆ U ∧ v ∈ S ∧ 2 ≤ S.card := by
  simpa only [rootedBlocks, Finset.mem_filter, Finset.mem_powerset] using h

theorem sdiff_subset_erase_of_mem {U S : Finset V} {v : V} (hv : v ∈ S) :
    U \ S ⊆ U.erase v := by
  intro x hx
  rw [Finset.mem_sdiff] at hx
  exact Finset.mem_erase.mpr ⟨fun h => hx.2 (h ▸ hv), hx.1⟩

/-- Positivity and all subset ratios, simultaneously, from the root recurrence. Only the
harmful part of each activity is charged: `b S` is a penalty with `-b S ≤ w S`, and the
penalties at each root must fit inside the singleton surplus `a - 1`. Activities known to be
nonnegative take `b S = 0`; taking `b S = |w S|` recovers the absolute-activity budget. -/
theorem positive_mono_of_root_recursion (z w b : Finset V → ℝ) (a : ℝ)
    (hz0 : z ∅ = 1)
    (hrec : ∀ U v, v ∈ U → z U = a * z (U.erase v) +
      ∑ S ∈ rootedBlocks U v, w S * z (U \ S))
    (hb : ∀ S, 0 ≤ b S)
    (hwb : ∀ S, -b S ≤ w S)
    (hsmall : ∀ U v, v ∈ U → ∑ S ∈ rootedBlocks U v, b S ≤ a - 1) :
    ∀ U, 0 < z U ∧ ∀ B, B ⊆ U → z B ≤ z U := by
  intro U
  induction U using Finset.strongInductionOn with
  | _ U ih =>
    by_cases hU : U = ∅
    · subst U
      refine ⟨by rw [hz0]; norm_num, ?_⟩
      intro B hB
      have : B = ∅ := Finset.subset_empty.mp hB
      rw [this]
    have hdel : ∀ v, v ∈ U → z (U.erase v) ≤ z U := by
      intro v hv
      have hi := ih (U.erase v) (Finset.erase_ssubset hv)
      have hterm : ∀ S ∈ rootedBlocks U v,
          -b S * z (U.erase v) ≤ w S * z (U \ S) := by
        intro S hS
        have hsub := sdiff_subset_erase_of_mem (U := U) (mem_rootedBlocks hS).2.1
        have hpos : 0 ≤ z (U \ S) := by
          have hproper : U \ S ⊂ U :=
            lt_of_le_of_lt hsub (Finset.erase_ssubset hv)
          exact (ih _ hproper).1.le
        have hle := hi.2 _ hsub
        calc -b S * z (U.erase v) ≤ -b S * z (U \ S) :=
            mul_le_mul_of_nonpos_left hle (neg_nonpos.mpr (hb S))
          _ ≤ w S * z (U \ S) := mul_le_mul_of_nonneg_right (hwb S) hpos
      have hsum := Finset.sum_le_sum hterm
      rw [← Finset.sum_mul, Finset.sum_neg_distrib] at hsum
      have hbudget := mul_le_mul_of_nonneg_right (hsmall U v hv) hi.1.le
      rw [hrec U v hv]
      nlinarith
    obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hU
    refine ⟨lt_of_lt_of_le (ih _ (Finset.erase_ssubset hv)).1 (hdel v hv), ?_⟩
    intro B hB
    by_cases heq : B = U
    · rw [heq]
    obtain ⟨v, hv, hvB⟩ := Finset.exists_of_ssubset (lt_of_le_of_ne hB heq)
    have hsub : B ⊆ U.erase v := by
      intro b hb
      exact Finset.mem_erase.mpr ⟨fun h => hvB (h ▸ hb), hB hb⟩
    exact le_trans ((ih _ (Finset.erase_ssubset hv)).2 _ hsub) (hdel v hv)

end GridGen.Polymer


