import GridGen.PolymerPartition
import GridGen.PolymerRatio

/-!
# Positivity for actual finite partition sums

This connects the proved partition identity to the finite-induction ratio lemma.
The inputs are only block weights, a constant singleton weight, and a local activity budget.
There is no assumed partition recurrence or assumed positivity in the conclusion.
-/

namespace GridGen.Polymer

open Finset

variable {V : Type*} [DecidableEq V] {U : Finset V}

theorem root_blocks_split (v : V) (hv : v ∈ U) :
    (blocks U).filter (fun S => v ∈ S) = insert {v} (rootedBlocks U v) := by
  ext S
  simp only [blocks, rootedBlocks, Finset.mem_filter, Finset.mem_powerset,
    Finset.mem_insert]
  constructor
  · rintro ⟨⟨hSU, hSne⟩, hvS⟩
    by_cases hc : S.card = 1
    · left
      obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc
      have : v = a := Finset.mem_singleton.mp hvS
      rw [this]
    · right
      exact ⟨hSU, hvS, by have := Finset.card_pos.mpr hSne; omega⟩
  · rintro (rfl | ⟨hSU, hvS, _⟩)
    · exact ⟨⟨Finset.singleton_subset_iff.mpr hv, Finset.singleton_nonempty _⟩,
        Finset.mem_singleton_self _⟩
    · exact ⟨⟨hSU, ⟨v, hvS⟩⟩, hvS⟩

theorem partitionSum_root_split (w : Finset V → ℝ) (v : V) (hv : v ∈ U) :
    partitionSum w U = w {v} * partitionSum w (U.erase v) +
      ∑ S ∈ rootedBlocks U v, w S * partitionSum w (U \ S) := by
  rw [partitionSum_root w v hv, root_blocks_split v hv]
  have hn : {v} ∉ rootedBlocks U v := by simp [rootedBlocks]
  rw [Finset.sum_insert hn, Finset.sdiff_singleton_eq_erase]

/-- Positivity and all deletion ratios for the actual partition function, from a local
one-sided activity budget. This holds for any finite ground set and needs no enumeration. -/
theorem partitionSum_positive_mono (w b : Finset V → ℝ) (a : ℝ)
    (hsingle : ∀ v, w {v} = a)
    (hb : ∀ S, 0 ≤ b S) (hwb : ∀ S, -b S ≤ w S)
    (hsmall : ∀ U v, v ∈ U → ∑ S ∈ rootedBlocks U v, b S ≤ a - 1) :
    ∀ U, 0 < partitionSum w U ∧
      ∀ B, B ⊆ U → partitionSum w B ≤ partitionSum w U := by
  apply positive_mono_of_root_recursion (partitionSum w) w b a (partitionSum_empty w)
  · intro U v hv
    simpa only [hsingle] using partitionSum_root_split w v hv
  · exact hb
  · exact hwb
  · exact hsmall

end GridGen.Polymer


