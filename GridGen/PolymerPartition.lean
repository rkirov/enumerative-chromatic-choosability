import Mathlib.Order.Partition.Finpartition
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Finite partition identities for the full-grid interpolation

Deleting a distinguished block is a bijection with partitions of its complement.
These are identities for actual finite partition sums, not assumed recurrences.
-/

namespace GridGen.Polymer

open Finset

variable {V : Type*} [DecidableEq V] {U S : Finset V}

/-- Remove one whole block, leaving a partition of its complement. -/
def removeBlock (P : Finpartition U) (hS : S ∈ P.parts) : Finpartition (U \ S) :=
  Finpartition.ofExistsUnique (P.parts.erase S)
    (by
      intro T hT x hx
      obtain ⟨hne, hT⟩ := Finset.mem_erase.mp hT
      exact Finset.mem_sdiff.mpr ⟨P.le hT hx, fun hxS =>
        hne (P.eq_of_mem_parts hT hS hx hxS)⟩)
    (by
      intro x hx
      obtain ⟨hxU, hxS⟩ := Finset.mem_sdiff.mp hx
      obtain ⟨T, hT, hxT⟩ := P.exists_mem hxU
      refine ⟨T, ⟨Finset.mem_erase.mpr ⟨?_, hT⟩, hxT⟩, ?_⟩
      · intro heq
        exact hxS (heq ▸ hxT)
      · intro R hR
        exact P.eq_of_mem_parts (Finset.mem_erase.mp hR.1).2 hT hR.2 hxT)
    (by simp)

@[simp] theorem removeBlock_parts (P : Finpartition U) (hS : S ∈ P.parts) :
    (removeBlock P hS).parts = P.parts.erase S := rfl

/-- Insert a nonempty block into a partition of its complement. -/
def addBlock (hSU : S ⊆ U) (hS : S.Nonempty) (Q : Finpartition (U \ S)) :
    Finpartition U :=
  Q.extend hS.ne_empty disjoint_sdiff_self_left (Finset.sdiff_union_of_subset hSU)

@[simp] theorem addBlock_parts (hSU : S ⊆ U) (hS : S.Nonempty)
    (Q : Finpartition (U \ S)) :
    (addBlock hSU hS Q).parts = insert S Q.parts := rfl

theorem block_notMem_complement (hS : S.Nonempty) (Q : Finpartition (U \ S)) :
    S ∉ Q.parts := by
  intro h
  obtain ⟨v, hv⟩ := hS
  exact (Finset.mem_sdiff.mp (Q.le h hv)).2 hv

/-- The distinguished-block bijection. -/
def removeBlockEquiv (hSU : S ⊆ U) (hS : S.Nonempty) :
    {P : Finpartition U // S ∈ P.parts} ≃ Finpartition (U \ S) where
  toFun P := removeBlock P.1 P.2
  invFun Q := ⟨addBlock hSU hS Q, by simp⟩
  left_inv P := by
    apply Subtype.ext
    apply Finpartition.ext
    simp [P.2]
  right_inv Q := by
    apply Finpartition.ext
    simp [block_notMem_complement hS Q]

/-- The finite partition polynomial evaluated at block weights `w`. -/
noncomputable def partitionSum (w : Finset V → ℝ) (U : Finset V) : ℝ :=
  ∑ P : Finpartition U, ∏ S ∈ P.parts, w S

/-- Summing over partitions containing a prescribed block removes that block exactly once. -/
theorem sum_removed_block (w : Finset V → ℝ) (hSU : S ⊆ U) (hS : S.Nonempty) :
    (∑ P : {P : Finpartition U // S ∈ P.parts}, ∏ T ∈ P.1.parts.erase S, w T) =
      partitionSum w (U \ S) := by
  classical
  exact Fintype.sum_equiv (removeBlockEquiv hSU hS) _ _ (fun P => rfl)


/-- All possible (nonempty) blocks of a partition of `U`. -/
def blocks (U : Finset V) : Finset (Finset V) :=
  U.powerset.filter Finset.Nonempty

theorem parts_subset_blocks (P : Finpartition U) : P.parts ⊆ blocks U := by
  intro S hS
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (P.le hS), P.nonempty_of_mem_parts hS⟩

theorem sum_parts_eq_sum_blocks (P : Finpartition U) (f : Finset V → ℝ) :
    (∑ S ∈ P.parts, f S) =
      ∑ S ∈ blocks U, if S ∈ P.parts then f S else 0 := by
  classical
  calc
    _ = ∑ S ∈ P.parts, if S ∈ P.parts then f S else 0 := by
      apply Finset.sum_congr rfl
      intro S hS
      simp [hS]
    _ = _ := Finset.sum_subset (parts_subset_blocks P) (by
      intro S _ hS
      simp [hS])

/-- Finite differentiation/combinatorial marking: every distinguished block has exactly
one complementary partition. No factor depending on the number of blocks appears. -/
theorem marked_partition_sum (w f : Finset V → ℝ) :
    (∑ P : Finpartition U, ∑ S ∈ P.parts,
      f S * ∏ T ∈ P.parts.erase S, w T) =
    ∑ S ∈ blocks U, f S * partitionSum w (U \ S) := by
  classical
  simp_rw [sum_parts_eq_sum_blocks]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  obtain ⟨hSU, hSne⟩ := Finset.mem_filter.mp hS
  have hSU : S ⊆ U := Finset.mem_powerset.mp hSU
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (p := fun P : Finpartition U => S ∈ P.parts) _ (by simp)]
  rw [← Finset.mul_sum]
  rw [sum_removed_block w hSU hSne]

/-- Actual root recurrence for a finite partition sum, including its singleton term. -/
theorem partitionSum_root (w : Finset V → ℝ) (v : V) (hv : v ∈ U) :
    partitionSum w U =
      ∑ S ∈ (blocks U).filter (fun S => v ∈ S), w S * partitionSum w (U \ S) := by
  classical
  have hmark := marked_partition_sum (U := U) w (fun S => if v ∈ S then w S else 0)
  have hone : ∀ P : Finpartition U,
      (∑ S ∈ P.parts, (if v ∈ S then w S else 0) *
        ∏ T ∈ P.parts.erase S, w T) = ∏ T ∈ P.parts, w T := by
    intro P
    obtain ⟨R, hR, hvR⟩ := P.exists_mem hv
    rw [Finset.sum_eq_single R]
    · rw [ite_eq_left hvR]
      exact Finset.mul_prod_erase _ _ hR
    · intro S hS hne
      have hvS : v ∉ S := fun h => hne (P.eq_of_mem_parts hS hR h hvR)
      simp [hvS]
    · exact fun h => (h hR).elim
  simp_rw [hone] at hmark
  rw [Finset.sum_filter]
  change (∑ P : Finpartition U, ∏ T ∈ P.parts, w T) = _
  rw [hmark]
  apply Finset.sum_congr rfl
  intro S _
  split_ifs <;> simp

@[simp] theorem partitionSum_empty (w : Finset V → ℝ) : partitionSum w ∅ = 1 := by
  classical
  have hp : ∀ P : Finpartition (∅ : Finset V), P.parts = ∅ :=
    fun P => P.parts_eq_empty_iff.mpr rfl
  let : Unique (Finpartition (∅ : Finset V)) :=
    { default := Finpartition.empty (Finset V)
      uniq := fun P => Finpartition.ext (by rw [hp P, hp _]) }
  simp [partitionSum, hp]

end GridGen.Polymer
