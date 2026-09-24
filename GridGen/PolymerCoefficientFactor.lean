import GridGen.PolymerEdgeFamilies

/-!
# Factoring the grouped Whitney coefficient

A choice of a connected spanning edge set in each block is in bijection with a spanning
edge set having exactly that component partition. The union is disjoint, so its alternating
sign is the product of the block signs. All sums remain symbolic and finite.
-/

namespace GridGen.Polymer

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem partitionCoefficient_eq_prod (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) :
    partitionCoefficient G P = ∏ S ∈ P.parts, blockCoefficient G S := by
  classical
  let families := Fintype.piFinset (fun S : P.parts => blockEdgeSets G S.1)
  have hs : ∀ f ∈ families, ∀ S, ∀ e ∈ f S, ∀ v ∈ e, v ∈ S.1 := by
    intro f hf S e he v hv
    have hS := (mem_blockEdgeSets G).mp ((Fintype.mem_piFinset.mp hf) S)
    exact (mem_edgesWithin.mp (hS.1 he)).2 v hv
  have hn : ∀ f ∈ families, ∀ S, ConnectedOn (f S) S.1 := by
    intro f hf S
    exact ((mem_blockEdgeSets G).mp ((Fintype.mem_piFinset.mp hf) S)).2
  rw [partitionCoefficient, ← Finset.prod_coe_sort]
  simp only [blockCoefficient]
  rw [Finset.prod_univ_sum]
  symm
  change (∑ f ∈ families, ∏ S, (-1 : ℝ) ^ (f S).card) = _
  refine Finset.sum_bij (fun f _ => familyUnion P f) ?_ ?_ ?_ ?_
  · intro f hf
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr ?_, componentPartition_familyUnion P f (hs f hf) (hn f hf)⟩
    intro e he
    obtain ⟨S, heS⟩ := (mem_familyUnion P).mp he
    exact (mem_edgesWithin.mp
      (((mem_blockEdgeSets G).mp ((Fintype.mem_piFinset.mp hf) S)).1 heS)).1
  · intro f hf g hg heq
    funext S
    rw [← edgesWithin_familyUnion P f (hs f hf) S, heq,
      edgesWithin_familyUnion P g (hs g hg) S]
  · intro T hT
    obtain ⟨hTG, hTP⟩ := Finset.mem_filter.mp hT
    have hTG : T ⊆ G.edgeFinset := Finset.mem_powerset.mp hTG
    refine ⟨fun S => edgesWithin T S.1, ?_, familyUnion_edgesWithin P T hTP⟩
    apply Fintype.mem_piFinset.mpr
    intro S
    apply (mem_blockEdgeSets G).mpr
    refine ⟨?_, (componentPart_closed_connected T (by rw [hTP]; exact S.2)).2⟩
    intro e he
    have he := mem_edgesWithin.mp he
    exact mem_edgesWithin.mpr ⟨hTG he.1, he.2⟩
  · intro f hf
    rw [card_familyUnion P f (hs f hf), Finset.prod_pow_eq_pow_sum]

/-- The list coloring count is the actual finite polymer partition sum with connected-block
coefficients and list-intersection weights. -/
theorem col_eq_partitionSum (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : ListAssignment V) :
    (G.col L : ℝ) = partitionSum
      (fun S => blockCoefficient G S * (listInter L S).card) univ := by
  classical
  rw [col_eq_sum_partitions, partitionSum]
  apply Finset.sum_congr rfl
  intro P _
  rw [partitionCoefficient_eq_prod, Finset.prod_mul_distrib]

end GridGen.Polymer
