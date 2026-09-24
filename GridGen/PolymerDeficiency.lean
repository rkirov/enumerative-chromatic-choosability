import ListColoring.Threshold

/-!
# Treewise list-deficiency domination

The existing component deficiency theorem applies separately to every spanning tree,
not only to the induced graph. The lemma below exposes this stronger useful interface:
any edge set connecting all vertices of `U` bounds its deficiency by its own edge sum.
Thus one can keep the individual tree edges when charging the polymer derivative.
-/

namespace GridGen.Polymer

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A connected edge set pays for the list-intersection deficiency. In particular this
applies to each spanning tree on `U`, without replacing its edges by all induced edges. -/
theorem deficiency_le_connecting_edges {L : ListAssignment V} {k : ℕ}
    (hL : IsNListAssignment L k) (U : Finset V) (T : Finset (Sym2 V))
    (r : V) (hr : r ∈ U)
    (hconn : ∀ v ∈ U, (edgeGraph T).Reachable r v) :
    k - (listInter L U).card ≤ ∑ e ∈ T, edgeDef L k e := by
  let C := (edgeGraph T).connectedComponentMk r
  have hU : U ⊆ compFinset T C := by
    intro v hv
    apply mem_compFinset.mpr
    exact (ConnectedComponent.sound (hconn v hv)).symm
  have hinter : compInter L T C ⊆ listInter L U := by
    intro a ha
    apply (mem_listInter ⟨r, hr⟩).mpr
    intro v hv
    exact (mem_listInter (compFinset_nonempty T C)).mp ha v (hU hv)
  calc
    k - (listInter L U).card ≤ k - (compInter L T C).card :=
      Nat.sub_le_sub_left (Finset.card_le_card hinter) k
    _ ≤ ∑ e ∈ compEdges T C, edgeDef L k e := sub_card_compInter_le hL T C
    _ ≤ ∑ e ∈ T, edgeDef L k e :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => Nat.zero_le _)

end GridGen.Polymer
