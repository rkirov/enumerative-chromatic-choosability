import GridGen.PolymerGraphPartition

/-!
# Connected edge sets on one vertex block

All edge sets live in the same ambient vertex type. `edgesWithin` restricts their endpoints;
`ConnectedOn` asks for connectivity only on the indicated nonempty vertex set.
-/

namespace GridGen.Polymer

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

def edgesWithin (T : Finset (Sym2 V)) (S : Finset V) : Finset (Sym2 V) :=
  T.filter (fun e => ∀ v ∈ e, v ∈ S)

@[simp] theorem mem_edgesWithin {T : Finset (Sym2 V)} {S : Finset V} {e : Sym2 V} :
    e ∈ edgesWithin T S ↔ e ∈ T ∧ ∀ v ∈ e, v ∈ S := Finset.mem_filter

theorem edgesWithin_subset (T : Finset (Sym2 V)) (S : Finset V) :
    edgesWithin T S ⊆ T := Finset.filter_subset _ _

def ConnectedOn (T : Finset (Sym2 V)) (S : Finset V) : Prop :=
  S.Nonempty ∧ ∀ u ∈ S, ∀ v ∈ S, (edgeGraph T).Reachable u v

/-- A set is closed if no edge can leave it. -/
def ClosedOn (T : Finset (Sym2 V)) (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v, (edgeGraph T).Adj u v → v ∈ S

omit [Fintype V] [DecidableEq V] in
theorem reachable_mem_of_closed {T : Finset (Sym2 V)} {S : Finset V}
    (hclosed : ClosedOn T S) {u v : V} (hu : u ∈ S)
    (h : (edgeGraph T).Reachable u v) : v ∈ S := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact hu
  | cons hadj p ih => exact ih (hclosed _ hu _ hadj)

theorem edgesWithin_adj {T : Finset (Sym2 V)} {S : Finset V} {u v : V} :
    (edgeGraph (edgesWithin T S)).Adj u v ↔
      (edgeGraph T).Adj u v ∧ u ∈ S ∧ v ∈ S := by
  simp only [edgeGraph, fromEdgeSet_adj, Finset.mem_coe, mem_edgesWithin]
  constructor
  · rintro ⟨⟨hT, hS⟩, hne⟩
    exact ⟨⟨hT, hne⟩, hS u (Sym2.mem_mk_left _ _), hS v (Sym2.mem_mk_right _ _)⟩
  · rintro ⟨⟨hT, hne⟩, hu, hv⟩
    refine ⟨⟨hT, ?_⟩, hne⟩
    intro x hx
    rcases Sym2.mem_iff.mp hx with rfl | rfl
    · exact hu
    · exact hv

theorem reachable_edgesWithin_of_closed {T : Finset (Sym2 V)} {S : Finset V}
    (hclosed : ClosedOn T S) {u v : V} (hu : u ∈ S)
    (h : (edgeGraph T).Reachable u v) :
    (edgeGraph (edgesWithin T S)).Reachable u v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact .rfl
  | cons hadj p ih =>
    have hv := hclosed _ hu _ hadj
    exact (edgesWithin_adj.mpr ⟨hadj, hu, hv⟩).reachable.trans (ih hv)

theorem reachable_of_edgesWithin {T : Finset (Sym2 V)} {S : Finset V} {u v : V}
    (h : (edgeGraph (edgesWithin T S)).Reachable u v) : (edgeGraph T).Reachable u v :=
  h.mono (fun _ _ h => (edgesWithin_adj.mp h).1)

/-- Connected spanning edge sets on a vertex block, using only edges of `G`. -/
noncomputable def blockEdgeSets (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : Finset (Finset (Sym2 V)) := by
  classical
  exact (edgesWithin G.edgeFinset S).powerset.filter (fun T => ConnectedOn T S)

theorem mem_blockEdgeSets (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} {T : Finset (Sym2 V)} :
    T ∈ blockEdgeSets G S ↔ T ⊆ edgesWithin G.edgeFinset S ∧ ConnectedOn T S := by
  classical
  simp only [blockEdgeSets, Finset.mem_filter, Finset.mem_powerset]

/-- The actual connected-block coefficient in the polymer interpolation. -/
noncomputable def blockCoefficient (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : ℝ := ∑ T ∈ blockEdgeSets G S, (-1 : ℝ) ^ T.card

end GridGen.Polymer
