import GridGen.PolymerBlockEdges

/-!
# Decomposing a spanning edge set into its connected blocks

This module builds the finite bijection needed to factor each coefficient of the grouped
Whitney expansion. Edge families are indexed by the parts of an actual vertex partition.
-/

namespace GridGen.Polymer

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem compFinset_eq_of_closed_connected {T : Finset (Sym2 V)} {S : Finset V}
    (hc : ClosedOn T S) (hn : ConnectedOn T S) {v : V} (hv : v ∈ S) :
    compFinset T ((edgeGraph T).connectedComponentMk v) = S := by
  ext u
  rw [mem_compFinset]
  constructor
  · intro hu
    exact reachable_mem_of_closed hc hv (ConnectedComponent.exact hu).symm
  · intro hu
    exact ConnectedComponent.sound (hn.2 u hu v hv)

theorem componentPartition_eq_of_closed_connected (T : Finset (Sym2 V))
    (P : Finpartition (univ : Finset V))
    (hc : ∀ S ∈ P.parts, ClosedOn T S)
    (hn : ∀ S ∈ P.parts, ConnectedOn T S) : componentPartition T = P := by
  apply Finpartition.ext
  ext S
  rw [mem_componentPartition_parts]
  constructor
  · rintro ⟨C, rfl⟩
    obtain ⟨v, hv⟩ := compFinset_nonempty T C
    obtain ⟨S, hS, hvS⟩ := P.exists_mem (Finset.mem_univ v)
    have heq := compFinset_eq_of_closed_connected (hc S hS) (hn S hS) hvS
    rw [mem_compFinset.mp hv] at heq
    rwa [heq]
  · intro hS
    obtain ⟨v, hv⟩ := P.nonempty_of_mem_parts hS
    exact ⟨_, compFinset_eq_of_closed_connected (hc S hS) (hn S hS) hv⟩

variable (P : Finpartition (univ : Finset V))

def familyUnion (f : P.parts → Finset (Sym2 V)) : Finset (Sym2 V) := univ.biUnion f

@[simp] theorem mem_familyUnion {f : P.parts → Finset (Sym2 V)} {e : Sym2 V} :
    e ∈ familyUnion P f ↔ ∃ S, e ∈ f S := by simp [familyUnion]

/-- Recover each member of an endpoint-supported edge family from its union. -/
theorem edgesWithin_familyUnion (f : P.parts → Finset (Sym2 V))
    (hs : ∀ S, ∀ e ∈ f S, ∀ v ∈ e, v ∈ S.1) (S : P.parts) :
    edgesWithin (familyUnion P f) S.1 = f S := by
  ext e
  rw [mem_edgesWithin, mem_familyUnion]
  constructor
  · rintro ⟨⟨R, heR⟩, heS⟩
    have hRS : R = S := by
      apply Subtype.ext
      induction e using Sym2.ind with
      | _ u v =>
        exact P.eq_of_mem_parts R.2 S.2
          (hs R _ heR u (Sym2.mem_mk_left _ _)) (heS u (Sym2.mem_mk_left _ _))
    simpa only [hRS] using heR
  · intro he
    exact ⟨⟨S, he⟩, hs S e he⟩

theorem closedOn_familyUnion (f : P.parts → Finset (Sym2 V))
    (hs : ∀ S, ∀ e ∈ f S, ∀ v ∈ e, v ∈ S.1) (S : P.parts) :
    ClosedOn (familyUnion P f) S.1 := by
  intro u hu v hadj
  obtain ⟨hmem, _⟩ := (fromEdgeSet_adj _).mp hadj
  obtain ⟨R, he⟩ := (mem_familyUnion P).mp hmem
  have hRS := P.eq_of_mem_parts R.2 S.2
    (hs R _ he u (Sym2.mem_mk_left _ _)) hu
  rw [← hRS]
  exact hs R _ he v (Sym2.mem_mk_right _ _)

theorem componentPartition_familyUnion (f : P.parts → Finset (Sym2 V))
    (hs : ∀ S, ∀ e ∈ f S, ∀ v ∈ e, v ∈ S.1)
    (hn : ∀ S, ConnectedOn (f S) S.1) : componentPartition (familyUnion P f) = P := by
  apply componentPartition_eq_of_closed_connected
  · intro S hS
    exact closedOn_familyUnion P f hs ⟨S, hS⟩
  · intro S hS
    refine ⟨(hn ⟨S, hS⟩).1, ?_⟩
    intro u hu v hv
    apply ((hn ⟨S, hS⟩).2 u hu v hv).mono
    intro x y hxy
    rw [fromEdgeSet_adj] at hxy ⊢
    exact ⟨(mem_familyUnion P).mpr ⟨⟨S, hS⟩, hxy.1⟩, hxy.2⟩


/-- Different vertex blocks give disjoint edge sets, since every edge has an endpoint. -/
theorem family_disjoint (f : P.parts → Finset (Sym2 V))
    (hs : ∀ S, ∀ e ∈ f S, ∀ v ∈ e, v ∈ S.1) :
    Pairwise (fun S R => Disjoint (f S) (f R)) := by
  intro S R hne
  apply Finset.disjoint_left.mpr
  intro e heS heR
  apply hne
  apply Subtype.ext
  induction e using Sym2.ind with
  | _ u v =>
    exact P.eq_of_mem_parts S.2 R.2
      (hs S _ heS u (Sym2.mem_mk_left _ _)) (hs R _ heR u (Sym2.mem_mk_left _ _))

theorem card_familyUnion (f : P.parts → Finset (Sym2 V))
    (hs : ∀ S, ∀ e ∈ f S, ∀ v ∈ e, v ∈ S.1) :
    (familyUnion P f).card = ∑ S, (f S).card := by
  apply Finset.card_biUnion
  intro S _ R _ hne
  exact family_disjoint P f hs hne

/-- Every actual component is closed, and its internally restricted edge set connects it. -/
theorem componentPart_closed_connected (T : Finset (Sym2 V)) {S : Finset V}
    (hS : S ∈ (componentPartition T).parts) :
    ClosedOn T S ∧ ConnectedOn (edgesWithin T S) S := by
  obtain ⟨C, rfl⟩ := (mem_componentPartition_parts T S).mp hS
  have hc : ClosedOn T (compFinset T C) := by
    intro u hu v hadj
    apply mem_compFinset.mpr
    exact (ConnectedComponent.sound hadj.reachable).symm.trans (mem_compFinset.mp hu)
  refine ⟨hc, compFinset_nonempty T C, ?_⟩
  intro u hu v hv
  apply reachable_edgesWithin_of_closed hc hu
  exact ConnectedComponent.exact ((mem_compFinset.mp hu).trans (mem_compFinset.mp hv).symm)

/-- Each edge belongs wholly to some actual component, including the harmless loop case. -/
theorem edge_in_componentPart (T : Finset (Sym2 V)) {e : Sym2 V} (he : e ∈ T) :
    ∃ S ∈ (componentPartition T).parts, ∀ v ∈ e, v ∈ S := by
  induction e using Sym2.ind with
  | _ u v =>
    have huv : (edgeGraph T).Reachable u v := by
      by_cases h : u = v
      · subst v; exact .rfl
      · exact (show (edgeGraph T).Adj u v from ⟨he, h⟩).reachable
    refine ⟨compFinset T ((edgeGraph T).connectedComponentMk u), ?_, ?_⟩
    · exact (mem_componentPartition_parts _ _).mpr ⟨_, rfl⟩
    · intro x hx
      rcases Sym2.mem_iff.mp hx with rfl | rfl
      · simp
      · exact mem_compFinset.mpr (ConnectedComponent.sound huv).symm

/-- Splitting into actual components and reuniting loses no edges. -/
theorem familyUnion_edgesWithin (T : Finset (Sym2 V))
    (hP : componentPartition T = P) :
    familyUnion P (fun S => edgesWithin T S.1) = T := by
  ext e
  rw [mem_familyUnion]
  constructor
  · rintro ⟨S, he⟩
    exact (mem_edgesWithin.mp he).1
  · intro he
    obtain ⟨S, hS, heS⟩ := edge_in_componentPart T he
    rw [hP] at hS
    exact ⟨⟨S, hS⟩, mem_edgesWithin.mpr ⟨he, heS⟩⟩

end GridGen.Polymer
