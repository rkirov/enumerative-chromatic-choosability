import GridGen.PolymerWalkTree
import GridGen.PolymerTreeGraph

/-!
# Unfolding graph trees into finite walk-tree codes

The ambient graph determines the available ports. The chosen subgraph determines which
ports are occupied. Decoding records actual vertices and edges, forgetting multiplicities.
-/

namespace GridGen.Polymer

open SimpleGraph
open scoped BigOperators

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def walkTreeVertices : {h : ℕ} → {p : Option V} → {v : V} →
    WalkTreeCode G h p v → Finset V
  | 0, _, v, _ => {v}
  | _h + 1, _, v, c => insert v (Finset.univ.biUnion fun w =>
      (c w).elim ∅ (fun t => walkTreeVertices t))

noncomputable def walkTreeEdges : {h : ℕ} → {p : Option V} → {v : V} →
    WalkTreeCode G h p v → Finset (Sym2 V)
  | 0, _, _, _ => ∅
  | _h + 1, _, v, c => Finset.univ.biUnion fun w =>
      (c w).elim ∅ (fun t => insert s(v, w.val) (walkTreeEdges t))

theorem root_mem_walkTreeVertices {h : ℕ} {p : Option V} {v : V}
    (c : WalkTreeCode G h p v) : v ∈ walkTreeVertices G c := by
  cases h <;> simp [walkTreeVertices]

theorem walkTreeVertices_child_subset {h : ℕ} {p : Option V} {v : V}
    (c : WalkTreeCode G (h + 1) p v) (w : childPorts G p v)
    (t : WalkTreeCode G h (some v) w.val) (ht : c w = some t) :
    walkTreeVertices G t ⊆ walkTreeVertices G c := by
  intro z hz
  apply Finset.mem_insert_of_mem
  apply Finset.mem_biUnion.mpr
  exact ⟨w, Finset.mem_univ _, by simpa [ht] using hz⟩

theorem walkTreeEdges_child_subset {h : ℕ} {p : Option V} {v : V}
    (c : WalkTreeCode G (h + 1) p v) (w : childPorts G p v)
    (t : WalkTreeCode G h (some v) w.val) (ht : c w = some t) :
    insert s(v, w.val) (walkTreeEdges G t) ⊆ walkTreeEdges G c := by
  intro e he
  apply Finset.mem_biUnion.mpr
  exact ⟨w, Finset.mem_univ _, by simpa [ht] using he⟩

variable (H : SimpleGraph V) [DecidableRel H.Adj]

/-- Unfold a chosen subgraph, excluding immediate backtracking at each step. -/
noncomputable def unfoldWalkTree : (h : ℕ) → (p : Option V) → (v : V) →
    WalkTreeCode G h p v
  | 0, _, _ => PUnit.unit
  | h + 1, _p, v => fun w =>
      if H.Adj v w.val then some (unfoldWalkTree h (some v) w.val) else none

/-- Every simple path short enough to fit in the code is faithfully represented. -/
theorem path_mem_unfoldWalkTree (hHG : H ≤ G) {v z : V} (q : H.Walk v z)
    (hq : q.IsPath) (h : ℕ) (hlen : q.length ≤ h) (p : Option V)
    (hp : ∀ a, p = some a → a ∉ q.support) :
    z ∈ walkTreeVertices G (unfoldWalkTree G H h p v) ∧
      ∀ e ∈ q.edges, e ∈ walkTreeEdges G (unfoldWalkTree G H h p v) := by
  induction q generalizing h p with
  | nil =>
    exact ⟨root_mem_walkTreeVertices G _, by simp⟩
  | @cons v w z hvw q ih =>
    cases h with
    | zero => simp at hlen
    | succ h =>
      have hpath := (Walk.cons_isPath_iff hvw q).mp hq
      have hw : w ∈ childPorts G p v := by
        apply (mem_childPorts G).mpr
        refine ⟨hHG hvw, ?_⟩
        intro heq
        exact hp w heq.symm (by simp)
      let port : childPorts G p v := ⟨w, hw⟩
      have ht : unfoldWalkTree G H (h + 1) p v port =
          some (unfoldWalkTree G H h (some v) w) := by
        simp [unfoldWalkTree, port, hvw]
      have hi := ih hpath.1 h (by simpa using hlen) (some v) (by
        intro a ha
        have : v = a := Option.some.inj ha
        subst a
        exact hpath.2)
      refine ⟨walkTreeVertices_child_subset G _ port _ ht hi.1, ?_⟩
      intro e he
      apply walkTreeEdges_child_subset G _ port _ ht
      rcases List.mem_cons.mp he with he | he
      · exact Finset.mem_insert.mpr (Or.inl he)
      · exact Finset.mem_insert_of_mem (hi.2 e he)

/-- Decoding never leaves the component of the root in the chosen subgraph. -/
theorem reachable_of_mem_unfoldWalkTree (h : ℕ) (p : Option V) (v : V) {z : V}
    (hz : z ∈ walkTreeVertices G (unfoldWalkTree G H h p v)) : H.Reachable v z := by
  induction h generalizing p v with
  | zero =>
    have : z = v := by simpa [walkTreeVertices, unfoldWalkTree] using hz
    subst z
    exact .rfl
  | succ h ih =>
    rcases Finset.mem_insert.mp hz with hz | hz
    · subst z; exact .rfl
    · obtain ⟨w, _, hw⟩ := Finset.mem_biUnion.mp hz
      by_cases hadj : H.Adj v w.val
      · have hc : z ∈ walkTreeVertices G (unfoldWalkTree G H h (some v) w.val) := by
          simpa [unfoldWalkTree, hadj] using hw
        exact hadj.reachable.trans (ih _ _ hc)
      · simp [unfoldWalkTree, hadj] at hw

theorem mem_unfoldWalkTree_iff_reachable (v z : V) (hHG : H ≤ G) :
    z ∈ walkTreeVertices G (unfoldWalkTree G H (Fintype.card V) none v) ↔
      H.Reachable v z := by
  constructor
  · exact reachable_of_mem_unfoldWalkTree G H _ _ _
  · intro hr
    let q := hr.some.toPath
    exact (path_mem_unfoldWalkTree G H hHG q.val q.property _
      q.property.length_lt.le none (by simp)).1

theorem unfoldWalkTree_edges_subset (h : ℕ) (p : Option V) (v : V) :
    walkTreeEdges G (unfoldWalkTree G H h p v) ⊆ H.edgeFinset := by
  induction h generalizing p v with
  | zero => simp [walkTreeEdges]
  | succ h ih =>
    intro e he
    obtain ⟨w, _, hw⟩ := Finset.mem_biUnion.mp he
    by_cases hadj : H.Adj v w.val
    · have hw' : e ∈ insert s(v, w.val)
          (walkTreeEdges G (unfoldWalkTree G H h (some v) w.val)) := by
        simpa [unfoldWalkTree, hadj] using hw
      rcases Finset.mem_insert.mp hw' with heq | he
      · subst e; exact H.mem_edgeFinset.mpr hadj
      · exact ih _ _ he
    · simp [unfoldWalkTree, hadj] at hw

/-- In a forest, every edge in the root component occurs in one of the two root paths
to its endpoints. -/
theorem edge_mem_unfoldWalkTree (hHG : H ≤ G) (hacyc : H.IsAcyclic)
    {r u v : V} (hu : H.Reachable r u) (huv : H.Adj u v) :
    s(u, v) ∈ walkTreeEdges G (unfoldWalkTree G H (Fintype.card V) none r) := by
  let p := hu.some.toPath
  let q := (hu.trans huv.reachable).some.toPath
  have hp := (path_mem_unfoldWalkTree G H hHG p.val p.property _
    p.property.length_lt.le none (by simp)).2
  have hq := (path_mem_unfoldWalkTree G H hHG q.val q.property _
    q.property.length_lt.le none (by simp)).2
  by_cases hmem : u ∈ q.val.support
  · have heq := hacyc.path_concat p.property q.property huv hmem
    apply hq
    rw [heq, Walk.edges_concat]
    simp
  · have hv := hacyc.mem_support_of_ne_mem_support_of_adj_of_isPath
      p.property q.property huv hmem
    have heq := hacyc.path_concat q.property p.property huv.symm hv
    apply hp
    rw [heq, Walk.edges_concat]
    simp [Sym2.eq_swap]

/-- If every edge belongs to the root component, decoding recovers the entire forest. -/
theorem unfoldWalkTree_edges_eq (hHG : H ≤ G) (hacyc : H.IsAcyclic) (r : V)
    (hr : ∀ u v, H.Adj u v → H.Reachable r u) :
    walkTreeEdges G (unfoldWalkTree G H (Fintype.card V) none r) = H.edgeFinset := by
  apply Finset.Subset.antisymm (unfoldWalkTree_edges_subset G H _ _ _)
  intro e he
  induction e using Sym2.inductionOn with
  | hf u v =>
    have huv : H.Adj u v := H.mem_edgeFinset.mp he
    exact edge_mem_unfoldWalkTree G H hHG hacyc (hr u v huv) huv

omit H [DecidableRel H.Adj] [DecidableEq V] in
theorem edgeGraph_le_of_subset {T : Finset (Sym2 V)} (hT : T ⊆ G.edgeFinset) :
    edgeGraph T ≤ G := by
  intro u v huv
  exact G.mem_edgeFinset.mp (hT huv.1)

omit H [DecidableRel H.Adj] in
theorem edgeFinset_edgeGraph_of_subset {T : Finset (Sym2 V)}
    (hT : T ⊆ G.edgeFinset) : (edgeGraph T).edgeFinset = T := by
  ext e
  induction e using Sym2.inductionOn with
  | hf u v =>
    simp only [mem_edgeFinset, edgeGraph]
    exact ⟨And.left, fun he => ⟨he, (G.mem_edgeFinset.mp (hT he)).ne⟩⟩

omit H [DecidableRel H.Adj] in
theorem spanningTree_unfold_recovers {S : Finset V} {T : Finset (Sym2 V)}
    (hT : T ∈ spanningTreeSets G S) {r : V} (hr : r ∈ S) :
    walkTreeVertices G (unfoldWalkTree G (edgeGraph T) (Fintype.card V) none r) = S ∧
    walkTreeEdges G (unfoldWalkTree G (edgeGraph T) (Fintype.card V) none r) = T := by
  obtain ⟨hb, ha⟩ := (mem_spanningTreeSets G).mp hT
  obtain ⟨hs, hc⟩ := (mem_blockEdgeSets G).mp hb
  have hTG : T ⊆ G.edgeFinset := hs.trans (edgesWithin_subset _ _)
  have hle := edgeGraph_le_of_subset G hTG
  have hclosed : ClosedOn T S := by
    intro u hu v huv
    exact ((mem_edgesWithin.mp (hs huv.1)).2 v (Sym2.mem_mk_right _ _))
  constructor
  · ext z
    rw [mem_unfoldWalkTree_iff_reachable G (edgeGraph T) r z hle]
    exact ⟨reachable_mem_of_closed hclosed hr, hc.2 r hr z⟩
  · rw [unfoldWalkTree_edges_eq G (edgeGraph T) hle ha r]
    · convert! edgeFinset_edgeGraph_of_subset G hTG
    · intro u v huv
      exact hc.2 r hr u ((mem_edgesWithin.mp (hs huv.1)).2 u (Sym2.mem_mk_left _ _))

omit H [DecidableRel H.Adj] in
/-- Rooted actual spanning trees (including their vertex blocks) have distinct codes. -/
theorem spanningTree_unfold_injective {S R : Finset V} {T Q : Finset (Sym2 V)}
    (hT : T ∈ spanningTreeSets G S) (hQ : Q ∈ spanningTreeSets G R)
    {r : V} (hrS : r ∈ S) (hrR : r ∈ R)
    (heq : unfoldWalkTree G (edgeGraph T) (Fintype.card V) none r =
      unfoldWalkTree G (edgeGraph Q) (Fintype.card V) none r) :
    S = R ∧ T = Q := by
  have ht := spanningTree_unfold_recovers G hT hrS
  have hq := spanningTree_unfold_recovers G hQ hrR
  constructor
  · exact ht.1.symm.trans ((congrArg (walkTreeVertices G) heq).trans hq.1)
  · exact ht.2.symm.trans ((congrArg (walkTreeEdges G) heq).trans hq.2)

end GridGen.Polymer
