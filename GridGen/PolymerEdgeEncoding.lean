import GridGen.PolymerTreeSize

/-! # Encoding a tree with a distinguished edge as two branches -/

namespace GridGen.Polymer

open SimpleGraph
open scoped BigOperators

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]

abbrev EdgeWalkTreeCode (h : ℕ) (u v : V) :=
  WalkTreeCode G h (some v) u × WalkTreeCode G h (some u) v

noncomputable def unfoldEdgeTree (h : ℕ) (u v : V) : EdgeWalkTreeCode G h u v :=
  (unfoldWalkTree G H h (some v) u, unfoldWalkTree G H h (some u) v)

noncomputable def edgeCodeVertices {h : ℕ} {u v : V} (c : EdgeWalkTreeCode G h u v) :
    Finset V := walkTreeVertices G c.1 ∪ walkTreeVertices G c.2

noncomputable def edgeCodeEdges {h : ℕ} {u v : V} (c : EdgeWalkTreeCode G h u v) :
    Finset (Sym2 V) := insert s(u, v) (walkTreeEdges G c.1 ∪ walkTreeEdges G c.2)

theorem path_mem_unfoldEdgeTree (hHG : H ≤ G) (hacyc : H.IsAcyclic)
    {u v z : V} (huv : H.Adj u v) (q : H.Walk u z) (hq : q.IsPath) :
    z ∈ edgeCodeVertices G (unfoldEdgeTree G H (Fintype.card V) u v) ∧
      ∀ e ∈ q.edges, e ∈ edgeCodeEdges G (unfoldEdgeTree G H (Fintype.card V) u v) := by
  by_cases hv : v ∈ q.support
  · cases q with
    | nil => simp at hv; exact (huv.ne hv.symm).elim
    | @cons u w z huw q =>
      have heq := hacyc.eq_snd_of_adj_start hq huv hv
      rw [Walk.snd_cons] at heq
      subst w
      have hh := (Walk.cons_isPath_iff huw q).mp hq
      have hp := path_mem_unfoldWalkTree G H hHG q hh.1 (Fintype.card V)
        hh.1.length_lt.le (some u) (by
          intro a ha
          have : u = a := Option.some.inj ha
          subst a
          exact hh.2)
      refine ⟨Finset.mem_union_right _ hp.1, ?_⟩
      intro e he
      rcases List.mem_cons.mp he with he | he
      · exact Finset.mem_insert.mpr (Or.inl he)
      · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (hp.2 e he))
  · have hp := path_mem_unfoldWalkTree G H hHG q hq (Fintype.card V)
      hq.length_lt.le (some v) (by
        intro a ha
        have : v = a := Option.some.inj ha
        subst a
        exact hv)
    exact ⟨Finset.mem_union_left _ hp.1, fun e he =>
      Finset.mem_insert_of_mem (Finset.mem_union_left _ (hp.2 e he))⟩

theorem opposite_unfold_branches_disjoint (hacyc : H.IsAcyclic) (h : ℕ)
    {u v : V} (huv : H.Adj u v) :
    Disjoint (walkTreeVertices G (unfoldWalkTree G H h (some v) u))
      (walkTreeVertices G (unfoldWalkTree G H h (some u) v)) := by
  apply Finset.disjoint_left.mpr
  intro z hz₁ hz₂
  obtain ⟨p, hp, hv⟩ := path_of_mem_unfoldWalkTree G H hacyc h (some v) u hz₁
  obtain ⟨q, hq, hu⟩ := path_of_mem_unfoldWalkTree G H hacyc h (some u) v hz₂
  have hq' : (q.cons huv).IsPath := hq.cons (hu u rfl huv.symm)
  have heq : p = q.cons huv :=
    Subtype.mk.inj (hacyc.subsingleton_path u z |>.elim ⟨_, hp⟩ ⟨_, hq'⟩)
  apply hv v rfl huv
  rw [heq]
  simp

theorem unfoldEdgeTree_edges_subset (h : ℕ) {u v : V} (huv : H.Adj u v) :
    edgeCodeEdges G (unfoldEdgeTree G H h u v) ⊆ H.edgeFinset := by
  apply Finset.insert_subset (H.mem_edgeFinset.mpr huv)
  exact Finset.union_subset (unfoldWalkTree_edges_subset G H _ _ _)
    (unfoldWalkTree_edges_subset G H _ _ _)

theorem unfoldEdgeTree_edges_eq (hHG : H ≤ G) (hacyc : H.IsAcyclic)
    {u v : V} (huv : H.Adj u v)
    (hr : ∀ a b, H.Adj a b → H.Reachable u a) :
    edgeCodeEdges G (unfoldEdgeTree G H (Fintype.card V) u v) = H.edgeFinset := by
  apply Finset.Subset.antisymm (unfoldEdgeTree_edges_subset G H _ huv)
  intro e he
  induction e using Sym2.inductionOn with
  | hf a b =>
    have hab : H.Adj a b := H.mem_edgeFinset.mp he
    let p := (hr a b hab).some.toPath
    let q := (hr b a hab.symm).some.toPath
    have hp := (path_mem_unfoldEdgeTree G H hHG hacyc huv p.val p.property).2
    have hq := (path_mem_unfoldEdgeTree G H hHG hacyc huv q.val q.property).2
    by_cases hm : a ∈ q.val.support
    · apply hq
      rw [hacyc.path_concat p.property q.property hab hm, Walk.edges_concat]
      simp
    · have hb := hacyc.mem_support_of_ne_mem_support_of_adj_of_isPath
        p.property q.property hab hm
      apply hp
      rw [hacyc.path_concat q.property p.property hab.symm hb, Walk.edges_concat]
      simp [Sym2.eq_swap]

omit H [DecidableRel H.Adj] in
theorem spanningTree_edge_unfold_recovers {S : Finset V} {T : Finset (Sym2 V)}
    (hT : T ∈ spanningTreeSets G S) {u v : V} (he : s(u, v) ∈ T) :
    edgeCodeVertices G (unfoldEdgeTree G (edgeGraph T) (Fintype.card V) u v) = S ∧
    edgeCodeEdges G (unfoldEdgeTree G (edgeGraph T) (Fintype.card V) u v) = T := by
  obtain ⟨hb, ha⟩ := (mem_spanningTreeSets G).mp hT
  obtain ⟨hs, hc⟩ := (mem_blockEdgeSets G).mp hb
  have hTG : T ⊆ G.edgeFinset := hs.trans (edgesWithin_subset _ _)
  have hle := edgeGraph_le_of_subset G hTG
  have huv : (edgeGraph T).Adj u v := ⟨he, (G.mem_edgeFinset.mp (hTG he)).ne⟩
  have hu := (mem_edgesWithin.mp (hs he)).2 u (Sym2.mem_mk_left _ _)
  have hv := (mem_edgesWithin.mp (hs he)).2 v (Sym2.mem_mk_right _ _)
  have hclosed : ClosedOn T S := by
    intro a ha b hab
    exact (mem_edgesWithin.mp (hs hab.1)).2 b (Sym2.mem_mk_right _ _)
  constructor
  · ext z
    constructor
    · intro hz
      rcases Finset.mem_union.mp hz with hz | hz
      · exact reachable_mem_of_closed hclosed hu
          (reachable_of_mem_unfoldWalkTree G (edgeGraph T) _ _ _ hz)
      · exact reachable_mem_of_closed hclosed hv
          (reachable_of_mem_unfoldWalkTree G (edgeGraph T) _ _ _ hz)
    · intro hz
      let q := (hc.2 u hu z hz).some.toPath
      exact (path_mem_unfoldEdgeTree G (edgeGraph T) hle ha huv q.val q.property).1
  · rw [unfoldEdgeTree_edges_eq G (edgeGraph T) hle ha huv]
    · convert! edgeFinset_edgeGraph_of_subset G hTG
    · intro a b hab
      exact hc.2 u hu a ((mem_edgesWithin.mp (hs hab.1)).2 a (Sym2.mem_mk_left _ _))

omit H [DecidableRel H.Adj] in
theorem spanningTree_edge_unfold_size {S : Finset V} {T : Finset (Sym2 V)}
    (hT : T ∈ spanningTreeSets G S) {u v : V} (he : s(u, v) ∈ T) :
    walkTreeSize G (unfoldEdgeTree G (edgeGraph T) (Fintype.card V) u v).1 +
      walkTreeSize G (unfoldEdgeTree G (edgeGraph T) (Fintype.card V) u v).2 =
        S.card - 2 := by
  have ha := ((mem_spanningTreeSets G).mp hT).2
  have hs := ((mem_blockEdgeSets G).mp ((mem_spanningTreeSets G).mp hT).1).1
  have huv : (edgeGraph T).Adj u v :=
    ⟨he, (G.mem_edgeFinset.mp ((edgesWithin_subset _ _) (hs he))).ne⟩
  have hc := congrArg Finset.card (spanningTree_edge_unfold_recovers G hT he).1
  change (walkTreeVertices G (unfoldWalkTree G (edgeGraph T) _ (some v) u) ∪
    walkTreeVertices G (unfoldWalkTree G (edgeGraph T) _ (some u) v)).card = S.card at hc
  rw [Finset.card_union_of_disjoint (opposite_unfold_branches_disjoint G (edgeGraph T) ha _ huv),
    card_vertices_unfoldWalkTree G (edgeGraph T) ha,
    card_vertices_unfoldWalkTree G (edgeGraph T) ha] at hc
  dsimp [unfoldEdgeTree]
  omega

omit H [DecidableRel H.Adj] in
theorem spanningTree_edge_unfold_injective {S R : Finset V} {T Q : Finset (Sym2 V)}
    (hT : T ∈ spanningTreeSets G S) (hQ : Q ∈ spanningTreeSets G R)
    {u v : V} (heT : s(u, v) ∈ T) (heQ : s(u, v) ∈ Q)
    (heq : unfoldEdgeTree G (edgeGraph T) (Fintype.card V) u v =
      unfoldEdgeTree G (edgeGraph Q) (Fintype.card V) u v) : S = R ∧ T = Q := by
  have ht := spanningTree_edge_unfold_recovers G hT heT
  have hq := spanningTree_edge_unfold_recovers G hQ heQ
  exact ⟨ht.1.symm.trans ((congrArg (edgeCodeVertices G) heq).trans hq.1),
    ht.2.symm.trans ((congrArg (edgeCodeEdges G) heq).trans hq.2)⟩

/-- Number of selected edges in an edge code, the anchor edge excluded. -/
noncomputable def edgeCodeSize {h : ℕ} {u v : V} (c : EdgeWalkTreeCode G h u v) : ℕ :=
  walkTreeSize G c.1 + walkTreeSize G c.2

theorem sum_edgeCode_weights (x : ℝ) (h : ℕ) (u v : V) :
    (∑ c : EdgeWalkTreeCode G h u v, x ^ edgeCodeSize G c) =
      walkTreeMass G x h (some v) u * walkTreeMass G x h (some u) v := by
  classical
  simp [edgeCodeSize, Fintype.sum_prod_type, pow_add, walkTreeMass,
    Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

end GridGen.Polymer
