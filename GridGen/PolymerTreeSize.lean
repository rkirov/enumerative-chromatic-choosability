import GridGen.PolymerTreeEncoding

/-! # Unfolding a forest does not duplicate vertices -/

namespace GridGen.Polymer

open SimpleGraph
open scoped BigOperators

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]

/-- The represented root path avoids an adjacent predecessor. -/
theorem path_of_mem_unfoldWalkTree (hacyc : H.IsAcyclic)
    (h : ℕ) (p : Option V) (v : V) {z : V}
    (hz : z ∈ walkTreeVertices G (unfoldWalkTree G H h p v)) :
    ∃ q : H.Walk v z, q.IsPath ∧
      ∀ a, p = some a → H.Adj v a → a ∉ q.support := by
  induction h generalizing p v with
  | zero =>
    have : z = v := by simpa [walkTreeVertices] using hz
    subst z
    refine ⟨.nil, .nil, ?_⟩
    intro a _ ha
    simpa using ha.ne'
  | succ h ih =>
    rcases Finset.mem_insert.mp hz with hz | hz
    · subst z
      refine ⟨.nil, .nil, ?_⟩
      intro a _ ha
      simpa using ha.ne'
    · obtain ⟨w, _, hw⟩ := Finset.mem_biUnion.mp hz
      by_cases hadj : H.Adj v w.val
      · have hc : z ∈ walkTreeVertices G (unfoldWalkTree G H h (some v) w.val) := by
          simpa [unfoldWalkTree, hadj] using hw
        obtain ⟨q, hq, hp⟩ := ih _ _ hc
        have hv := hp v rfl hadj.symm
        have hpath : (q.cons hadj).IsPath := hq.cons hv
        refine ⟨q.cons hadj, hpath, ?_⟩
        intro a hpa hva ha
        have heq := hacyc.eq_snd_of_adj_start hpath hva ha
        rw [Walk.snd_cons] at heq
        exact (mem_childPorts G |>.mp w.property).2 ((congrArg some heq).symm.trans hpa.symm)
      · simp [unfoldWalkTree, hadj] at hw

theorem predecessor_not_mem_unfoldWalkTree (hacyc : H.IsAcyclic)
    (h : ℕ) {p v : V} (hp : H.Adj v p) :
    p ∉ walkTreeVertices G (unfoldWalkTree G H h (some p) v) := by
  intro hz
  obtain ⟨q, _, hq⟩ := path_of_mem_unfoldWalkTree G H hacyc h (some p) v hz
  exact hq p rfl hp q.end_mem_support

theorem unfoldWalkTree_branches_disjoint (hacyc : H.IsAcyclic) (h : ℕ)
    {v a b : V} (ha : H.Adj v a) (hb : H.Adj v b) (hab : a ≠ b) :
    Disjoint (walkTreeVertices G (unfoldWalkTree G H h (some v) a))
      (walkTreeVertices G (unfoldWalkTree G H h (some v) b)) := by
  apply Finset.disjoint_left.mpr
  intro z hza hzb
  obtain ⟨p, hp, hav⟩ := path_of_mem_unfoldWalkTree G H hacyc h (some v) a hza
  obtain ⟨q, hq, hbv⟩ := path_of_mem_unfoldWalkTree G H hacyc h (some v) b hzb
  have hpa : (p.cons ha).IsPath := hp.cons (hav v rfl ha.symm)
  have hqb : (q.cons hb).IsPath := hq.cons (hbv v rfl hb.symm)
  have heq : p.cons ha = q.cons hb :=
    Subtype.mk.inj (hacyc.subsingleton_path v z |>.elim ⟨_, hpa⟩ ⟨_, hqb⟩)
  have heq' := congrArg Walk.snd heq
  exact hab (by simpa only [Walk.snd_cons] using heq')

/-- In a forest, all represented vertices are distinct, so the code size is the number
of decoded vertices minus one. This holds at every finite depth. -/
theorem card_vertices_unfoldWalkTree (hacyc : H.IsAcyclic)
    (h : ℕ) (p : Option V) (v : V) :
    (walkTreeVertices G (unfoldWalkTree G H h p v)).card =
      walkTreeSize G (unfoldWalkTree G H h p v) + 1 := by
  induction h generalizing p v with
  | zero => simp [walkTreeVertices, walkTreeSize]
  | succ h ih =>
    let f : childPorts G p v → Finset V := fun w =>
      if H.Adj v w.val then walkTreeVertices G (unfoldWalkTree G H h (some v) w.val)
        else ∅
    have hvertices : walkTreeVertices G (unfoldWalkTree G H (h + 1) p v) =
        insert v (Finset.univ.biUnion f) := by
      simp only [walkTreeVertices, unfoldWalkTree]
      congr 1
      apply Finset.biUnion_congr rfl
      intro w _
      dsimp [f]
      split <;> rfl
    have hn : v ∉ Finset.univ.biUnion f := by
      intro hv
      obtain ⟨w, _, hw⟩ := Finset.mem_biUnion.mp hv
      by_cases hadj : H.Adj v w.val
      · exact predecessor_not_mem_unfoldWalkTree G H hacyc h hadj.symm
          (by simpa [f, hadj] using hw)
      · simp [f, hadj] at hw
    have hd : ((Finset.univ : Finset (childPorts G p v)) : Set (childPorts G p v)).PairwiseDisjoint f := by
      intro a _ b _ hab
      change Disjoint (f a) (f b)
      by_cases ha : H.Adj v a.val <;> by_cases hb : H.Adj v b.val
      · simpa [f, ha, hb] using unfoldWalkTree_branches_disjoint G H hacyc h ha hb
          (fun heq => hab (Subtype.ext heq))
      · simp [f, ha, hb]
      · simp [f, ha, hb]
      · simp [f, ha, hb]
    rw [hvertices, Finset.card_insert_of_notMem hn, Finset.card_biUnion hd]
    change (∑ w, (f w).card) + 1 =
      (∑ w, (unfoldWalkTree G H (h + 1) p v w).elim 0
        (fun t => 1 + walkTreeSize G t)) + 1
    congr 1
    apply Finset.sum_congr rfl
    intro w _
    by_cases hadj : H.Adj v w.val
    · simp [f, unfoldWalkTree, hadj, ih, Nat.add_comm]
    · simp [f, unfoldWalkTree, hadj]

omit H [DecidableRel H.Adj] in
theorem spanningTree_unfold_size {S : Finset V} {T : Finset (Sym2 V)}
    (hT : T ∈ spanningTreeSets G S) {r : V} (hr : r ∈ S) :
    walkTreeSize G (unfoldWalkTree G (edgeGraph T) (Fintype.card V) none r) =
      S.card - 1 := by
  have hc := card_vertices_unfoldWalkTree G (edgeGraph T)
    ((mem_spanningTreeSets G).mp hT).2 (Fintype.card V) none r
  rw [(spanningTree_unfold_recovers G hT hr).1] at hc
  omega

end GridGen.Polymer
