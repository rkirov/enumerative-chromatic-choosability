import GridGen.PolymerBlockEdges
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Max

/-!
# Ordered-edge cancellation for connected coefficients

An active edge has its endpoints already connected by smaller selected edges. Toggling it
preserves connectivity. Choosing the least active edge gives the sign-reversing pairing.
-/

namespace GridGen.Polymer

open Finset SimpleGraph

-- Use the chosen total order of edges, not Sym2's built-in endpoint-inclusion order.
variable {V : Type*} [DecidableEq V] [LinearOrder (Sym2 V)]

local instance (priority := 2000) edgeOrder : PartialOrder (Sym2 V) :=
  (inferInstance : LinearOrder (Sym2 V)).toPartialOrder

def lowerEdges (T : Finset (Sym2 V)) (e : Sym2 V) : Finset (Sym2 V) :=
  T.filter (· < e)

def Active (T : Finset (Sym2 V)) (e : Sym2 V) : Prop :=
  ∀ u v, e = s(u, v) → (edgeGraph (lowerEdges T e)).Reachable u v

omit [DecidableEq V] in
theorem active_mk {T : Finset (Sym2 V)} {u v : V} :
    Active T s(u, v) ↔ (edgeGraph (lowerEdges T s(u, v))).Reachable u v := by
  constructor
  · exact fun h => h u v rfl
  · intro h x y he
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h
    · exact h.symm

def toggleEdge (T : Finset (Sym2 V)) (e : Sym2 V) : Finset (Sym2 V) :=
  if e ∈ T then T.erase e else insert e T

omit [LinearOrder (Sym2 V)] in
@[simp] theorem mem_toggleEdge {T : Finset (Sym2 V)} {e f : Sym2 V} :
    f ∈ toggleEdge T e ↔ if f = e then e ∉ T else f ∈ T := by
  by_cases he : e ∈ T <;> by_cases hf : f = e <;> simp [toggleEdge, he, hf]

omit [LinearOrder (Sym2 V)] in
@[simp] theorem toggleEdge_twice (T : Finset (Sym2 V)) (e : Sym2 V) :
    toggleEdge (toggleEdge T e) e = T := by
  ext f
  by_cases h : f = e <;> simp [mem_toggleEdge, h]

omit [LinearOrder (Sym2 V)] in
theorem toggleEdge_ne (T : Finset (Sym2 V)) (e : Sym2 V) : toggleEdge T e ≠ T := by
  intro h
  have := congrArg (fun A => e ∈ A) h
  simp at this

theorem lowerEdges_toggle_of_le (T : Finset (Sym2 V)) {e f : Sym2 V} (h : f ≤ e) :
    lowerEdges (toggleEdge T e) f = lowerEdges T f := by
  ext x
  by_cases hx : x = e
  · subst x
    simp [lowerEdges, not_lt_of_ge h]
  · simp [lowerEdges, hx]

theorem active_toggle_of_le (T : Finset (Sym2 V)) {e f : Sym2 V} (h : f ≤ e) :
    Active (toggleEdge T e) f ↔ Active T f := by
  unfold Active
  rw [lowerEdges_toggle_of_le T h]

theorem lowerEdges_subset_toggle (T : Finset (Sym2 V)) (e : Sym2 V) :
    lowerEdges T e ⊆ toggleEdge T e := by
  intro f hf
  obtain ⟨hfT, hfe⟩ := Finset.mem_filter.mp hf
  simpa [ne_of_lt hfe] using hfT

omit [DecidableEq V] [LinearOrder (Sym2 V)] in
theorem reachable_of_adj_reachable {H K : SimpleGraph V}
    (h : ∀ u v, H.Adj u v → K.Reachable u v) {u v : V}
    (hr : H.Reachable u v) : K.Reachable u v := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => exact .rfl
  | cons hadj p ih => exact (h _ _ hadj).trans ih

theorem reachable_toggle_of_active {T : Finset (Sym2 V)} {e : Sym2 V} (he : Active T e)
    {u v : V} (h : (edgeGraph T).Reachable u v) :
    (edgeGraph (toggleEdge T e)).Reachable u v := by
  apply reachable_of_adj_reachable (H := edgeGraph T) _ h
  intro x y hxy
  by_cases hxe : s(x, y) = e
  · apply (he x y hxe.symm).mono
    intro a b hab
    rw [fromEdgeSet_adj] at hab ⊢
    exact ⟨lowerEdges_subset_toggle T e hab.1, hab.2⟩
  · apply Adj.reachable
    rw [fromEdgeSet_adj] at hxy ⊢
    exact ⟨by simpa [hxe] using hxy.1, hxy.2⟩

theorem connectedOn_toggle_iff {T : Finset (Sym2 V)} {e : Sym2 V} {S : Finset V}
    (he : Active T e) : ConnectedOn (toggleEdge T e) S ↔ ConnectedOn T S := by
  have ht : Active (toggleEdge T e) e := (active_toggle_of_le T le_rfl).mpr he
  constructor
  · rintro ⟨hS, hconn⟩
    refine ⟨hS, fun u hu v hv => ?_⟩
    simpa using reachable_toggle_of_active ht (hconn u hu v hv)
  · rintro ⟨hS, hconn⟩
    exact ⟨hS, fun u hu v hv => reachable_toggle_of_active he (hconn u hu v hv)⟩

omit [LinearOrder (Sym2 V)] in
theorem sign_toggleEdge (T : Finset (Sym2 V)) (e : Sym2 V) :
    (-1 : ℝ) ^ T.card + (-1 : ℝ) ^ (toggleEdge T e).card = 0 := by
  by_cases he : e ∈ T
  · rw [toggleEdge, if_pos he]
    conv_lhs => lhs; rw [← Finset.card_erase_add_one he, pow_succ]
    ring
  · rw [toggleEdge, if_neg he, Finset.card_insert_of_notMem he, pow_succ]
    ring


omit [DecidableEq V] in
theorem active_mono {T R : Finset (Sym2 V)} (hTR : T ⊆ R) {e : Sym2 V}
    (he : Active T e) : Active R e := by
  intro u v huv
  apply (he u v huv).mono
  intro a b hab
  rw [fromEdgeSet_adj] at hab ⊢
  exact ⟨Finset.mem_filter.mpr
    ⟨hTR (Finset.mem_filter.mp hab.1).1, (Finset.mem_filter.mp hab.1).2⟩, hab.2⟩

/-- A selected edge set without active edges is a forest: insert its edges in increasing
order, so each new edge joins different components. -/
theorem isAcyclic_of_no_active (T : Finset (Sym2 V))
    (hn : ∀ e ∈ T, ¬Active T e) : (edgeGraph T).IsAcyclic := by
  classical
  induction T using Finset.strongInductionOn with
  | _ T ih =>
    by_cases hT : T = ∅
    · subst T
      simp [edgeGraph]
    obtain ⟨e, he, hmax⟩ := T.exists_max_image id (Finset.nonempty_iff_ne_empty.mpr hT)
    have hsmall : lowerEdges T e = T.erase e := by
      ext f
      simp only [lowerEdges, Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hf, hfe⟩
        exact ⟨ne_of_lt hfe, hf⟩
      · rintro ⟨hne, hf⟩
        exact ⟨hf, lt_of_le_of_ne (hmax f hf) hne⟩
    have hac := ih (T.erase e) (Finset.erase_ssubset he) (by
      intro f hf hactive
      exact hn f (Finset.mem_of_mem_erase hf)
        (active_mono (Finset.erase_subset _ _) hactive))
    have hne := hn e he
    induction e using Sym2.ind with
    | _ u v =>
      have hnr : ¬(edgeGraph (T.erase s(u, v))).Reachable u v := by
        rwa [active_mk, hsmall] at hne
      have h := hac.sup_edge_of_not_reachable hnr
      have heq : edgeGraph T = edgeGraph (T.erase s(u, v)) ⊔ SimpleGraph.edge u v := by
        change fromEdgeSet _ = fromEdgeSet _ ⊔ fromEdgeSet _
        rw [← SimpleGraph.fromEdgeSet_union]
        congr 1
        ext f
        simp only [Set.mem_union, Finset.mem_coe, Set.mem_singleton_iff, Finset.mem_erase]
        constructor
        · intro hf
          by_cases hfe : f = s(u, v)
          · exact Or.inr hfe
          · exact Or.inl ⟨hfe, hf⟩
        · rintro (⟨_, hf⟩ | rfl)
          · exact hf
          · exact he
      rwa [heq]


noncomputable def activeEdges (E T : Finset (Sym2 V)) : Finset (Sym2 V) := by
  classical
  exact E.filter (Active T)

omit [DecidableEq V] in
theorem activeEdges_min_mem (E T : Finset (Sym2 V)) (h : (activeEdges E T).Nonempty) :
    (activeEdges E T).min' h ∈ E ∧ Active T ((activeEdges E T).min' h) := by
  classical
  exact Finset.mem_filter.mp ((activeEdges E T).min'_mem h)

theorem activeEdges_toggle_nonempty (E T : Finset (Sym2 V))
    (h : (activeEdges E T).Nonempty) :
    (activeEdges E (toggleEdge T ((activeEdges E T).min' h))).Nonempty := by
  classical
  refine ⟨(activeEdges E T).min' h, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
  · exact (activeEdges_min_mem E T h).1
  · exact (active_toggle_of_le T le_rfl).mpr (activeEdges_min_mem E T h).2

/-- The least active edge is unchanged by toggling it. Smaller candidates see exactly
the same lower-edge subgraph before and after the toggle. -/
theorem activeEdges_min_toggle (E T : Finset (Sym2 V))
    (h : (activeEdges E T).Nonempty) :
    (activeEdges E (toggleEdge T ((activeEdges E T).min' h))).min'
      (activeEdges_toggle_nonempty E T h) = (activeEdges E T).min' h := by
  classical
  apply (Finset.min'_eq_iff _ _ _).mpr
  constructor
  · exact Finset.mem_filter.mpr ⟨(activeEdges_min_mem E T h).1,
      (active_toggle_of_le T le_rfl).mpr (activeEdges_min_mem E T h).2⟩
  · intro f hf
    by_contra hle
    have hlt := lt_of_not_ge hle
    have hf' : f ∈ activeEdges E T := by
      have hf := Finset.mem_filter.mp hf
      exact Finset.mem_filter.mpr
        ⟨hf.1, (active_toggle_of_le T hlt.le).mp hf.2⟩
    exact (not_lt_of_ge ((activeEdges E T).min'_le f hf')) hlt

omit [LinearOrder (Sym2 V)] in
theorem toggleEdge_subset {E T : Finset (Sym2 V)} {e : Sym2 V}
    (hT : T ⊆ E) (he : e ∈ E) : toggleEdge T e ⊆ E := by
  intro f hf
  by_cases hfe : f = e
  · simpa [hfe] using he
  · exact hT (by simpa [hfe] using hf)

variable [Fintype V]

/-- Cancellation of all connected spanning edge sets that have an active edge. -/
theorem sum_active_blockEdgeSets_eq_zero (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) :
    (∑ T ∈ (blockEdgeSets G S).filter
      (fun T => (activeEdges (edgesWithin G.edgeFinset S) T).Nonempty),
      (-1 : ℝ) ^ T.card) = 0 := by
  classical
  let E := edgesWithin G.edgeFinset S
  let bad := (blockEdgeSets G S).filter (fun T => (activeEdges E T).Nonempty)
  have hb : ∀ T ∈ bad, (activeEdges E T).Nonempty :=
    fun T hT => (Finset.mem_filter.mp hT).2
  let flip := fun T (hT : T ∈ bad) => toggleEdge T ((activeEdges E T).min' (hb T hT))
  have hmem : ∀ T (hT : T ∈ bad), flip T hT ∈ bad := by
    intro T hT
    obtain ⟨hTblocks, _⟩ := Finset.mem_filter.mp hT
    obtain ⟨hTE, hconn⟩ := (mem_blockEdgeSets G).mp hTblocks
    apply Finset.mem_filter.mpr
    refine ⟨(mem_blockEdgeSets G).mpr ⟨?_, ?_⟩, activeEdges_toggle_nonempty E T (hb T hT)⟩
    · exact toggleEdge_subset hTE (activeEdges_min_mem E T (hb T hT)).1
    · exact (connectedOn_toggle_iff (activeEdges_min_mem E T (hb T hT)).2).mpr hconn
  change (∑ T ∈ bad, (-1 : ℝ) ^ T.card) = 0
  refine Finset.sum_involution flip ?_ ?_ hmem ?_
  · intro T hT
    exact sign_toggleEdge T _
  · intro T hT _
    exact toggleEdge_ne T _
  · intro T hT
    change toggleEdge (toggleEdge T ((activeEdges E T).min' (hb T hT)))
      ((activeEdges E (toggleEdge T ((activeEdges E T).min' (hb T hT)))).min' _) = T
    rw [activeEdges_min_toggle E T (hb T hT), toggleEdge_twice]

end GridGen.Polymer
