import GridGen.PolymerBlockEdges

/-! Exact connected-block coefficients on single vertices and pairs of vertices. -/

namespace GridGen.Polymer

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

@[simp] theorem edgesWithin_singleton (v : V) : edgesWithin G.edgeFinset {v} = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨heG, heV⟩ := mem_edgesWithin.mp he
  induction e using Sym2.ind with
  | _ x y =>
    have hx : x = v := Finset.mem_singleton.mp (heV x (Sym2.mem_mk_left _ _))
    have hy : y = v := Finset.mem_singleton.mp (heV y (Sym2.mem_mk_right _ _))
    subst x; subst y
    exact G.not_isDiag_of_mem_edgeFinset heG (by simp)

@[simp] theorem blockEdgeSets_singleton (v : V) : blockEdgeSets G {v} = {∅} := by
  classical
  ext T
  simp [blockEdgeSets, ConnectedOn]

@[simp] theorem blockCoefficient_singleton (v : V) : blockCoefficient G {v} = 1 := by
  simp [blockCoefficient]

theorem edgesWithin_pair_of_adj {u v : V} (huv : G.Adj u v) :
    edgesWithin G.edgeFinset {u, v} = {s(u, v)} := by
  ext e
  rw [mem_edgesWithin, Finset.mem_singleton]
  constructor
  · rintro ⟨heG, heV⟩
    induction e using Sym2.ind with
    | _ x y =>
      have hx := heV x (Sym2.mem_mk_left _ _)
      have hy := heV y (Sym2.mem_mk_right _ _)
      have hxy : G.Adj x y := G.mem_edgeFinset.mp heG
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact (hxy.ne rfl).elim
      · rfl
      · exact Sym2.eq_swap
      · exact (hxy.ne rfl).elim
  · rintro rfl
    refine ⟨G.mem_edgeFinset.mpr huv, ?_⟩
    intro x hx
    rcases Sym2.mem_iff.mp hx with rfl | rfl <;> simp

omit [Fintype V] in
theorem connectedOn_edge (u v : V) : ConnectedOn {s(u, v)} {u, v} := by
  refine ⟨by simp, ?_⟩
  intro x hx y hy
  have huv : (edgeGraph {s(u, v)}).Reachable u v := by
    by_cases h : u = v
    · subst v; exact .rfl
    · exact (show (edgeGraph {s(u, v)}).Adj u v from ⟨by simp, h⟩).reachable
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact .rfl
  · exact huv
  · exact huv.symm
  · exact .rfl

omit [Fintype V] in
theorem not_connectedOn_empty_pair {u v : V} (huv : u ≠ v) :
    ¬ ConnectedOn (∅ : Finset (Sym2 V)) {u, v} := by
  intro h
  apply huv
  apply eq_of_reachable_of_no_adj (H := edgeGraph (∅ : Finset (Sym2 V)))
    (by intro x y; simp [edgeGraph])
  exact h.2 u (by simp) v (by simp)

theorem blockEdgeSets_pair_of_adj {u v : V} (huv : G.Adj u v) :
    blockEdgeSets G {u, v} = {{s(u, v)}} := by
  classical
  rw [blockEdgeSets, edgesWithin_pair_of_adj G huv]
  ext T
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_singleton_iff,
    Finset.mem_singleton]
  constructor
  · rintro ⟨rfl | rfl, h⟩
    · exact (not_connectedOn_empty_pair huv.ne h).elim
    · rfl
  · rintro rfl
    exact ⟨Or.inr rfl, connectedOn_edge u v⟩

theorem blockCoefficient_pair_of_adj {u v : V} (huv : G.Adj u v) :
    blockCoefficient G {u, v} = -1 := by
  rw [blockCoefficient, blockEdgeSets_pair_of_adj G huv]
  simp

end GridGen.Polymer
