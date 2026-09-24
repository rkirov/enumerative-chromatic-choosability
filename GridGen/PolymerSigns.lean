import GridGen.PolymerTreeEncoding

/-!
# Parity of the connected-block coefficients

Cancellation leaves spanning trees, all with exactly `|S| - 1` edges.
Consequently odd vertex blocks have nonnegative coefficients and even blocks
have nonpositive coefficients. These signs permit one-sided polymer budgets.
-/

namespace GridGen.Polymer

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem reachable_induce_of_closed {T : Finset (Sym2 V)} {S : Finset V}
    (hc : ClosedOn T S) {u v : V} (hu : u ∈ S) (hv : v ∈ S)
    (h : (edgeGraph T).Reachable u v) :
    ((edgeGraph T).induce (S : Set V)).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact .rfl
  | cons hadj p ih =>
    have hw := hc _ hu _ hadj
    exact (show ((edgeGraph T).induce (S : Set V)).Adj ⟨_, hu⟩ ⟨_, hw⟩
      from hadj).reachable.trans (ih hw hv)

theorem spanningTree_card_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} {T : Finset (Sym2 V)} (hT : T ∈ spanningTreeSets G S) :
    T.card + 1 = S.card := by
  classical
  obtain ⟨hb, ha⟩ := (mem_spanningTreeSets G).mp hT
  obtain ⟨hsub, hn⟩ := (mem_blockEdgeSets G).mp hb
  have hsupp : (edgeGraph T).support ⊆ (S : Set V) := by
    rintro u ⟨v, huv⟩
    exact (mem_edgesWithin.mp (hsub huv.1)).2 u (Sym2.mem_mk_left _ _)
  have hc : ClosedOn T S := by
    intro u hu v huv
    exact hsupp huv.mem_support_right
  have hconn : ((edgeGraph T).induce (S : Set V)).Connected := by
    obtain ⟨v, hv⟩ := hn.1
    let : Nonempty (S : Set V) := ⟨⟨v, hv⟩⟩
    apply Connected.mk
    intro u v
    exact reachable_induce_of_closed hc u.2 v.2 (hn.2 u u.2 v v.2)
  have ht : ((edgeGraph T).induce (S : Set V)).IsTree := ⟨hconn, ha.induce _⟩
  have heq : (edgeGraph T).edgeFinset = T := by
    convert! edgeFinset_edgeGraph_of_subset G (hsub.trans (edgesWithin_subset _ _))
  have hh := ht.card_edgeFinset
  have hind : ((edgeGraph T).induce (S : Set V)).edgeFinset.card = T.card := by
    calc
      _ = (edgeGraph T).edgeFinset.card := by
        convert! card_edgeFinset_induce_of_support_subset hsupp
      _ = _ := congrArg Finset.card heq
  rw [hind] at hh
  simpa using hh

section Ordered

variable [LinearOrder (Sym2 V)]

local instance (priority := 2000) signsOrder : PartialOrder (Sym2 V) :=
  (inferInstance : LinearOrder (Sym2 V)).toPartialOrder

theorem blockCoefficient_sign_ordered (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) :
    0 ≤ (-1 : ℝ) ^ (S.card - 1) * blockCoefficient G S := by
  classical
  rw [blockCoefficient_eq_sum_inactive, Finset.mul_sum]
  apply Finset.sum_nonneg
  intro T hT
  have hc := spanningTree_card_edges G (inactive_subset_spanningTreeSets G S hT)
  have he : T.card = S.card - 1 := by omega
  rw [he]
  exact mul_self_nonneg _

end Ordered

theorem blockCoefficient_sign (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) :
    0 ≤ (-1 : ℝ) ^ (S.card - 1) * blockCoefficient G S := by
  classical
  let e := Fintype.equivFin (Sym2 V)
  let : LinearOrder (Sym2 V) := LinearOrder.lift' e e.injective
  exact blockCoefficient_sign_ordered G S

theorem blockCoefficient_nonneg_of_odd (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hS : Odd S.card) : 0 ≤ blockCoefficient G S := by
  have h := blockCoefficient_sign G S
  have he : Even (S.card - 1) := by
    obtain ⟨n, hn⟩ := hS
    exact ⟨n, by omega⟩
  simpa [he.neg_one_pow] using h

theorem blockCoefficient_nonpos_of_even (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hS : Even S.card) (hn : S.Nonempty) :
    blockCoefficient G S ≤ 0 := by
  have h := blockCoefficient_sign G S
  have he : Odd (S.card - 1) := by
    obtain ⟨n, hn'⟩ := hS
    have := hn.card_pos
    exact ⟨n - 1, by omega⟩
  simpa [he.neg_one_pow] using h

end GridGen.Polymer
