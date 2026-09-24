import GridGen.MaximumDegree

/-!
# Strict comparison and the equality case at the uniform threshold

The uniform proof leaves a fraction `1 - 2eo = 671/5000` of the positive edge derivative.
Retaining it proves strict inequality whenever two adjacent lists differ, and hence that on a
connected graph only the constant assignments attain `P(G,k)`. The argument is now the
generic `GridGen.Polymer.colConst_lt_col_of_certifiedAt` (`PolymerCertificate.lean`), so the
same conclusions hold at every certified threshold (`DegreeFourTwenty.lean`,
`SmallDegree.lean`); this file states them at `567 D ≤ 100 k`.

This is a refinement of this repository's degree bound, using the same interpolation and
charging method; strict comparison at a larger degree threshold also follows from Zhang–Dong,
arXiv:2609.08540v1, Theorem 5.
-/

namespace GridGen.Polymer

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- At the uniform degree threshold, any deficient edge forces strictly more list colorings. -/
theorem colConst_lt_col_of_degree_bound_of_edgeDef_pos {D : ℕ}
    (hdeg : ∀ v, G.degree v ≤ D)
    {L : ListAssignment V} {k : ℕ} (hL : IsNListAssignment L k)
    (hk : 567 * D ≤ 100 * k) (hk0 : 0 < k)
    {e : Sym2 V} (he : e ∈ G.edgeFinset) (hd : 0 < edgeDef L k e) :
    G.colConst k < G.col L :=
  colConst_lt_col_of_certifiedAt G hdeg (certifiedAt_uniform hk hk0) hL he hd

end GridGen.Polymer

namespace SimpleGraph

open GridGen.Polymer

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Adjacent unequal lists cannot minimize the count above the uniform degree threshold. -/
theorem colConst_lt_col_of_degree_bound_of_adj_lists_ne {D k : ℕ}
    (hdeg : ∀ v, G.degree v ≤ D) (hk : 567 * D ≤ 100 * k)
    {L : ListAssignment V} (hL : IsNListAssignment L k)
    {u v : V} (huv : G.Adj u v) (hne : L u ≠ L v) : G.colConst k < G.col L := by
  have hk0 : 0 < k := by
    by_contra h0
    have hu := hL u
    have hv := hL v
    exact hne ((Finset.card_eq_zero.mp (by omega)).trans (Finset.card_eq_zero.mp (by omega)).symm)
  exact colConst_lt_col_of_certifiedAt_of_adj G hdeg (certifiedAt_uniform hk hk0) hL huv hne

/-- For a connected graph at the uniform threshold, precisely the constant assignments
attain the ordinary coloring count. The palette may be any set of `k` colors. -/
theorem col_eq_colConst_iff_constant_of_degree_bound {D k : ℕ}
    (hdeg : ∀ v, G.degree v ≤ D) (hk : 567 * D ≤ 100 * k)
    (hG : G.Connected) {L : ListAssignment V} (hL : IsNListAssignment L k) :
    G.col L = G.colConst k ↔ ∃ s : Finset ℕ, ∀ v, L v = s := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · have hs : ∀ v, L v = ∅ := fun v => Finset.card_eq_zero.mp (hL v)
    have heq : L = fun _ => ∅ := funext hs
    exact ⟨fun _ => ⟨∅, hs⟩, fun _ => by rw [heq]; exact col_const_eq_colConst (G := G) rfl⟩
  · exact col_eq_colConst_iff_of_certifiedAt G hdeg (certifiedAt_uniform hk hk0) hG hL

end SimpleGraph
