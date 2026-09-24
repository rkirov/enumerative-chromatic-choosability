import GridGen.PolymerGraphCharge
import GridGen.PolymerComparison

/-! # Identifying the two-vertex derivative terms with actual graph edges -/

namespace GridGen.Polymer

open SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def graphActivityDeriv (L : ListAssignment V) (k : ℕ) (x : ℝ)
    (S : Finset V) : ℝ := -blockCoefficient G S * listDeficiency L k S * x ^ S.card

theorem hasDerivAt_graphActivity (L : ListAssignment V) (k : ℕ) (x t : ℝ) (S : Finset V) :
    HasDerivAt (graphActivity G L k x S) (graphActivityDeriv G L k x S) t := by
  unfold graphActivity graphActivityDeriv
  convert! (((hasDerivAt_const t (k : ℝ)).sub
    ((hasDerivAt_id t).mul_const (listDeficiency L k S))).const_mul
      (blockCoefficient G S)).mul_const (x ^ S.card) using 1
  try simp

theorem edgesWithin_pair_of_not_adj {u v : V} (huv : ¬G.Adj u v) :
    edgesWithin G.edgeFinset {u, v} = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨heG, hs⟩ := mem_edgesWithin.mp he
  induction e using Sym2.inductionOn with
  | hf a b =>
    have hab : G.Adj a b := G.mem_edgeFinset.mp heG
    have ha := hs a (Sym2.mem_mk_left _ _)
    have hb := hs b (Sym2.mem_mk_right _ _)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact hab.ne rfl
    · exact huv hab
    · exact huv hab.symm
    · exact hab.ne rfl

theorem blockCoefficient_pair_of_not_adj {u v : V} (hne : u ≠ v) (huv : ¬G.Adj u v) :
    blockCoefficient G {u, v} = 0 := by
  have hb : blockEdgeSets G {u, v} = ∅ := by
    classical
    simp [blockEdgeSets, edgesWithin_pair_of_not_adj G huv, not_connectedOn_empty_pair hne]
  simp [blockCoefficient, hb]

theorem graphActivityDeriv_singleton {L : ListAssignment V} {k : ℕ}
    (hL : IsNListAssignment L k) (x : ℝ) (v : V) :
    graphActivityDeriv G L k x {v} = 0 := by
  simp [graphActivityDeriv, listDeficiency_singleton hL]

theorem graphActivityDeriv_edge {L : ListAssignment V} {k : ℕ}
    (hL : IsNListAssignment L k) (x : ℝ) {e : Sym2 V} (he : e ∈ G.edgeFinset) :
    graphActivityDeriv G L k x e.toFinset = (edgeDef L k e : ℝ) * x ^ 2 := by
  induction e using Sym2.inductionOn with
  | hf u v =>
    have huv : G.Adj u v := G.mem_edgeFinset.mp he
    have hi : listInter L {u, v} = L u ∩ L v := by
      rw [listInter_insert L (Finset.singleton_nonempty v), listInter_singleton,
        Finset.inter_comm]
    have hc : (L u ∩ L v).card ≤ k := (Finset.card_le_card Finset.inter_subset_left).trans
      (by rw [hL u])
    simp [graphActivityDeriv, Sym2.toFinset_mk_eq, blockCoefficient_pair_of_adj G huv,
      listDeficiency, hi, edgeDef_mk, Nat.cast_sub hc, Finset.card_pair huv.ne]

omit G [Fintype V] [DecidableRel G.Adj] in
theorem sym2_toFinset_injective : Function.Injective (@Sym2.toFinset V _) := by
  intro e f he
  apply Sym2.ext
  intro v
  rw [← Sym2.mem_toFinset, ← Sym2.mem_toFinset, he]

theorem edge_toFinset_mem_small {U : Finset V} {e : Sym2 V}
    (he : e ∈ edgesWithin G.edgeFinset U) :
    e.toFinset ∈ (blocks U).filter (fun S => S.card ≤ 2) := by
  obtain ⟨heG, heU⟩ := mem_edgesWithin.mp he
  apply Finset.mem_filter.mpr
  refine ⟨?_, (Sym2.card_toFinset_of_not_isDiag e (G.not_isDiag_of_mem_edgeFinset heG)).le⟩
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_powerset.mpr (fun v hv => heU v (Sym2.mem_toFinset.mp hv)),
    Finset.nonempty_iff_ne_empty.mpr e.toFinset_ne_empty⟩

theorem small_nonanchor_derivative_zero {L : ListAssignment V} {k : ℕ}
    (hL : IsNListAssignment L k) (x : ℝ) {U S : Finset V}
    (hS : S ∈ (blocks U).filter (fun S => S.card ≤ 2))
    (hn : S ∉ (edgesWithin G.edgeFinset U).image Sym2.toFinset) :
    graphActivityDeriv G L k x S = 0 := by
  obtain ⟨hS, hcard⟩ := Finset.mem_filter.mp hS
  obtain ⟨hSU, hne⟩ := Finset.mem_filter.mp hS
  have hSU := Finset.mem_powerset.mp hSU
  by_cases hc : S.card = 1
  · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hc
    exact graphActivityDeriv_singleton G hL x v
  · have hc2 : S.card = 2 := by have := hne.card_pos; omega
    obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hc2
    have hna : ¬G.Adj u v := by
      intro ha
      apply hn
      apply Finset.mem_image.mpr
      refine ⟨s(u, v), ?_, Sym2.toFinset_mk_eq⟩
      apply mem_edgesWithin.mpr
      refine ⟨G.mem_edgeFinset.mpr ha, ?_⟩
      intro z hz
      exact hSU (by simpa [Sym2.mem_iff] using hz)
    simp [graphActivityDeriv, blockCoefficient_pair_of_not_adj G huv hna]

theorem small_derivative_sum_eq_edges {L : ListAssignment V} {k : ℕ}
    (hL : IsNListAssignment L k) (x : ℝ) (U : Finset V) (z : Finset V → ℝ) :
    (∑ S ∈ (blocks U).filter (fun S => S.card ≤ 2),
      graphActivityDeriv G L k x S * z (U \ S)) =
    ∑ e ∈ edgesWithin G.edgeFinset U, (edgeDef L k e : ℝ) * x ^ 2 * z (U \ e.toFinset) := by
  classical
  have hsub : (edgesWithin G.edgeFinset U).image Sym2.toFinset ⊆
      (blocks U).filter (fun S => S.card ≤ 2) := by
    intro S hS
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hS
    exact edge_toFinset_mem_small G he
  calc
    _ = ∑ S ∈ (edgesWithin G.edgeFinset U).image Sym2.toFinset,
        graphActivityDeriv G L k x S * z (U \ S) := by
      symm
      apply Finset.sum_subset hsub
      intro S hS hn
      rw [small_nonanchor_derivative_zero G hL x hS hn, zero_mul]
    _ = ∑ e ∈ edgesWithin G.edgeFinset U,
        graphActivityDeriv G L k x e.toFinset * z (U \ e.toFinset) :=
      Finset.sum_image (fun _ _ _ _ he => sym2_toFinset_injective he)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e he
      rw [graphActivityDeriv_edge G hL x (mem_edgesWithin.mp he).1]

omit G [Fintype V] [DecidableRel G.Adj] [DecidableEq V] in
theorem blocks_filter_large (U : Finset V) :
    (blocks U).filter (fun S => ¬S.card ≤ 2) = U.powerset.filter (fun S => 3 ≤ S.card) := by
  ext S
  simp only [blocks, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨⟨hSU, _⟩, hc⟩
    exact ⟨hSU, by omega⟩
  · rintro ⟨hSU, hc⟩
    exact ⟨⟨hSU, Finset.card_pos.mp (by omega)⟩, by omega⟩

end GridGen.Polymer
