/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.PolymerPeelRoot
import GridGen.PolymerParityMonotonicity
import GridGen.PolymerCertificate

/-!
# ECC from a degree-sensitive parity certificate

The polymer argument of `PolymerCertificate.lean` with the deletion ratio required only at vertices
of residual degree at most `D - 1` (`PolymerPeel.lean`). Every comparison the argument makes deletes
a connected block outward from a root or an anchor edge, and each such deletion step removes a
vertex that has already lost a neighbour (`PolymerPeelGraph.lean`). So:

* at a root of residual degree at most `D - 1`, the harmful mass is at most `k x o` — the branch
  odd mass, `PolymerPeelRoot.lean` — and the ratio needs `k x o ≤ k x - 1`;
* at a root of full degree only positivity is needed, which the root mass `r < 1` gives.

`CertifiedPeelAt D k` packages these, and `colConst_le_col_of_certifiedPeelAt` concludes ECC. The
instances are in `PeelDegree.lean` (degree four: `k ≥ 17`, improving `k ≥ 20`). The
argument is the one proposed by Codex (OpenAI) in `ai_research_notes/CODEX_GRID_ALL_HEIGHTS_2026-10-07.md`,
§3, without its neighbour-pair refinement to `k ≥ 16`.
-/

namespace GridGen.Polymer

open SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A block with a nonzero activity has a spanning connected edge set. -/
theorem blockEdgeSets_nonempty_of_penalty_ne {L : ListAssignment V} {k : ℕ} {x t : ℝ}
    {S : Finset V} (h : graphActivityPenalty G L k x S t ≠ 0) : (blockEdgeSets G S).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  apply h
  simp [graphActivityPenalty, graphActivity, blockCoefficient, hne]

/-- **Positivity everywhere and the deletion ratio at residual degree at most `D - 1`.** -/
theorem graphActivity_peel_positive {D : ℕ} (hdeg : ∀ v, G.degree v ≤ D)
    {x₀ e o r : ℝ} (hc : ParityCert D x₀ e o r) (hr : r < 1)
    {L : ListAssignment V} {k : ℕ} (hL : IsNListAssignment L k)
    {x : ℝ} (hx : 0 ≤ x) (hxx : x ≤ x₀) (hbudget : (k : ℝ) * x * o ≤ (k : ℝ) * x - 1)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (U : Finset V) :
    0 < partitionSum (fun S => graphActivity G L k x S t) U ∧
      ∀ u, u ∈ U → smallIn G (D - 1) U u →
        partitionSum (fun S => graphActivity G L k x S t) (U.erase u) ≤
          partitionSum (fun S => graphActivity G L k x S t) U := by
  have hkx : 1 ≤ (k : ℝ) * x := by nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg k) hx) hc.o_nonneg]
  apply partitionSum_positive_peel _
    (fun S => graphActivityPenalty G L k x S t) ((k : ℝ) * x) (smallIn G (D - 1))
  · intro v; rw [graphActivity_singleton G hL]
  · exact fun S => graphActivityPenalty_nonneg G L k _ S t
  · exact neg_graphActivityPenalty_le G hL hx ht
  · intro U v S hv hS hb
    obtain ⟨T, hT⟩ := blockEdgeSets_nonempty_of_penalty_ne G hb
    have hvS := (mem_rootedBlocks hS).2.1
    have := peelChain_of_mem_blockEdgeSets G hdeg hT U {v} (Finset.singleton_subset_iff.mpr hvS)
      (Finset.singleton_nonempty v)
    rwa [Finset.sdiff_singleton_eq_erase] at this
  · intro U v _
    have hroot := graphActivity_cert_root_bound G hdeg hc hL hx hxx ht U v
    have : (k : ℝ) * x * r < (k : ℝ) * x := by nlinarith
    linarith
  · intro U v hv hsmall
    exact (graphActivity_cert_root_bound_small G hdeg hc hL hx hxx ht U hv hsmall).trans hbudget

/-- **Peel monotonicity for charged blocks.** -/
theorem graphActivity_peel_charge_mono {D : ℕ} (hdeg : ∀ v, G.degree v ≤ D)
    {L : ListAssignment V} {k : ℕ} {x : ℝ} (z : Finset V → ℝ)
    (hz : ∀ C u, u ∈ C → smallIn G (D - 1) C u → z (C.erase u) ≤ z C)
    (U S : Finset V) (e : Sym2 V) (hc : graphTreeCharge G L k x S e ≠ 0) :
    z (U \ S) ≤ z (U \ e.toFinset) := by
  classical
  obtain ⟨T, hT⟩ : ((spanningTreeSets G S).filter (fun T => e ∈ T)).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    exact hc (by simp [graphTreeCharge, hne])
  obtain ⟨hTS, heT⟩ := Finset.mem_filter.mp hT
  have hTb := ((mem_spanningTreeSets G).mp hTS).1
  have heS := (mem_edgesWithin.mp (graphTreeCharge_support G L k x S e hc)).2
  have hsub : e.toFinset ⊆ S := fun v hv => heS v (Sym2.mem_toFinset.mp hv)
  have hne : e.toFinset.Nonempty := by
    induction e using Sym2.inductionOn with
    | hf a b => exact ⟨a, Sym2.mem_toFinset.mpr (Sym2.mem_mk_left a b)⟩
  exact (peelChain_of_mem_blockEdgeSets G hdeg hTb U _ hsub hne).le z
    fun C u _ hu hs => hz C u hu hs

/-- The derivative keeps a fraction `1 - 2eo` of its positive edge terms, under the peel budget. -/
theorem graphActivity_peel_derivative_lower_bound {D : ℕ} (hdeg : ∀ v, G.degree v ≤ D)
    {x₀ e o r : ℝ} (hc : ParityCert D x₀ e o r) (hr : r < 1)
    {L : ListAssignment V} {k : ℕ} (hL : IsNListAssignment L k)
    {x : ℝ} (hx : 0 ≤ x) (hxx : x ≤ x₀) (hbudget : (k : ℝ) * x * o ≤ (k : ℝ) * x - 1)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (U : Finset V) :
    (1 - 2 * e * o) * ∑ f ∈ edgesWithin G.edgeFinset U,
        (edgeDef L k f : ℝ) * x ^ 2 * partitionSum (fun T => graphActivity G L k x T t)
          (U \ f.toFinset) ≤
      ∑ S ∈ blocks U, graphActivityDeriv G L k x S *
        partitionSum (fun T => graphActivity G L k x T t) (U \ S) := by
  classical
  let z := partitionSum (fun T => graphActivity G L k x T t)
  have hp := graphActivity_peel_positive G hdeg hc hr hL hx hxx hbudget ht
  have hz : ∀ A, 0 ≤ z A := fun A => (hp A).1.le
  have hm : ∀ S f, S ⊆ U → graphTreeCharge G L k x S f ≠ 0 → z (U \ S) ≤ z (U \ f.toFinset) :=
    fun S f _ hcf => graphActivity_peel_charge_mono G hdeg z (fun C u hu hs => (hp C).2 u hu hs)
      U S f hcf
  have htail := graphActivity_parity_charged_tail_of G hdeg hc hL hx hxx U z hz hm
  have hsplit := Finset.sum_filter_add_sum_filter_not (blocks U) (fun S => S.card ≤ 2)
    (fun S => graphActivityDeriv G L k x S * z (U \ S))
  rw [small_derivative_sum_eq_edges G hL, blocks_filter_large] at hsplit
  simp only [neg_mul, Finset.sum_neg_distrib] at htail
  change (1 - 2 * e * o) * ∑ f ∈ edgesWithin G.edgeFinset U,
    (edgeDef L k f : ℝ) * x ^ 2 * z (U \ f.toFinset) ≤ _
  linarith

/-- The hypotheses of the degree-sensitive polymer argument at list size `k`. -/
def CertifiedPeelAt (D k : ℕ) : Prop :=
  ∃ q x₀ e o r : ℝ, 0 < q ∧ ParityCert D x₀ e o r ∧ r < 1 ∧ q⁻¹ ≤ x₀ ∧
    (k : ℝ) * q⁻¹ * o ≤ (k : ℝ) * q⁻¹ - 1

/-- A certificate at activity `s / k₀` with `s o ≤ s - 1` and `r < 1` covers every `k ≥ k₀`. -/
theorem certifiedPeelAt_of_parityCert {D k₀ : ℕ} {s e o r : ℝ}
    (hc : ParityCert D (s / k₀) e o r) (hr : r < 1) (hs : 0 < s) (hso : s * o ≤ s - 1)
    (hk₀ : 0 < k₀) {k : ℕ} (hk : k₀ ≤ k) : CertifiedPeelAt D k := by
  have hk₀' : (0 : ℝ) < k₀ := by exact_mod_cast hk₀
  have hkk : (k₀ : ℝ) ≤ k := by exact_mod_cast hk
  have hk' : (0 : ℝ) < k := hk₀'.trans_le hkk
  have hks : (k : ℝ) * (k / s)⁻¹ = s := by rw [inv_div]; field_simp
  refine ⟨k / s, _, e, o, r, div_pos hk' hs, hc, hr, ?_, by rw [hks]; exact hso⟩
  rw [inv_div]
  gcongr

/-- `P(G,k) ≤ P(G,L)` under the degree-sensitive certificate. -/
theorem colConst_le_col_of_certifiedPeelAt {D k : ℕ} (hdeg : ∀ v, G.degree v ≤ D)
    (hcert : CertifiedPeelAt D k) {L : ListAssignment V} (hL : IsNListAssignment L k) :
    G.colConst k ≤ G.col L := by
  obtain ⟨q, x₀, e, o, r, hq, hc, hr, hqx, hbudget⟩ := hcert
  have hx : 0 ≤ q⁻¹ := (inv_pos.mpr hq).le
  have hh := partitionSum_endpoints_le (Finset.univ : Finset V)
    (graphActivity G L k q⁻¹)
    (fun S _t => graphActivityDeriv G L k q⁻¹ S)
    (fun t S _ => hasDerivAt_graphActivity G L k _ t S)
    (fun t ht => by
      have hp := graphActivity_peel_positive G hdeg hc hr hL hx hqx hbudget ht
      refine le_trans (mul_nonneg (by linarith [hc.edge]) (Finset.sum_nonneg fun f _ => ?_))
        (graphActivity_peel_derivative_lower_bound G hdeg hc hr hL hx hqx hbudget ht _)
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) (hp _).1.le)
  rw [partitionSum_graphActivity_eq, partitionSum_graphActivity_eq,
    interpolatedSum_zero, interpolatedSum_one] at hh
  have hqn := pow_pos hq (Finset.univ : Finset V).card
  have hcol : (G.colConst k : ℝ) ≤ (G.col L : ℝ) := (div_le_div_iff_of_pos_right hqn).mp hh
  exact_mod_cast hcol

theorem eccAt_of_certifiedPeelAt {D k : ℕ} (hdeg : ∀ v, G.degree v ≤ D)
    (hcert : CertifiedPeelAt D k) : G.ECCAt k :=
  fun _ hL => colConst_le_col_of_certifiedPeelAt G hdeg hcert hL

end GridGen.Polymer
