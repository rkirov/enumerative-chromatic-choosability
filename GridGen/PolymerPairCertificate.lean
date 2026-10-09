/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.PolymerPairRoot
import GridGen.PolymerPeelCertificate

/-!
# ECC from the neighbour-pair certificate

The degree-sensitive induction of `PolymerPeelCertificate.lean`, strengthened by a third claim,
the upper ratio `z U ≤ k x z (U - u)` at every vertex (`PolymerUpperRoot.lean`). The upper ratio
gives lower bounds on the positive neighbour-pair blocks at a root, which the earlier argument
discards, and on the deficient edges' saving; together they raise the lower ratio at a root with
`D - 1` neighbours by `C(D - 1, 2) x / k` (`PolymerPairRoot.lean`). Roots with fewer neighbours use
the `D - 2`-port odd mass, and full-degree roots still need only positivity.

`CertifiedPairAt` packages the numbers and `eccAt_of_certifiedPairAt` concludes ECC. The instance
is `PeelDegree.lean`'s degree-four bound at `k = 16`. The argument, including the upper ratio and
the neighbour-pair blocks, was proposed by Codex (OpenAI) in
`ai_research_notes/CODEX_GRID_ALL_HEIGHTS_2026-10-07.md` §3; the formal proof and the
`D - 2`-port treatment of the smaller roots are this repository's.
-/

namespace GridGen.Polymer

open SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem filter_adj_card_le_degree (U : Finset V) (v : V) :
    (U.filter (G.Adj v)).card ≤ G.degree v := by
  rw [← card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro w hw
  exact (G.mem_neighborFinset v w).mpr (Finset.mem_filter.mp hw).2

/-- **Positivity, the small-deletion ratio and the upper ratio, simultaneously.** -/
theorem graphActivity_pair_good {D : ℕ} (hdeg : ∀ v, G.degree v ≤ D)
    {x₀ e o r : ℝ} (hc : ParityCert D x₀ e o r) (hr : r < 1)
    {L : ListAssignment V} {k : ℕ} (hL : IsNListAssignment L k)
    {x : ℝ} (hx : 0 < x) (hxx : x ≤ x₀) (hk : 0 < k)
    (hfull : 1 ≤ (k : ℝ) * x * (1 - (parityPower (1 + x₀ * o) (x₀ * e) (D - 1)).2) +
        (((D - 1).choose 2 : ℕ) : ℝ) * (x / k))
    (hless : 1 ≤ (k : ℝ) * x * (1 - (parityPower (1 + x₀ * o) (x₀ * e) (D - 2)).2))
    (hpd : (((D - 1 : ℕ) : ℝ) - 1) * x ^ 3 ≤ x / k)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (U : Finset V) :
    0 < partitionSum (fun S => graphActivity G L k x S t) U ∧
      (∀ u, u ∈ U → smallIn G (D - 1) U u →
        partitionSum (fun S => graphActivity G L k x S t) (U.erase u) ≤
          partitionSum (fun S => graphActivity G L k x S t) U) ∧
      (∀ u, u ∈ U → partitionSum (fun S => graphActivity G L k x S t) U ≤
        (k : ℝ) * x * partitionSum (fun S => graphActivity G L k x S t) (U.erase u)) := by
  classical
  set z := partitionSum (fun S => graphActivity G L k x S t) with hzdef
  have hkx : 0 < (k : ℝ) * x := mul_pos (Nat.cast_pos.mpr hk) hx
  have hrec : ∀ U v, v ∈ U → z U = (k : ℝ) * x * z (U.erase v) +
      ∑ S ∈ rootedBlocks U v, graphActivity G L k x S t * z (U \ S) := by
    intro U v hv
    have := partitionSum_root_split (fun S => graphActivity G L k x S t) v hv
    rwa [graphActivity_singleton G hL] at this
  have hpow : ∀ n, 0 ≤ (parityPower (1 + x₀ * o) (x₀ * e) n).2 := fun n =>
    (parityPower_nonneg (by have := mul_nonneg hc.x₀_nonneg hc.o_nonneg; linarith)
      (mul_nonneg hc.x₀_nonneg hc.e_nonneg) n).2
  induction U using Finset.strongInductionOn with
  | _ U ih =>
    by_cases hU : U = ∅
    · subst hU
      exact ⟨by simp [z], fun u hu => absurd hu (Finset.notMem_empty u),
        fun u hu => absurd hu (Finset.notMem_empty u)⟩
    have hz : ∀ A, A ⊂ U → 0 ≤ z A := fun A hA => (ih A hA).1.le
    have hmono : ∀ C u, C ⊂ U → u ∈ C → smallIn G (D - 1) C u → z (C.erase u) ≤ z C :=
      fun C u hC hu hs => (ih C hC).2.1 u hu hs
    have hup : ∀ C u, C ⊂ U → u ∈ C → z C ≤ (k : ℝ) * x * z (C.erase u) :=
      fun C u hC hu => (ih C hC).2.2 u hu
    obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hU
    refine ⟨?_, ?_, ?_⟩
    · -- positivity from the full-degree root bound `r < 1`
      have hlow := graphActivity_root_lower_plain G hdeg hc hL hx.le hxx ht U hv
        ((filter_adj_card_le_degree G U v).trans (hdeg v)) z hz (hrec U v hv) hmono
      have hZ := (ih _ (Finset.erase_ssubset hv)).1
      have hroot := hc.root
      have : 0 < (k : ℝ) * x * (1 - (parityPower (1 + x₀ * o) (x₀ * e) D).2) :=
        mul_pos hkx (by linarith)
      exact lt_of_lt_of_le (mul_pos this hZ) hlow
    · intro u hu hsmall
      have hZ := (ih _ (Finset.erase_ssubset hu)).1
      unfold smallIn at hsmall
      by_cases hfullN : (U.filter (G.Adj u)).card = D - 1
      · have hpd' : (((D - 1 : ℕ) : ℝ) - 1) * x ^ 3 ≤ x / k := hpd
        have hlow := graphActivity_pair_root_lower G hdeg hc hL hx.le hxx hkx ht U hu
          hfullN.le hpd' z hz (hrec U u hu) hmono hup
        rw [hfullN] at hlow
        nlinarith
      · have hle : (U.filter (G.Adj u)).card ≤ D - 2 := by omega
        have hlow := graphActivity_root_lower_plain G hdeg hc hL hx.le hxx ht U hu hle z hz
          (hrec U u hu) hmono
        nlinarith
    · intro u hu
      have hneg := graphActivity_upper_root G hdeg hc hL hx.le hxx ht U hu z hz hmono
      rw [hrec U u hu]
      linarith

/-- The derivative bound of `PolymerPeelCertificate.lean`, from positivity and small-deletion
monotonicity as hypotheses. -/
theorem graphActivity_derivative_lower_bound_of {D : ℕ} (hdeg : ∀ v, G.degree v ≤ D)
    {x₀ e o r : ℝ} (hc : ParityCert D x₀ e o r)
    {L : ListAssignment V} {k : ℕ} (hL : IsNListAssignment L k)
    {x : ℝ} (hx : 0 ≤ x) (hxx : x ≤ x₀) {t : ℝ} (U : Finset V)
    (hp : ∀ A, 0 < partitionSum (fun S => graphActivity G L k x S t) A ∧
      ∀ u, u ∈ A → smallIn G (D - 1) A u →
        partitionSum (fun S => graphActivity G L k x S t) (A.erase u) ≤
          partitionSum (fun S => graphActivity G L k x S t) A) :
    (1 - 2 * e * o) * ∑ f ∈ edgesWithin G.edgeFinset U,
        (edgeDef L k f : ℝ) * x ^ 2 * partitionSum (fun T => graphActivity G L k x T t)
          (U \ f.toFinset) ≤
      ∑ S ∈ blocks U, graphActivityDeriv G L k x S *
        partitionSum (fun T => graphActivity G L k x T t) (U \ S) := by
  classical
  let z := partitionSum (fun T => graphActivity G L k x T t)
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

/-- The hypotheses of the neighbour-pair argument at list size `k`. -/
def CertifiedPairAt (D k : ℕ) : Prop :=
  ∃ q x₀ e o r : ℝ, 0 < q ∧ ParityCert D x₀ e o r ∧ r < 1 ∧ q⁻¹ ≤ x₀ ∧
    1 ≤ (k : ℝ) * q⁻¹ * (1 - (parityPower (1 + x₀ * o) (x₀ * e) (D - 1)).2) +
      (((D - 1).choose 2 : ℕ) : ℝ) * (q⁻¹ / k) ∧
    1 ≤ (k : ℝ) * q⁻¹ * (1 - (parityPower (1 + x₀ * o) (x₀ * e) (D - 2)).2) ∧
    (((D - 1 : ℕ) : ℝ) - 1) * q⁻¹ ^ 3 ≤ q⁻¹ / k

/-- `P(G,k) ≤ P(G,L)` under the neighbour-pair certificate. -/
theorem colConst_le_col_of_certifiedPairAt {D k : ℕ} (hdeg : ∀ v, G.degree v ≤ D)
    (hk : 0 < k) (hcert : CertifiedPairAt D k) {L : ListAssignment V}
    (hL : IsNListAssignment L k) : G.colConst k ≤ G.col L := by
  obtain ⟨q, x₀, e, o, r, hq, hc, hr, hqx, hfull, hless, hpd⟩ := hcert
  have hx : 0 < q⁻¹ := inv_pos.mpr hq
  have hgood := fun {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) =>
    graphActivity_pair_good G hdeg hc hr hL hx hqx hk hfull hless hpd ht
  have hh := partitionSum_endpoints_le (Finset.univ : Finset V)
    (graphActivity G L k q⁻¹)
    (fun S _t => graphActivityDeriv G L k q⁻¹ S)
    (fun t S _ => hasDerivAt_graphActivity G L k _ t S)
    (fun t ht => by
      have hp : ∀ A, 0 < partitionSum (fun S => graphActivity G L k q⁻¹ S t) A ∧
          ∀ u, u ∈ A → smallIn G (D - 1) A u →
            partitionSum (fun S => graphActivity G L k q⁻¹ S t) (A.erase u) ≤
              partitionSum (fun S => graphActivity G L k q⁻¹ S t) A :=
        fun A => ⟨(hgood ht A).1, (hgood ht A).2.1⟩
      refine le_trans (mul_nonneg (by linarith [hc.edge]) (Finset.sum_nonneg fun f _ => ?_))
        (graphActivity_derivative_lower_bound_of G hdeg hc hL hx.le hqx _ hp)
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) (hp _).1.le)
  rw [partitionSum_graphActivity_eq, partitionSum_graphActivity_eq,
    interpolatedSum_zero, interpolatedSum_one] at hh
  have hqn := pow_pos hq (Finset.univ : Finset V).card
  have hcol : (G.colConst k : ℝ) ≤ (G.col L : ℝ) := (div_le_div_iff_of_pos_right hqn).mp hh
  exact_mod_cast hcol

theorem eccAt_of_certifiedPairAt {D k : ℕ} (hdeg : ∀ v, G.degree v ≤ D) (hk : 0 < k)
    (hcert : CertifiedPairAt D k) : G.ECCAt k :=
  fun _ hL => colConst_le_col_of_certifiedPairAt G hdeg hk hcert hL

end GridGen.Polymer
