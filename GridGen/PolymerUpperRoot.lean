/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.PolymerPairBlocks
import GridGen.PolymerParityCount

/-!
# The upper deletion ratio at any root

In the root recurrence `z U = k x z (U - v) + ∑ w S z (U ∖ S)`, the edges at `v` contribute
`-(k - t d_{vu}) x² z (U ∖ {v, u})`, even blocks of four or more vertices contribute nonpositive
terms, and every odd block is charged to a root edge `s(v, u)` of each of its spanning trees: its
interpolation factor is at most that edge's, and peeling outward from the edge gives
`z (U ∖ S) ≤ z (U ∖ {v, u})`. The edge-rooted parity count bounds the total charge on each root
edge by `2 e o` times the edge term, so under `2 e o < 1` the block sum is nonpositive and
`z U ≤ k x z (U - v)`.
-/

namespace GridGen.Polymer

open SimpleGraph Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] in
/-- The two-vertex rooted blocks are the pairs `{v, u}`. -/
theorem rootedBlocks_card_two (U : Finset V) {v : V} (hv : v ∈ U) :
    (rootedBlocks U v).filter (fun S => S.card = 2) =
      (U.erase v).image (fun u => ({v, u} : Finset V)) := by
  ext S
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨hS, h2⟩
    obtain ⟨hSU, hvS, -⟩ := mem_rootedBlocks hS
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvS
    rcases hvS with rfl | rfl
    · exact ⟨b, ⟨hab.symm, hSU (by simp)⟩, rfl⟩
    · exact ⟨a, ⟨hab, hSU (by simp)⟩, Finset.pair_comm _ _⟩
  · rintro ⟨u, ⟨huv, huU⟩, rfl⟩
    refine ⟨?_, Finset.card_pair (Ne.symm huv)⟩
    simp only [rootedBlocks, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, by simp, (Finset.card_pair (Ne.symm huv)).ge⟩
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl <;> assumption

omit [Fintype V] in
theorem pair_injOn (U : Finset V) (v : V) :
    Set.InjOn (fun u => ({v, u} : Finset V)) (U.erase v : Set V) := by
  intro a ha b hb h
  have ha' := (Finset.mem_erase.mp ha).1
  have : a ∈ ({v, b} : Finset V) := by rw [← show ({v, a} : Finset V) = {v, b} from h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  exact this.resolve_left ha'

/-- A spanning connected edge set of a block of at least two vertices uses an edge at each of its
vertices. -/
theorem exists_root_edge {S : Finset V} {T : Finset (Sym2 V)} (hT : T ∈ blockEdgeSets G S)
    {v : V} (hv : v ∈ S) (h2 : 2 ≤ S.card) : ∃ u, s(v, u) ∈ T ∧ G.Adj v u ∧ u ∈ S := by
  obtain ⟨hTsub, hconn⟩ := (mem_blockEdgeSets G).mp hT
  obtain ⟨w, hwS, hwv⟩ := Finset.exists_mem_ne (show 1 < S.card by omega) v
  obtain ⟨p⟩ := hconn.2 v hv w hwS
  cases p with
  | nil => exact absurd rfl hwv
  | @cons _ u _ hadj _ =>
    simp only [SimpleGraph.fromEdgeSet_adj, Finset.mem_coe] at hadj
    have hmem := mem_edgesWithin.mp (hTsub hadj.1)
    exact ⟨u, hadj.1, G.mem_edgeFinset.mp hmem.1, hmem.2 u (Sym2.mem_mk_right _ _)⟩

omit [Fintype V] in
theorem sdiff_ssubset_of_mem {U S : Finset V} {v : V} (hv : v ∈ U) (hvS : v ∈ S) :
    U \ S ⊂ U :=
  (Finset.ssubset_iff_of_subset Finset.sdiff_subset).mpr
    ⟨v, hv, fun h => (Finset.mem_sdiff.mp h).2 hvS⟩

/-- **The rooted block sum is nonpositive** under `2 e o < 1`, given the small-deletion
monotonicity on proper subsets. -/
theorem graphActivity_upper_root {D : ℕ} (hdeg : ∀ v, G.degree v ≤ D)
    {x₀ e o r : ℝ} (hc : ParityCert D x₀ e o r)
    {L : ListAssignment V} {k : ℕ} (hL : IsNListAssignment L k)
    {x t : ℝ} (hx : 0 ≤ x) (hxx : x ≤ x₀) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (U : Finset V) {v : V} (hv : v ∈ U) (z : Finset V → ℝ) (hz : ∀ A, A ⊂ U → 0 ≤ z A)
    (hmono : ∀ C u, C ⊂ U → u ∈ C → smallIn G (D - 1) C u → z (C.erase u) ≤ z C) :
    ∑ S ∈ rootedBlocks U v, graphActivity G L k x S t * z (U \ S) ≤ 0 := by
  classical
  set N := (U.erase v).filter (G.Adj v) with hN
  let E : V → ℝ := fun u =>
    ((k : ℝ) - t * listDeficiency L k {v, u}) * x ^ 2 * z (U \ {v, u})
  have hE : ∀ u, 0 ≤ E u := fun u =>
    mul_nonneg (mul_nonneg (interpolation_factor_bounds hL (S := {v, u}) ⟨v, by simp⟩ ht).1
      (pow_nonneg hx 2)) (hz _ (sdiff_ssubset_of_mem hv (by simp)))
  -- the comparison along a peel from a root edge
  have hpeel : ∀ S T u, T ∈ blockEdgeSets G S → v ∈ S → u ∈ S →
      z (U \ S) ≤ z (U \ {v, u}) := by
    intro S T u hT hvS huS
    have hch := peelChain_of_mem_blockEdgeSets G hdeg hT U {v, u}
      (by intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl <;> assumption) (by simp)
    refine hch.le z fun C w hC hw hs => hmono C w ?_ hw hs
    exact lt_of_le_of_lt hC
      ((Finset.ssubset_iff_of_subset Finset.sdiff_subset).mpr ⟨v, hv, by simp⟩)
  -- split off the two-vertex blocks
  rw [← Finset.sum_filter_add_sum_filter_not (rootedBlocks U v) (fun S => S.card = 2)]
  have htwo : ∑ S ∈ (rootedBlocks U v).filter (fun S => S.card = 2),
      graphActivity G L k x S t * z (U \ S) = -∑ u ∈ N, E u := by
    rw [rootedBlocks_card_two U hv, Finset.sum_image (pair_injOn U v), hN, Finset.sum_filter,
      ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    have huv : v ≠ u := Ne.symm (Finset.mem_erase.mp hu).1
    split_ifs with hadj
    · rw [graphActivity_pair_of_adj G x t hadj]; ring
    · rw [graphActivity_pair_of_not_adj G x t huv hadj]; ring
  -- every other block is charged to the root edges of its spanning trees
  let F : Finset V → ℝ := fun S =>
    ∑ T ∈ spanningTreeSets G S, ∑ u ∈ N, if s(v, u) ∈ T then E u * x ^ (S.card - 2) else 0
  have hF : ∀ S, 0 ≤ F S := fun S => Finset.sum_nonneg fun T _ => Finset.sum_nonneg fun u _ => by
    split_ifs
    · exact mul_nonneg (hE u) (pow_nonneg hx _)
    · exact le_rfl
  have hrest : ∀ S ∈ (rootedBlocks U v).filter (fun S => ¬ S.card = 2),
      graphActivity G L k x S t * z (U \ S) ≤
        if 3 ≤ S.card ∧ Odd S.card then F S else 0 := by
    intro S hS
    obtain ⟨hSrb, hS2⟩ := Finset.mem_filter.mp hS
    obtain ⟨hSU, hvS, hcard⟩ := mem_rootedBlocks hSrb
    have hne : S.Nonempty := ⟨v, hvS⟩
    have hf := interpolation_factor_bounds hL hne ht
    rcases Nat.even_or_odd S.card with hev | hodd
    · have hcoef := blockCoefficient_nonpos_of_even G S hev hne
      have hnot : ¬ (3 ≤ S.card ∧ Odd S.card) := fun h => (Nat.not_odd_iff_even.mpr hev) h.2
      rw [ite_cond_eq_false _ _ (eq_false hnot)]
      apply mul_nonpos_of_nonpos_of_nonneg _ (hz _ (sdiff_ssubset_of_mem hv hvS))
      exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hcoef hf.1)
        (pow_nonneg hx _)
    · rw [ite_cond_eq_true _ _ (eq_true ⟨by omega, hodd⟩)]
      have hxS := pow_nonneg hx S.card
      calc
        _ ≤ |blockCoefficient G S| * ((k : ℝ) - t * listDeficiency L k S) * x ^ S.card *
            z (U \ S) := by
          apply mul_le_mul_of_nonneg_right _ (hz _ (sdiff_ssubset_of_mem hv hvS))
          apply mul_le_mul_of_nonneg_right _ hxS
          exact mul_le_mul_of_nonneg_right (le_abs_self _) hf.1
        _ ≤ (spanningTreeSets G S).card * ((k : ℝ) - t * listDeficiency L k S) * x ^ S.card *
            z (U \ S) := by
          apply mul_le_mul_of_nonneg_right _ (hz _ (sdiff_ssubset_of_mem hv hvS))
          apply mul_le_mul_of_nonneg_right _ hxS
          exact mul_le_mul_of_nonneg_right (blockCoefficient_abs_le_trees G S) hf.1
        _ = ∑ T ∈ spanningTreeSets G S,
            ((k : ℝ) - t * listDeficiency L k S) * x ^ S.card * z (U \ S) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ F S := by
          apply Finset.sum_le_sum
          intro T hT
          have hTb := ((mem_spanningTreeSets G).mp hT).1
          obtain ⟨u, huT, hadj, huS⟩ := exists_root_edge G hTb hvS hcard
          have huN : u ∈ N := Finset.mem_filter.mpr
            ⟨Finset.mem_erase.mpr ⟨hadj.ne.symm, hSU huS⟩, hadj⟩
          refine le_trans ?_ (Finset.single_le_sum (f := fun u =>
            if s(v, u) ∈ T then E u * x ^ (S.card - 2) else 0) (fun u _ => by
              split_ifs
              · exact mul_nonneg (hE u) (pow_nonneg hx _)
              · exact le_rfl) huN)
          simp only [ite_cond_eq_true _ _ (eq_true huT), E]
          have hsub : ({v, u} : Finset V) ⊆ S := by
            intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl <;> assumption
          have hd := listDeficiency_mono (L := L) (k := k) (by simp) hsub
          have hfac : (k : ℝ) - t * listDeficiency L k S ≤ (k : ℝ) - t * listDeficiency L k {v, u} := by
            nlinarith [ht.1]
          have hzz := hpeel S T u hTb hvS huS
          have hpow : x ^ S.card = x ^ 2 * x ^ (S.card - 2) := by
            rw [← pow_add]; congr 1; omega
          rw [hpow]
          have h1 := mul_le_mul hfac hzz (hz _ (sdiff_ssubset_of_mem hv hvS))
            (interpolation_factor_bounds hL (S := {v, u}) ⟨v, by simp⟩ ht).1
          have h2 : 0 ≤ x ^ 2 * x ^ (S.card - 2) := by positivity
          nlinarith [mul_le_mul_of_nonneg_left h1 h2]
  have hsumrest : ∑ S ∈ (rootedBlocks U v).filter (fun S => ¬ S.card = 2),
      graphActivity G L k x S t * z (U \ S) ≤ (2 * e * o) * ∑ u ∈ N, E u := by
    calc
      _ ≤ ∑ S ∈ (rootedBlocks U v).filter (fun S => ¬ S.card = 2),
          (if 3 ≤ S.card ∧ Odd S.card then F S else 0) := Finset.sum_le_sum hrest
      _ ≤ ∑ S ∈ U.powerset.filter (fun S => 3 ≤ S.card ∧ Odd S.card), F S := by
        rw [← Finset.sum_filter]
        apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun S _ _ => hF S)
        intro S hS
        obtain ⟨hS1, hS2⟩ := Finset.mem_filter.mp hS
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr (mem_rootedBlocks (Finset.mem_filter.mp hS1).1).1, hS2⟩
      _ = ∑ u ∈ N, E u * ∑ S ∈ U.powerset.filter (fun S => 3 ≤ S.card ∧ Odd S.card),
          ∑ _T ∈ (spanningTreeSets G S).filter (fun T => s(v, u) ∈ T), x ^ (S.card - 2) := by
        simp only [F]
        conv_lhs => arg 2; ext S; rw [Finset.sum_comm]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [Finset.sum_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl fun T _ => ?_
        split_ifs <;> simp
      _ ≤ ∑ u ∈ N, E u * (2 * e * o) := by
        apply Finset.sum_le_sum
        intro u hu
        exact mul_le_mul_of_nonneg_left
          (odd_edge_tree_sum_cert_le G hdeg hc hx hxx U (Finset.mem_filter.mp hu).2) (hE u)
      _ = _ := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  have hsum : 0 ≤ ∑ u ∈ N, E u := Finset.sum_nonneg fun u _ => hE u
  rw [htwo]
  nlinarith [hc.edge]

end GridGen.Polymer
