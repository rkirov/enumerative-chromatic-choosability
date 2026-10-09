/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.PolymerPeelRoot
import GridGen.PolymerSmallBlocks

/-!
# Blocks of two and three vertices at a root

The pieces of the root recurrence that the neighbour-pair refinement (`PolymerPairRoot.lean`)
keeps exactly rather than bounding by tree counts:

* a pair `{v, u}` has coefficient `-1` if `u ~ v` and `0` otherwise;
* a triple `{v, u, w}` with `u, w` neighbours of `v` has coefficient at least `1` (it is `1` for a
  path and `2` for a triangle), and its deficiency is at most the sum of the two edge deficiencies.

It also records the root odd-mass bound for a root with at most `n` ports, and the even-block
"harm" whose sum at a root that bound controls.
-/

namespace GridGen.Polymer

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### Three-vertex blocks -/

/-- An edge of `G` inside a three-element set is one of its three pairs. -/
theorem edge_cases_triple {a b c : V} {e : Sym2 V}
    (he : e ∈ edgesWithin G.edgeFinset {a, b, c}) :
    e = s(a, b) ∨ e = s(a, c) ∨ e = s(b, c) := by
  obtain ⟨heG, heS⟩ := mem_edgesWithin.mp he
  induction e using Sym2.ind with
  | _ x y =>
    have hxy : G.Adj x y := G.mem_edgeFinset.mp heG
    have hx := heS x (Sym2.mem_mk_left _ _)
    have hy := heS y (Sym2.mem_mk_right _ _)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first
      | exact absurd rfl hxy.ne
      | simp [Sym2.eq_iff]

omit [Fintype V] [DecidableEq V] in
theorem eq_of_reachable_of_isolated {T : Finset (Sym2 V)} {x y : V}
    (hx : ∀ e ∈ T, x ∉ e) (h : (edgeGraph T).Reachable x y) : x = y := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => rfl
  | cons hadj _ =>
    exfalso
    simp only [SimpleGraph.fromEdgeSet_adj, Finset.mem_coe] at hadj
    exact hx _ hadj.1 (Sym2.mem_mk_left _ _)

omit [Fintype V] [DecidableEq V] in
theorem reachable_of_mem_edges {T : Finset (Sym2 V)} {x y : V} (hxy : x ≠ y)
    (h : s(x, y) ∈ T) : (edgeGraph T).Reachable x y :=
  (show (edgeGraph T).Adj x y from ⟨by simpa using h, hxy⟩).reachable

/-- On three vertices, an edge set is connected exactly when it has at least two edges. -/
theorem connectedOn_triple_iff {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {T : Finset (Sym2 V)} (hT : T ⊆ edgesWithin G.edgeFinset {a, b, c}) :
    ConnectedOn T {a, b, c} ↔ 2 ≤ T.card := by
  constructor
  · intro hconn
    by_contra hlt
    push_neg at hlt
    have hone : ∀ e ∈ T, ∀ f ∈ T, e = f := Finset.card_le_one.mp (by omega)
    -- some vertex of the triple meets no edge of `T`
    have hiso : ∃ x ∈ ({a, b, c} : Finset V), ∃ y ∈ ({a, b, c} : Finset V), x ≠ y ∧
        ∀ e ∈ T, x ∉ e := by
      by_cases hne : T.Nonempty
      · obtain ⟨e, he⟩ := hne
        rcases edge_cases_triple G (hT he) with rfl | rfl | rfl
        · refine ⟨c, by simp, a, by simp, hac.symm, fun f hf => ?_⟩
          rw [hone f hf _ he]; simp [Sym2.mem_iff, hac.symm, hbc.symm]
        · refine ⟨b, by simp, a, by simp, hab.symm, fun f hf => ?_⟩
          rw [hone f hf _ he]; simp [Sym2.mem_iff, hab.symm, hbc]
        · refine ⟨a, by simp, b, by simp, hab, fun f hf => ?_⟩
          rw [hone f hf _ he]; simp [Sym2.mem_iff, hab, hac]
      · refine ⟨a, by simp, b, by simp, hab, fun f hf => (hne ⟨f, hf⟩).elim⟩
    obtain ⟨x, hx, y, hy, hxy, hxT⟩ := hiso
    exact hxy (eq_of_reachable_of_isolated hxT (hconn.2 x hx y hy))
  · intro h2
    obtain ⟨e, he, f, hf, hef⟩ := Finset.one_lt_card.mp h2
    have Rab := fun h : s(a, b) ∈ T => reachable_of_mem_edges hab h
    have Rac := fun h : s(a, c) ∈ T => reachable_of_mem_edges hac h
    have Rbc := fun h : s(b, c) ∈ T => reachable_of_mem_edges hbc h
    have hR : (edgeGraph T).Reachable a b ∧ (edgeGraph T).Reachable a c := by
      rcases edge_cases_triple G (hT he) with rfl | rfl | rfl <;>
        rcases edge_cases_triple G (hT hf) with rfl | rfl | rfl <;>
        first
        | exact absurd rfl hef
        | exact ⟨Rab ‹_›, Rac ‹_›⟩
        | exact ⟨Rab ‹_›, (Rab ‹_›).trans (Rbc ‹_›)⟩
        | exact ⟨(Rac ‹_›).trans (Rbc ‹_›).symm, Rac ‹_›⟩
    have hfrom : ∀ x ∈ ({a, b, c} : Finset V), (edgeGraph T).Reachable a x := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact .rfl
      · exact hR.1
      · exact hR.2
    exact ⟨⟨a, by simp⟩, fun x hx y hy => (hfrom x hx).symm.trans (hfrom y hy)⟩

/-- **A root with two neighbours spans a block of coefficient at least one.** It is `1` for an
induced path and `2` for a triangle. -/
theorem one_le_blockCoefficient_triple {v u w : V} (hu : G.Adj v u) (hw : G.Adj v w)
    (huw : u ≠ w) : 1 ≤ blockCoefficient G {v, u, w} := by
  classical
  set E := edgesWithin G.edgeFinset {v, u, w} with hE
  have hvu : v ≠ u := hu.ne
  have hvw : v ≠ w := hw.ne
  have huE : s(v, u) ∈ E := mem_edgesWithin.mpr ⟨G.mem_edgeFinset.mpr hu, fun x hx => by
    rcases Sym2.mem_iff.mp hx with rfl | rfl <;> simp⟩
  have hwE : s(v, w) ∈ E := mem_edgesWithin.mpr ⟨G.mem_edgeFinset.mpr hw, fun x hx => by
    rcases Sym2.mem_iff.mp hx with rfl | rfl <;> simp⟩
  have hne : s(v, u) ≠ s(v, w) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨_, h⟩ | ⟨h1, h2⟩
    · exact huw h
    · exact hvw h1
  have hE2 : 2 ≤ E.card := by
    have : ({s(v, u), s(v, w)} : Finset (Sym2 V)) ⊆ E := by
      intro e he; simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl <;> assumption
    simpa [Finset.card_pair hne] using Finset.card_le_card this
  have hE3 : E.card ≤ 3 := by
    have : E ⊆ {s(v, u), s(v, w), s(u, w)} := by
      intro e he
      rcases edge_cases_triple G he with rfl | rfl | rfl <;> simp
    exact (Finset.card_le_card this).trans Finset.card_le_three
  have hBES : blockEdgeSets G {v, u, w} = E.powerset.filter (fun T => 2 ≤ T.card) := by
    ext T
    rw [mem_blockEdgeSets, Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨hT, hc⟩
      exact ⟨hT, (connectedOn_triple_iff G hvu hvw huw hT).mp hc⟩
    · rintro ⟨hT, hc⟩
      exact ⟨hT, (connectedOn_triple_iff G hvu hvw huw hT).mpr hc⟩
  rw [blockCoefficient, hBES, Finset.sum_filter,
    Finset.sum_powerset_apply_card (fun m => if 2 ≤ m then (-1 : ℝ) ^ m else 0)]
  have hcases : E.card = 2 ∨ E.card = 3 := by omega
  rcases hcases with h | h <;> rw [h] <;> simp [Finset.sum_range_succ, Nat.choose] <;> norm_num

/-- A non-adjacent pair is not a block. -/
theorem blockCoefficient_pair_of_not_adj {u v : V} (huv : u ≠ v) (h : ¬ G.Adj u v) :
    blockCoefficient G {u, v} = 0 := by
  classical
  have hE : edgesWithin G.edgeFinset {u, v} = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    rcases edge_cases_triple G (a := u) (b := v) (c := v) (by simpa using he) with
      rfl | rfl | rfl
    · exact h (G.mem_edgeFinset.mp (mem_edgesWithin.mp he).1)
    · exact h (G.mem_edgeFinset.mp (mem_edgesWithin.mp he).1)
    · exact (G.mem_edgeFinset.mp (mem_edgesWithin.mp he).1).ne rfl
  have hB : blockEdgeSets G {u, v} = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro T hT
    obtain ⟨hTE, hc⟩ := (mem_blockEdgeSets G).mp hT
    rw [hE, Finset.subset_empty] at hTE
    subst hTE
    exact not_connectedOn_empty_pair huv hc
  simp [blockCoefficient, hB]

/-! ### Deficiencies -/

theorem listDeficiency_mono {L : ListAssignment V} {k : ℕ} {A S : Finset V}
    (hA : A.Nonempty) (hAS : A ⊆ S) : listDeficiency L k A ≤ listDeficiency L k S := by
  unfold listDeficiency
  have : listInter L S ⊆ listInter L A := by
    intro a ha
    rw [mem_listInter (hA.mono hAS)] at ha
    rw [mem_listInter hA]
    exact fun v hv => ha v (hAS hv)
  have := Finset.card_le_card this
  have : ((listInter L S).card : ℝ) ≤ (listInter L A).card := by exact_mod_cast this
  linarith

/-- The colours shared by `v, u, w` are at least those shared by `v, u` plus those shared by
`v, w`, minus the `k` colours of `v`. -/
theorem listDeficiency_triple_le {L : ListAssignment V} {k : ℕ} (hL : IsNListAssignment L k)
    (v u w : V) :
    listDeficiency L k {v, u, w} ≤ listDeficiency L k {v, u} + listDeficiency L k {v, w} := by
  unfold listDeficiency
  have h3 : listInter L {v, u, w} = (L u ∩ L v) ∩ (L w ∩ L v) := by
    rw [listInter_insert L (Finset.insert_nonempty u {w}),
      listInter_insert L (Finset.singleton_nonempty w), listInter_singleton]
    ext a; simp only [Finset.mem_inter]; tauto
  have h2u : listInter L {v, u} = L u ∩ L v := by
    rw [listInter_insert L (Finset.singleton_nonempty u), listInter_singleton]
  have h2w : listInter L {v, w} = L w ∩ L v := by
    rw [listInter_insert L (Finset.singleton_nonempty w), listInter_singleton]
  rw [h3, h2u, h2w]
  have hun := Finset.card_union_add_card_inter (L u ∩ L v) (L w ∩ L v)
  have hsub : (L u ∩ L v) ∪ (L w ∩ L v) ⊆ L v := Finset.union_subset
    Finset.inter_subset_right Finset.inter_subset_right
  have hle := Finset.card_le_card hsub
  rw [hL v] at hle
  have : ((L u ∩ L v).card : ℝ) + (L w ∩ L v).card ≤
      k + ((L u ∩ L v) ∩ (L w ∩ L v)).card := by exact_mod_cast (by omega)
  linarith

/-! ### Activities of small blocks -/

theorem graphActivity_pair_of_adj {L : ListAssignment V} {k : ℕ} (x t : ℝ) {v u : V}
    (h : G.Adj v u) :
    graphActivity G L k x {v, u} t = -(((k : ℝ) - t * listDeficiency L k {v, u}) * x ^ 2) := by
  rw [graphActivity, blockCoefficient_pair_of_adj G h, Finset.card_pair h.ne]
  ring

theorem graphActivity_pair_of_not_adj {L : ListAssignment V} {k : ℕ} (x t : ℝ) {v u : V}
    (hvu : v ≠ u) (h : ¬ G.Adj v u) : graphActivity G L k x {v, u} t = 0 := by
  rw [graphActivity, blockCoefficient_pair_of_not_adj G hvu h]
  ring

/-- **The neighbour-pair activity.** -/
theorem graphActivity_triple_ge {L : ListAssignment V} {k : ℕ} (hL : IsNListAssignment L k)
    {x t : ℝ} (hx : 0 ≤ x) (ht : t ∈ Set.Icc (0 : ℝ) 1) {v u w : V} (hu : G.Adj v u)
    (hw : G.Adj v w) (huw : u ≠ w) :
    ((k : ℝ) - t * (listDeficiency L k {v, u} + listDeficiency L k {v, w})) * x ^ 3 ≤
      graphActivity G L k x {v, u, w} t := by
  have hcard : ({v, u, w} : Finset V).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hu.ne, hw.ne]), Finset.card_pair huw]
  have hf : 0 ≤ (k : ℝ) - t * listDeficiency L k {v, u, w} :=
    (interpolation_factor_bounds hL ⟨v, by simp⟩ ht).1
  have hc := one_le_blockCoefficient_triple G hu hw huw
  have hd := listDeficiency_triple_le hL v u w
  rw [graphActivity, hcard]
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hx 3)
  have : (k : ℝ) - t * (listDeficiency L k {v, u} + listDeficiency L k {v, w}) ≤
      (k : ℝ) - t * listDeficiency L k {v, u, w} := by
    nlinarith [ht.1]
  nlinarith

/-! ### The root budget with `n` ports -/

/-- The odd mass at a root of degree at most `n`. -/
theorem walkTreeOddMass_cert_root_le_ports {D : ℕ} (hdeg : ∀ v, G.degree v ≤ D)
    {x₀ e o r : ℝ} (hc : ParityCert D x₀ e o r) {x : ℝ} (hx : 0 ≤ x) (hxx : x ≤ x₀)
    (h : ℕ) {v : V} {n : ℕ} (hv : G.degree v ≤ n) :
    walkTreeOddMass G x h none v ≤ (parityPower (1 + x₀ * o) (x₀ * e) n).2 := by
  have hpow := (parityPower_nonneg (a := 1 + x₀ * o) (b := x₀ * e)
    (by have := mul_nonneg hc.x₀_nonneg hc.o_nonneg; linarith)
    (mul_nonneg hc.x₀_nonneg hc.e_nonneg) n).2
  cases h with
  | zero => norm_num [walkTreeOddMass]; exact hpow
  | succ h =>
    have hw : ∀ w : childPorts G none v, _ := fun w =>
      have hb := walkTreeParity_cert_branch_bounds G hdeg hc hx hxx h
        ((mem_childPorts G).mp w.2).1.symm
      childFactor_cert_bounds hx hxx hb.1 hb.2
    have hcard : (childPorts G none v).card ≤ n := by
      have : childPorts G none v = G.neighborFinset v := by
        ext w; simp [childPorts]
      rw [this, card_neighborFinset_eq_degree]; exact hv
    have hh := parityProduct_cert_bounds Finset.univ _ _ hc.x₀_nonneg hc.e_nonneg hc.o_nonneg
      (by simpa using hcard) (fun w _ => (hw w).1) (fun w _ => (hw w).2)
    rw [(walkTreeParity_succ G x h none v).2]
    exact hh.2.2

/-- The tree-count bound on an even block's activity, the quantity the root budget sums. -/
noncomputable def rootHarm (k : ℕ) (x : ℝ) (S : Finset V) : ℝ :=
  if Even S.card then (k : ℝ) * x * ∑ _T ∈ spanningTreeSets G S, x ^ (S.card - 1) else 0

theorem rootHarm_nonneg (k : ℕ) {x : ℝ} (hx : 0 ≤ x) (S : Finset V) :
    0 ≤ rootHarm G k x S := by
  unfold rootHarm
  split_ifs
  · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hx)
      (Finset.sum_nonneg fun _ _ => pow_nonneg hx _)
  · exact le_rfl

/-- Every block's activity is at least minus its harm. -/
theorem neg_rootHarm_le {L : ListAssignment V} {k : ℕ} (hL : IsNListAssignment L k)
    {x t : ℝ} (hx : 0 ≤ x) (ht : t ∈ Set.Icc (0 : ℝ) 1) {S : Finset V} (hS : S.Nonempty) :
    -rootHarm G k x S ≤ graphActivity G L k x S t := by
  have h := neg_graphActivityPenalty_le G hL hx ht S
  refine le_trans ?_ h
  unfold graphActivityPenalty rootHarm
  split_ifs
  · exact neg_le_neg (graphActivity_abs_le G hL hx ht hS)
  · exact le_rfl

/-- **The root harm with `n` ports in `U`.** -/
theorem rootHarm_sum_le {D : ℕ} (hdeg : ∀ v, G.degree v ≤ D)
    {x₀ e o r : ℝ} (hc : ParityCert D x₀ e o r) (k : ℕ) {x : ℝ} (hx : 0 ≤ x) (hxx : x ≤ x₀)
    (U : Finset V) {v : V} (hv : v ∈ U) {n : ℕ} (hn : (U.filter (G.Adj v)).card ≤ n) :
    ∑ S ∈ rootedBlocks U v, rootHarm G k x S ≤
      (k : ℝ) * x * (parityPower (1 + x₀ * o) (x₀ * e) n).2 := by
  classical
  have hdegU : ∀ w, (restrictTo G U).degree w ≤ D := fun w =>
    (restrictTo_degree_le G U w).trans (hdeg w)
  have hvdeg : (restrictTo G U).degree v ≤ n := by
    rw [restrictTo_degree_eq G hv]; exact hn
  simp only [rootHarm, ← Finset.sum_filter]
  calc
    _ = (k : ℝ) * x * (∑ S ∈ (rootedBlocks U v).filter (fun S => Even S.card),
        ∑ _T ∈ spanningTreeSets (restrictTo G U) S, x ^ (S.card - 1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S hS
      rw [spanningTreeSets_restrictTo G (mem_rootedBlocks (Finset.mem_filter.mp hS).1).1]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Nat.cast_nonneg _) hx)
      exact (even_rooted_tree_sum_le_oddMass (restrictTo G U) hx U v).trans
        (walkTreeOddMass_cert_root_le_ports (restrictTo G U) hdegU hc hx hxx _ hvdeg)

end GridGen.Polymer
