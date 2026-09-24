import GridGen.PolymerParityBounds
import GridGen.PolymerEdgeEncoding
import GridGen.PolymerRatio
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! # Parity-restricted counts of actual embedded trees

The weight-preserving injections of actual spanning trees into walk-tree codes, restricted
by parity, and the resulting budgets under a `ParityCert`. -/

namespace GridGen.Polymer

open SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem even_rooted_tree_sum_le_oddMass {x : ℝ} (hx : 0 ≤ x)
    (U : Finset V) (v : V) :
    (∑ S ∈ (rootedBlocks U v).filter (fun S => Even S.card), ∑ _T ∈ spanningTreeSets G S, x ^ (S.card - 1)) ≤
      walkTreeOddMass G x (Fintype.card V) none v := by
  classical
  let ts := ((rootedBlocks U v).filter (fun S => Even S.card)).sigma (spanningTreeSets G)
  let enc : (Σ _S : Finset V, Finset (Sym2 V)) →
      WalkTreeCode G (Fintype.card V) none v := fun t =>
    unfoldWalkTree G (edgeGraph t.2) (Fintype.card V) none v
  have hvS {S : Finset V} (hS : S ∈ (rootedBlocks U v).filter (fun S => Even S.card)) : v ∈ S := by
    exact (mem_rootedBlocks (Finset.mem_filter.mp hS).1).2.1
  have hsize {t : Σ _S : Finset V, Finset (Sym2 V)} (ht : t ∈ ts) :
      walkTreeSize G (enc t) = t.1.card - 1 := by
    have h := Finset.mem_sigma.mp ht
    exact spanningTree_unfold_size G h.2 (hvS h.1)
  have hinj : Set.InjOn enc ts := by
    intro a ha b hb he
    have ha' := Finset.mem_sigma.mp ha
    have hb' := Finset.mem_sigma.mp hb
    have hh := spanningTree_unfold_injective G ha'.2 hb'.2 (hvS ha'.1) (hvS hb'.1) he
    cases a; cases b
    simp_all
  have hsub : ts.image enc ⊆ Finset.univ.filter
      (fun c : WalkTreeCode G (Fintype.card V) none v => Odd (walkTreeSize G c)) := by
    intro c hc
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hc
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hsize ht]
    have hs := Finset.mem_filter.mp (Finset.mem_sigma.mp ht).1
    have hcard := (mem_rootedBlocks hs.1).2.2
    obtain ⟨n, hn⟩ := hs.2
    exact ⟨n - 1, by omega⟩
  calc
    _ = ∑ t ∈ ts, x ^ walkTreeSize G (enc t) := by
      rw [Finset.sum_sigma']
      apply Finset.sum_congr rfl
      intro t ht
      rw [hsize ht]
    _ = ∑ c ∈ ts.image enc, x ^ walkTreeSize G c := (Finset.sum_image (f := fun c : WalkTreeCode G (Fintype.card V) none v =>
        x ^ walkTreeSize G c) hinj).symm
    _ ≤ ∑ c ∈ Finset.univ.filter (fun c : WalkTreeCode G (Fintype.card V) none v => Odd (walkTreeSize G c)),
        x ^ walkTreeSize G c :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => pow_nonneg hx _)
    _ = _ := sum_odd_walkTreeCodes G x _ _ _

noncomputable def edgeOddMass (x : ℝ) (h : ℕ) (u v : V) : ℝ :=
  walkTreeEvenMass G x h (some v) u * walkTreeOddMass G x h (some u) v +
    walkTreeOddMass G x h (some v) u * walkTreeEvenMass G x h (some u) v

theorem sum_odd_edgeCodes (x : ℝ) (h : ℕ) (u v : V) :
    (∑ c ∈ Finset.univ.filter (fun c : EdgeWalkTreeCode G h u v =>
      Odd (edgeCodeSize G c)), x ^ edgeCodeSize G c) = edgeOddMass G x h u v := by
  rw [sum_odd_powers, sum_edgeCode_weights, sum_edgeCode_weights]
  unfold edgeOddMass walkTreeEvenMass walkTreeOddMass
  ring

theorem odd_edge_tree_sum_le_oddMass {x : ℝ} (hx : 0 ≤ x)
    (U : Finset V) (u v : V) :
    (∑ S ∈ U.powerset.filter (fun S => 3 ≤ S.card ∧ Odd S.card),
      ∑ _T ∈ (spanningTreeSets G S).filter (fun T => s(u, v) ∈ T), x ^ (S.card - 2)) ≤
      edgeOddMass G x (Fintype.card V) u v := by
  classical
  let ts := (U.powerset.filter (fun S => 3 ≤ S.card ∧ Odd S.card)).sigma
    (fun S => (spanningTreeSets G S).filter (fun T => s(u, v) ∈ T))
  let enc : (Σ _S : Finset V, Finset (Sym2 V)) →
      EdgeWalkTreeCode G (Fintype.card V) u v := fun t =>
    unfoldEdgeTree G (edgeGraph t.2) (Fintype.card V) u v
  have hsize {t : Σ _S : Finset V, Finset (Sym2 V)} (ht : t ∈ ts) :
      edgeCodeSize G (enc t) = t.1.card - 2 := by
    have h := Finset.mem_filter.mp (Finset.mem_sigma.mp ht).2
    exact spanningTree_edge_unfold_size G h.1 h.2
  have hinj : Set.InjOn enc ts := by
    intro a ha b hb he
    have ha' := Finset.mem_filter.mp (Finset.mem_sigma.mp ha).2
    have hb' := Finset.mem_filter.mp (Finset.mem_sigma.mp hb).2
    have hh := spanningTree_edge_unfold_injective G ha'.1 hb'.1 ha'.2 hb'.2 he
    cases a; cases b
    simp_all
  have hsub : ts.image enc ⊆ Finset.univ.filter
      (fun c : EdgeWalkTreeCode G (Fintype.card V) u v => Odd (edgeCodeSize G c)) := by
    intro c hc
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hc
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hsize ht]
    have hs := (Finset.mem_filter.mp (Finset.mem_sigma.mp ht).1).2
    obtain ⟨n, hn⟩ := hs.2
    exact ⟨n - 1, by omega⟩
  calc
    _ = ∑ t ∈ ts, x ^ edgeCodeSize G (enc t) := by
      rw [Finset.sum_sigma']
      apply Finset.sum_congr rfl
      intro t ht
      rw [hsize ht]
    _ = ∑ c ∈ ts.image enc, x ^ edgeCodeSize G c :=
      (Finset.sum_image (f := fun c : EdgeWalkTreeCode G (Fintype.card V) u v =>
        x ^ edgeCodeSize G c) hinj).symm
    _ ≤ ∑ c ∈ Finset.univ.filter (fun c : EdgeWalkTreeCode G (Fintype.card V) u v => Odd (edgeCodeSize G c)),
        x ^ edgeCodeSize G c :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => pow_nonneg hx _)
    _ = _ := sum_odd_edgeCodes G x _ _ _

theorem edgeOddMass_cert_le {D : ℕ} (hdeg : ∀ v, G.degree v ≤ D)
    {x₀ e o r : ℝ} (hc : ParityCert D x₀ e o r) {x : ℝ} (hx : 0 ≤ x) (hxx : x ≤ x₀)
    (h : ℕ) {u v : V} (huv : G.Adj u v) : edgeOddMass G x h u v ≤ 2 * e * o := by
  have hu := walkTreeParity_cert_branch_bounds G hdeg hc hx hxx h huv
  have hv := walkTreeParity_cert_branch_bounds G hdeg hc hx hxx h huv.symm
  have h₁ := mul_le_mul hu.1.2 hv.2.2 hv.2.1 hc.e_nonneg
  have h₂ := mul_le_mul hu.2.2 hv.1.2 hv.1.1 hc.o_nonneg
  unfold edgeOddMass
  linarith

/-- The root budget: nontrivial even-sized blocks at a root, weighted by their spanning trees. -/
theorem even_rooted_tree_sum_cert_le {D : ℕ} (hdeg : ∀ v, G.degree v ≤ D)
    {x₀ e o r : ℝ} (hc : ParityCert D x₀ e o r) {x : ℝ} (hx : 0 ≤ x) (hxx : x ≤ x₀)
    (U : Finset V) (v : V) :
    (∑ S ∈ (rootedBlocks U v).filter (fun S => Even S.card),
      ∑ _T ∈ spanningTreeSets G S, x ^ (S.card - 1)) ≤ r :=
  (even_rooted_tree_sum_le_oddMass G hx U v).trans
    (walkTreeOddMass_cert_root_le G hdeg hc hx hxx _ v)

/-- The edge-rooted tail: odd-sized blocks of size at least three whose trees use the anchor. -/
theorem odd_edge_tree_sum_cert_le {D : ℕ} (hdeg : ∀ v, G.degree v ≤ D)
    {x₀ e o r : ℝ} (hc : ParityCert D x₀ e o r) {x : ℝ} (hx : 0 ≤ x) (hxx : x ≤ x₀)
    (U : Finset V) {u v : V} (huv : G.Adj u v) :
    (∑ S ∈ U.powerset.filter (fun S => 3 ≤ S.card ∧ Odd S.card),
      ∑ _T ∈ (spanningTreeSets G S).filter (fun T => s(u, v) ∈ T), x ^ (S.card - 2)) ≤
      2 * e * o :=
  (odd_edge_tree_sum_le_oddMass G hx U u v).trans
    (edgeOddMass_cert_le G hdeg hc hx hxx _ huv)

end GridGen.Polymer
