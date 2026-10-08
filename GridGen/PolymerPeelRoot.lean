/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.PolymerPeelGraph
import GridGen.PolymerParityActivity

/-!
# The root budget at a vertex of residual degree at most `D - 1`

The harmful rooted mass at `v` inside `U` only sees trees inside `U`, so it is bounded by the walk
trees of `G` restricted to `U`, where the root has `|N(v) ∩ U|` ports. With at most `D - 1` ports
the root is no worse than a branch node, so its odd mass is at most the certificate's branch odd
mass `o` instead of the root mass `r`.
-/

namespace GridGen.Polymer

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The odd mass at a root of degree at most `D - 1` is at most the branch odd mass. -/
theorem walkTreeOddMass_cert_root_le_of_degree {D : ℕ} (hdeg : ∀ v, G.degree v ≤ D)
    {x₀ e o r : ℝ} (hc : ParityCert D x₀ e o r) {x : ℝ} (hx : 0 ≤ x) (hxx : x ≤ x₀)
    (h : ℕ) {v : V} (hv : G.degree v ≤ D - 1) : walkTreeOddMass G x h none v ≤ o := by
  cases h with
  | zero =>
    norm_num [walkTreeOddMass]
    exact hc.o_nonneg
  | succ h =>
    have hw : ∀ w : childPorts G none v, _ := fun w =>
      have hb := walkTreeParity_cert_branch_bounds G hdeg hc hx hxx h
        ((mem_childPorts G).mp w.2).1.symm
      childFactor_cert_bounds hx hxx hb.1 hb.2
    have hcard : (childPorts G none v).card ≤ D - 1 := by
      have : childPorts G none v = G.neighborFinset v := by
        ext w; simp [childPorts]
      rw [this, card_neighborFinset_eq_degree]; exact hv
    have hh := parityProduct_cert_bounds Finset.univ _ _ hc.x₀_nonneg hc.e_nonneg hc.o_nonneg
      (by simpa using hcard) (fun w _ => (hw w).1) (fun w _ => (hw w).2)
    rw [(walkTreeParity_succ G x h none v).2]
    exact hh.2.2.trans hc.branch.2

/-- `G` with only the edges inside `U`. -/
def restrictTo (U : Finset V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ a ∈ U ∧ b ∈ U
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun a h => G.loopless.irrefl a h.1⟩

instance (U : Finset V) : DecidableRel (restrictTo G U).Adj := fun a b =>
  inferInstanceAs (Decidable (G.Adj a b ∧ a ∈ U ∧ b ∈ U))

theorem restrictTo_degree_le (U : Finset V) (w : V) : (restrictTo G U).degree w ≤ G.degree w := by
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro y hy
  rw [mem_neighborFinset] at hy ⊢
  exact hy.1

theorem restrictTo_degree_eq {U : Finset V} {v : V} (hv : v ∈ U) :
    (restrictTo G U).degree v = (U.filter (G.Adj v)).card := by
  rw [← card_neighborFinset_eq_degree]
  congr 1
  ext y
  simp only [mem_neighborFinset, Finset.mem_filter]
  change (G.Adj v y ∧ v ∈ U ∧ y ∈ U) ↔ _
  tauto

theorem edgesWithin_restrictTo {U S : Finset V} (hSU : S ⊆ U) :
    edgesWithin (restrictTo G U).edgeFinset S = edgesWithin G.edgeFinset S := by
  ext e
  induction e using Sym2.inductionOn with
  | hf a b =>
    simp only [mem_edgesWithin, mem_edgeFinset, mem_edgeSet, Sym2.mem_iff]
    constructor
    · rintro ⟨h, hS⟩; exact ⟨h.1, hS⟩
    · rintro ⟨h, hS⟩
      exact ⟨⟨h, hSU (hS a (Or.inl rfl)), hSU (hS b (Or.inr rfl))⟩, hS⟩

theorem spanningTreeSets_restrictTo {U S : Finset V} (hSU : S ⊆ U) :
    spanningTreeSets (restrictTo G U) S = spanningTreeSets G S := by
  unfold spanningTreeSets blockEdgeSets
  rw [edgesWithin_restrictTo G hSU]

/-- **The harmful root mass at a vertex with at most `D - 1` neighbours in `U`.** -/
theorem graphActivity_cert_root_bound_small {D : ℕ} (hdeg : ∀ v, G.degree v ≤ D)
    {x₀ e o r : ℝ} (hc : ParityCert D x₀ e o r)
    {L : ListAssignment V} {k : ℕ} (hL : IsNListAssignment L k)
    {x t : ℝ} (hx : 0 ≤ x) (hxx : x ≤ x₀)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (U : Finset V) {v : V} (hv : v ∈ U)
    (hsmall : smallIn G (D - 1) U v) :
    (∑ S ∈ rootedBlocks U v, graphActivityPenalty G L k x S t) ≤ (k : ℝ) * x * o := by
  classical
  have hdegU : ∀ w, (restrictTo G U).degree w ≤ D := fun w =>
    (restrictTo_degree_le G U w).trans (hdeg w)
  have hvdeg : (restrictTo G U).degree v ≤ D - 1 := by
    rw [restrictTo_degree_eq G hv]; exact hsmall
  simp only [graphActivityPenalty, ← Finset.sum_filter]
  calc
    _ ≤ ∑ S ∈ (rootedBlocks U v).filter (fun S => Even S.card),
        (k : ℝ) * x * (∑ _T ∈ spanningTreeSets G S, x ^ (S.card - 1)) := by
      apply Finset.sum_le_sum
      intro S hS
      exact graphActivity_abs_le G hL hx ht
        ⟨v, (mem_rootedBlocks (Finset.mem_filter.mp hS).1).2.1⟩
    _ = (k : ℝ) * x * (∑ S ∈ (rootedBlocks U v).filter (fun S => Even S.card),
        ∑ _T ∈ spanningTreeSets (restrictTo G U) S, x ^ (S.card - 1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S hS
      rw [spanningTreeSets_restrictTo G (mem_rootedBlocks (Finset.mem_filter.mp hS).1).1]
    _ ≤ (k : ℝ) * x * o := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Nat.cast_nonneg _) hx)
      exact (even_rooted_tree_sum_le_oddMass (restrictTo G U) hx U v).trans
        (walkTreeOddMass_cert_root_le_of_degree (restrictTo G U) hdegU
          hc hx hxx _ hvdeg)

end GridGen.Polymer
