import GridGen.PolymerParityActivity
import GridGen.PolymerAnchors

/-! # Parity-restricted derivative charging under a parity certificate

Only odd-sized blocks of size at least three can make the derivative negative. Their
deficiencies are charged to the anchor edges of individual spanning trees, and a
`ParityCert` bounds the total charge on each anchor by the anchor's own term. -/

namespace GridGen.Polymer

open SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem graphTreeCharge_odd_budget {D : ℕ} (hdeg : ∀ v, G.degree v ≤ D)
    {x₀ e₀ o₀ r₀ : ℝ} (hc : ParityCert D x₀ e₀ o₀ r₀)
    (L : ListAssignment V) (k : ℕ) {x : ℝ} (hx : 0 ≤ x) (hxb : x ≤ x₀)
    (U : Finset V) {e : Sym2 V} (he : e ∈ G.edgeFinset) :
    (∑ S ∈ U.powerset.filter (fun S => 3 ≤ S.card ∧ Odd S.card), graphTreeCharge G L k x S e) ≤
      (2 * e₀ * o₀) * ((edgeDef L k e : ℝ) * x ^ 2) := by
  classical
  induction e using Sym2.inductionOn with
  | hf u v =>
    have huv : G.Adj u v := G.mem_edgeFinset.mp he
    have hh := odd_edge_tree_sum_cert_le G hdeg hc hx hxb U huv
    have hf : 0 ≤ (edgeDef L k s(u, v) : ℝ) * x ^ 2 := by positivity
    calc
      _ = ((edgeDef L k s(u, v) : ℝ) * x ^ 2) *
          (∑ S ∈ U.powerset.filter (fun S => 3 ≤ S.card ∧ Odd S.card),
            ∑ _T ∈ (spanningTreeSets G S).filter (fun T => s(u, v) ∈ T),
              x ^ (S.card - 2)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro S hS
        unfold graphTreeCharge
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro T _
        have hcard : S.card - 2 + 2 = S.card := by
          have := (Finset.mem_filter.mp hS).2
          omega
        have hpow : x ^ S.card = x ^ (S.card - 2) * x ^ 2 := by rw [← pow_add, hcard]
        rw [hpow]
        ring
      _ ≤ ((edgeDef L k s(u, v) : ℝ) * x ^ 2) * (2 * e₀ * o₀) :=
        mul_le_mul_of_nonneg_left hh hf
      _ = _ := by ring

theorem graphActivity_odd_charged_tail {D : ℕ} (hdeg : ∀ v, G.degree v ≤ D)
    {x₀ e₀ o₀ r₀ : ℝ} (hc : ParityCert D x₀ e₀ o₀ r₀)
    {L : ListAssignment V} {k : ℕ} (hL : IsNListAssignment L k)
    {x : ℝ} (hx : 0 ≤ x) (hxb : x ≤ x₀) (U : Finset V)
    (z : Finset V → ℝ) (hz : ∀ A, 0 ≤ z A)
    (hmono : ∀ A B, A ⊆ B → z A ≤ z B) :
    (∑ S ∈ U.powerset.filter (fun S => 3 ≤ S.card ∧ Odd S.card),
      -graphActivityDeriv G L k x S * z (U \ S)) ≤
      (2 * e₀ * o₀) * ∑ e ∈ edgesWithin G.edgeFinset U,
        (edgeDef L k e : ℝ) * x ^ 2 * z (U \ e.toFinset) := by
  classical
  have hcoeff : ∀ S ∈ U.powerset.filter (fun S => 3 ≤ S.card ∧ Odd S.card),
      -graphActivityDeriv G L k x S ≤
        ∑ e ∈ edgesWithin G.edgeFinset U, graphTreeCharge G L k x S e := by
    intro S hS
    obtain ⟨hSU, hcard⟩ := Finset.mem_filter.mp hS
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    have hh := mul_le_mul_of_nonneg_right (le_abs_self (blockCoefficient G S))
      (mul_nonneg (listDeficiency_nonneg hL hne) (pow_nonneg hx S.card))
    have hc := coefficient_deficiency_le_graphTreeCharge G hL hx
      (Finset.mem_powerset.mp hSU) hne
    simp only [graphActivityDeriv, neg_mul, neg_neg]
    apply le_trans ?_ hc
    simpa only [mul_assoc] using hh
  calc
    _ ≤ ∑ S ∈ U.powerset.filter (fun S => 3 ≤ S.card ∧ Odd S.card),
        (∑ e ∈ edgesWithin G.edgeFinset U, graphTreeCharge G L k x S e) * z (U \ S) := by
      exact Finset.sum_le_sum fun S hS => mul_le_mul_of_nonneg_right (hcoeff S hS) (hz _)
    _ = ∑ e ∈ edgesWithin G.edgeFinset U,
        ∑ S ∈ U.powerset.filter (fun S => 3 ≤ S.card ∧ Odd S.card),
          graphTreeCharge G L k x S e * z (U \ S) := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
    _ ≤ ∑ e ∈ edgesWithin G.edgeFinset U,
        ∑ S ∈ U.powerset.filter (fun S => 3 ≤ S.card ∧ Odd S.card),
          graphTreeCharge G L k x S e * z (U \ e.toFinset) := by
      apply Finset.sum_le_sum
      intro e he
      apply Finset.sum_le_sum
      intro S hS
      by_cases hc : graphTreeCharge G L k x S e = 0
      · simp [hc]
      · apply mul_le_mul_of_nonneg_left _ (graphTreeCharge_nonneg G L k hx S e)
        apply hmono
        have hs := (mem_edgesWithin.mp (graphTreeCharge_support G L k x S e hc)).2
        intro v hv
        obtain ⟨hvU, hvS⟩ := Finset.mem_sdiff.mp hv
        exact Finset.mem_sdiff.mpr ⟨hvU, fun hve => hvS (hs v (Sym2.mem_toFinset.mp hve))⟩
    _ ≤ ∑ e ∈ edgesWithin G.edgeFinset U,
        ((2 * e₀ * o₀) * ((edgeDef L k e : ℝ) * x ^ 2)) * z (U \ e.toFinset) := by
      apply Finset.sum_le_sum
      intro e he
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right
        (graphTreeCharge_odd_budget G hdeg hc L k hx hxb U (mem_edgesWithin.mp he).1) (hz _)
    _ = _ := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring


theorem graphActivity_parity_charged_tail {D : ℕ} (hdeg : ∀ v, G.degree v ≤ D)
    {x₀ e₀ o₀ r₀ : ℝ} (hc : ParityCert D x₀ e₀ o₀ r₀)
    {L : ListAssignment V} {k : ℕ} (hL : IsNListAssignment L k)
    {x : ℝ} (hx : 0 ≤ x) (hxb : x ≤ x₀) (U : Finset V)
    (z : Finset V → ℝ) (hz : ∀ A, 0 ≤ z A)
    (hmono : ∀ A B, A ⊆ B → z A ≤ z B) :
    (∑ S ∈ U.powerset.filter (fun S => 3 ≤ S.card),
      -graphActivityDeriv G L k x S * z (U \ S)) ≤
      (2 * e₀ * o₀) * ∑ e ∈ edgesWithin G.edgeFinset U,
        (edgeDef L k e : ℝ) * x ^ 2 * z (U \ e.toFinset) := by
  classical
  apply le_trans ?_ (graphActivity_odd_charged_tail G hdeg hc hL hx hxb U z hz hmono)
  rw [← Finset.filter_filter]
  conv_rhs => rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro S hS
  split_ifs with ho
  · exact le_rfl
  · have he : Even S.card := (Nat.even_or_odd S.card).resolve_right ho
    have hn : S.Nonempty := Finset.card_pos.mp (by
      have := (Finset.mem_filter.mp hS).2
      omega)
    have hc := blockCoefficient_nonpos_of_even G S he hn
    have hd := listDeficiency_nonneg hL hn
    simp only [graphActivityDeriv, neg_mul, neg_neg]
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hc hd) (pow_nonneg hx _)) (hz _)

/-- The derivative keeps a fraction `1 - 2eo` of its positive edge terms. -/
theorem graphActivity_cert_derivative_sum_lower_bound {D : ℕ} (hdeg : ∀ v, G.degree v ≤ D)
    {x₀ e o r : ℝ} (hc : ParityCert D x₀ e o r)
    {L : ListAssignment V} {k : ℕ} (hL : IsNListAssignment L k)
    {x : ℝ} (hx : 0 ≤ x) (hxx : x ≤ x₀) (hbudget : (k : ℝ) * x * r ≤ (k : ℝ) * x - 1)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (U : Finset V) :
    (1 - 2 * e * o) * ∑ f ∈ edgesWithin G.edgeFinset U,
        (edgeDef L k f : ℝ) * x ^ 2 * partitionSum (fun T => graphActivity G L k x T t)
          (U \ f.toFinset) ≤
      ∑ S ∈ blocks U, graphActivityDeriv G L k x S *
        partitionSum (fun T => graphActivity G L k x T t) (U \ S) := by
  classical
  let z := partitionSum (fun T => graphActivity G L k x T t)
  have hp := graphActivity_cert_positive_mono G hdeg hc hL hx hxx hbudget ht
  have hz : ∀ A, 0 ≤ z A := fun A => (hp A).1.le
  have hm : ∀ A B, A ⊆ B → z A ≤ z B := fun A B hAB => (hp B).2 A hAB
  have htail := graphActivity_parity_charged_tail G hdeg hc hL hx hxx U z hz hm
  have hsplit := Finset.sum_filter_add_sum_filter_not (blocks U) (fun S => S.card ≤ 2)
    (fun S => graphActivityDeriv G L k x S * z (U \ S))
  rw [small_derivative_sum_eq_edges G hL, blocks_filter_large] at hsplit
  simp only [neg_mul, Finset.sum_neg_distrib] at htail
  change (1 - 2 * e * o) * ∑ f ∈ edgesWithin G.edgeFinset U,
    (edgeDef L k f : ℝ) * x ^ 2 * z (U \ f.toFinset) ≤ _
  linarith

theorem graphActivity_cert_derivative_sum_nonneg {D : ℕ} (hdeg : ∀ v, G.degree v ≤ D)
    {x₀ e o r : ℝ} (hc : ParityCert D x₀ e o r)
    {L : ListAssignment V} {k : ℕ} (hL : IsNListAssignment L k)
    {x : ℝ} (hx : 0 ≤ x) (hxx : x ≤ x₀) (hbudget : (k : ℝ) * x * r ≤ (k : ℝ) * x - 1)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (U : Finset V) :
    0 ≤ ∑ S ∈ blocks U, graphActivityDeriv G L k x S *
      partitionSum (fun T => graphActivity G L k x T t) (U \ S) := by
  have hp := graphActivity_cert_positive_mono G hdeg hc hL hx hxx hbudget ht
  refine le_trans (mul_nonneg (by linarith [hc.edge]) (Finset.sum_nonneg fun f _ => ?_))
    (graphActivity_cert_derivative_sum_lower_bound G hdeg hc hL hx hxx hbudget ht U)
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) (hp _).1.le

end GridGen.Polymer
