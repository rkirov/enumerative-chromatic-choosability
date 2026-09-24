import GridGen.PolymerActivity
import GridGen.PolymerSigns
import GridGen.PolymerParityCount

/-! # One-sided root budget and positivity under a parity certificate

Odd-sized blocks have nonnegative activity, so only even-sized blocks are charged to the
root; their penalty is at most `k x r` for a `ParityCert` with root bound `r`. -/

namespace GridGen.Polymer

open SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def graphActivityPenalty (L : ListAssignment V) (k : ℕ) (x : ℝ)
    (S : Finset V) (t : ℝ) : ℝ :=
  if Even S.card then |graphActivity G L k x S t| else 0

theorem graphActivityPenalty_nonneg (L : ListAssignment V) (k : ℕ) (x : ℝ)
    (S : Finset V) (t : ℝ) : 0 ≤ graphActivityPenalty G L k x S t := by
  unfold graphActivityPenalty
  split_ifs <;> positivity

theorem neg_graphActivityPenalty_le {L : ListAssignment V} {k : ℕ}
    (hL : IsNListAssignment L k) {x t : ℝ} (hx : 0 ≤ x)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (S : Finset V) :
    -graphActivityPenalty G L k x S t ≤ graphActivity G L k x S t := by
  unfold graphActivityPenalty
  split_ifs with he
  · exact neg_abs_le _
  · have ho : Odd S.card := (Nat.even_or_odd S.card).resolve_left he
    have hn : S.Nonempty := Finset.card_pos.mp ho.pos
    have hc := blockCoefficient_nonneg_of_odd G S ho
    have hf := (interpolation_factor_bounds hL hn ht).1
    simpa only [neg_zero, graphActivity] using
      mul_nonneg (mul_nonneg hc hf) (pow_nonneg hx S.card)

theorem graphActivity_cert_root_bound {D : ℕ} (hdeg : ∀ v, G.degree v ≤ D)
    {x₀ e o r : ℝ} (hc : ParityCert D x₀ e o r)
    {L : ListAssignment V} {k : ℕ} (hL : IsNListAssignment L k)
    {x t : ℝ} (hx : 0 ≤ x) (hxx : x ≤ x₀)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (U : Finset V) (v : V) :
    (∑ S ∈ rootedBlocks U v, graphActivityPenalty G L k x S t) ≤ (k : ℝ) * x * r := by
  classical
  simp only [graphActivityPenalty, ← Finset.sum_filter]
  calc
    _ ≤ ∑ S ∈ (rootedBlocks U v).filter (fun S => Even S.card),
        (k : ℝ) * x * (∑ _T ∈ spanningTreeSets G S, x ^ (S.card - 1)) := by
      apply Finset.sum_le_sum
      intro S hS
      exact graphActivity_abs_le G hL hx ht
        ⟨v, (mem_rootedBlocks (Finset.mem_filter.mp hS).1).2.1⟩
    _ = (k : ℝ) * x * (∑ S ∈ (rootedBlocks U v).filter (fun S => Even S.card),
        ∑ _T ∈ spanningTreeSets G S, x ^ (S.card - 1)) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (even_rooted_tree_sum_cert_le G hdeg hc hx hxx U v)
      (mul_nonneg (Nat.cast_nonneg _) hx)

/-- Positivity and deletion monotonicity of the normalized interpolation, whenever the
root penalty `k x r` fits inside the singleton surplus `k x - 1`. -/
theorem graphActivity_cert_positive_mono {D : ℕ} (hdeg : ∀ v, G.degree v ≤ D)
    {x₀ e o r : ℝ} (hc : ParityCert D x₀ e o r)
    {L : ListAssignment V} {k : ℕ} (hL : IsNListAssignment L k)
    {x : ℝ} (hx : 0 ≤ x) (hxx : x ≤ x₀) (hbudget : (k : ℝ) * x * r ≤ (k : ℝ) * x - 1)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (U : Finset V) :
    0 < partitionSum (fun S => graphActivity G L k x S t) U ∧
      ∀ B ⊆ U,
        partitionSum (fun S => graphActivity G L k x S t) B ≤
          partitionSum (fun S => graphActivity G L k x S t) U := by
  apply partitionSum_positive_mono _
    (fun S => graphActivityPenalty G L k x S t) ((k : ℝ) * x)
  · intro v
    rw [graphActivity_singleton G hL]
  · exact fun S => graphActivityPenalty_nonneg G L k _ S t
  · exact neg_graphActivityPenalty_le G hL hx ht
  · intro B v _
    exact (graphActivity_cert_root_bound G hdeg hc hL hx hxx ht B v).trans hbudget

end GridGen.Polymer
