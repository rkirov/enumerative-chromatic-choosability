import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Finite non-backtracking walk-tree codes

These codes allow repeated graph vertices on different branches. Thus they are a finite
overcounting space for embedded trees, not themselves embedded trees. The connection to
actual acyclic edge sets requires a separate weight-preserving injection.
-/

namespace GridGen.Polymer

open scoped BigOperators

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Neighbors available after excluding the predecessor, if one is specified. -/
def childPorts (p : Option V) (v : V) : Finset V :=
  (G.neighborFinset v).filter (fun w => some w ≠ p)

@[simp] theorem mem_childPorts {p : Option V} {v w : V} :
    w ∈ childPorts G p v ↔ G.Adj v w ∧ some w ≠ p := by
  simp [childPorts]

@[simp] theorem childPorts_none (v : V) :
    childPorts G none v = G.neighborFinset v := by
  ext w; simp

@[simp] theorem childPorts_some (p v : V) :
    childPorts G (some p) v = (G.neighborFinset v).erase p := by
  ext w; simp [and_comm]

/-- Depth-bounded trees in the non-backtracking walk tree of `G`. -/
def WalkTreeCode : ℕ → Option V → V → Type u
  | 0, _, _ => PUnit
  | h + 1, p, v => (w : childPorts G p v) → Option (WalkTreeCode h (some v) w.val)

noncomputable instance walkTreeCodeFintype :
    (h : ℕ) → (p : Option V) → (v : V) → Fintype (WalkTreeCode G h p v)
  | 0, _, _ => inferInstanceAs (Fintype PUnit)
  | h + 1, p, v => by
    letI := fun (w : childPorts G p v) => walkTreeCodeFintype h (some v) w.val
    exact inferInstanceAs (Fintype ((w : childPorts G p v) →
      Option (WalkTreeCode G h (some v) w.val)))

/-- Number of selected edges in a code, counted with their walk-tree multiplicity. -/
noncomputable def walkTreeSize : {h : ℕ} → {p : Option V} → {v : V} →
    WalkTreeCode G h p v → ℕ
  | 0, _, _, _ => 0
  | _h + 1, _, _, c => ∑ w, (c w).elim 0 (fun t => 1 + walkTreeSize t)

noncomputable def walkTreeMass (x : ℝ) (h : ℕ) (p : Option V) (v : V) : ℝ :=
  ∑ c : WalkTreeCode G h p v, x ^ walkTreeSize G c

@[simp] theorem walkTreeMass_zero (x : ℝ) (p : Option V) (v : V) :
    walkTreeMass G x 0 p v = 1 := by
  change (∑ _ : PUnit, (x : ℝ) ^ 0) = 1
  simp

theorem walkTreeMass_succ (x : ℝ) (h : ℕ) (p : Option V) (v : V) :
    walkTreeMass G x (h + 1) p v =
      ∏ w : childPorts G p v, (1 + x * walkTreeMass G x h (some v) w.val) := by
  classical
  unfold walkTreeMass
  change (∑ c : (w : childPorts G p v) → Option (WalkTreeCode G h (some v) w.val),
    x ^ (∑ w, (c w).elim 0 (fun t => 1 + walkTreeSize G t))) = _
  simp_rw [← Finset.prod_pow_eq_pow_sum]
  rw [← Fintype.prod_sum (fun (w : childPorts G p v)
    (t : Option (WalkTreeCode G h (some v) w.val)) =>
      x ^ t.elim 0 (fun c => 1 + walkTreeSize G c))]
  apply Finset.prod_congr rfl
  intro w _
  simp [Fintype.sum_option, pow_add, Finset.mul_sum]

theorem walkTreeMass_nonneg {x : ℝ} (hx : 0 ≤ x) (h : ℕ)
    (p : Option V) (v : V) : 0 ≤ walkTreeMass G x h p v := by
  exact Finset.sum_nonneg (fun _ _ => pow_nonneg hx _)

@[simp] theorem card_childPorts_some {p v : V} (hp : G.Adj v p) :
    (childPorts G (some p) v).card = G.degree v - 1 := by
  simp [Finset.card_erase_of_mem, hp]

end GridGen.Polymer
