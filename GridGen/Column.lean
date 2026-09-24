/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ListColoring

/-!
# Column states and the transfer, for an arbitrary row graph

`Grid3.Transfer` treats columns of three vertices. Here the column is an arbitrary finite graph
`H` on a vertex type `V` — for the grid `P_m □ P_n`, `H = pathG (m-1)` — and a *state* of a
column is a proper colouring of `H` from the column's lists. Two states of adjacent columns are
compatible when they differ at every vertex of `V`. The transfer `step` extends a state vector
across one seam, and the chain `vec` of an infinite sequence of columns of lists is the vector of
colouring counts graded by the last column (`GridGen.Graph` proves that).

Nothing in this file depends on the shape of `H`.
-/

open Finset SimpleGraph

namespace GridGen

variable {V : Type*}

/-- A column state: a colour at every vertex of the row graph. -/
abbrev State (V : Type*) := V → ℕ

/-- The lists of one column. -/
abbrev Lists (V : Type*) := V → Finset ℕ

/-- Two states of adjacent columns are compatible when they differ at every vertex. -/
def Compat (s t : State V) : Prop := ∀ v, s v ≠ t v

/-- Total mass of a state vector. -/
def total (S : Finset (State V)) (N : State V → ℕ) : ℕ := ∑ s ∈ S, N s

theorem total_congr {S : Finset (State V)} {N N' : State V → ℕ} (h : ∀ s ∈ S, N s = N' s) :
    total S N = total S N' :=
  Finset.sum_congr rfl h

variable [Fintype V]

instance (s t : State V) : Decidable (Compat s t) := by unfold Compat; infer_instance

/-- One seam of transfer. -/
def step (S : Finset (State V)) (N : State V → ℕ) : State V → ℕ :=
  fun t => ∑ s ∈ S.filter (fun s => Compat s t), N s

/-- The transfer only reads the vector on the states summed over. -/
theorem step_congr {S : Finset (State V)} {N N' : State V → ℕ} (h : ∀ s ∈ S, N s = N' s) :
    step S N = step S N' := by
  funext t
  unfold step
  exact Finset.sum_congr rfl fun s hs => h s (Finset.mem_filter.mp hs).1

theorem step_sum {ι : Type*} (I : Finset ι) (S : Finset (State V)) (Ns : ι → State V → ℕ) :
    step S (fun s => ∑ i ∈ I, Ns i s) = fun t => ∑ i ∈ I, step S (Ns i) t := by
  funext t; unfold step; exact Finset.sum_comm

theorem step_smul (c : ℕ) (S : Finset (State V)) (N : State V → ℕ) :
    step S (fun s => c * N s) = fun t => c * step S N t := by
  funext t; unfold step; rw [Finset.mul_sum]

/-- The transfer of a nonnegative combination. -/
theorem step_sum_smul {ι : Type*} (I : Finset ι) (c : ι → ℕ) (S : Finset (State V))
    (Ns : ι → State V → ℕ) :
    step S (fun s => ∑ i ∈ I, c i * Ns i s) = fun t => ∑ i ∈ I, c i * step S (Ns i) t := by
  funext t
  unfold step
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]

/-- Every list of the column has `k` colours. -/
def IsKLists (k : ℕ) (X : Lists V) : Prop := ∀ v, (X v).card = k

variable [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- The states of a column with lists `X`: the proper colourings of the row graph from `X`. -/
def states (X : Lists V) : Finset (State V) := H.colorings X

theorem mem_states {X : Lists V} {s : State V} :
    s ∈ states H X ↔ (∀ v, s v ∈ X v) ∧ H.IsProperColoring s := by
  simp [states]

/-- The number of successors of `s` in the column with lists `X`. -/
def succ (X : Lists V) (s : State V) : ℕ := ((states H X).filter (Compat s)).card

/-- Summing a function of the next column against a state vector, seam by seam. -/
theorem sum_step_mul (S : Finset (State V)) (N : State V → ℕ) (X : Lists V) (F : State V → ℕ) :
    ∑ t ∈ states H X, step S N t * F t
      = ∑ s ∈ S, N s * ∑ t ∈ (states H X).filter (Compat s), F t := by
  classical
  simp only [step, Finset.sum_filter, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  split_ifs <;> simp

/-- The total after a seam. -/
theorem total_step (S : Finset (State V)) (N : State V → ℕ) (X : Lists V) :
    total (states H X) (step S N) = ∑ s ∈ S, N s * succ H X s := by
  have h := sum_step_mul H S N X (fun _ => 1)
  simp only [mul_one, Finset.sum_const, smul_eq_mul] at h
  simpa [total, succ] using h

/-! ### Chains -/

/-- A sequence of columns of lists. -/
abbrev Cols (V : Type*) := ℕ → Lists V

/-- A sequence of columns of `k`-lists. -/
def IsKCols (k : ℕ) (L : Cols V) : Prop := ∀ j, IsKLists k (L j)

/-- The states of column `j`. -/
def cols (L : Cols V) (j : ℕ) : Finset (State V) := states H (L j)

/-- The chain of state vectors: all ones on the first column, then one seam at a time. -/
def vec (L : Cols V) : ℕ → (State V → ℕ)
  | 0 => fun _ => 1
  | j + 1 => step (cols H L j) (vec L j)

@[simp] theorem vec_zero (L : Cols V) : vec H L 0 = fun _ => 1 := rfl
@[simp] theorem vec_succ (L : Cols V) (j : ℕ) : vec H L (j + 1) = step (cols H L j) (vec H L j) :=
  rfl

/-- The chain up to column `j` depends only on the first `j` columns of lists. -/
theorem vec_congr {L L' : Cols V} : ∀ j, (∀ i, i ≤ j → L i = L' i) → vec H L j = vec H L' j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro h
      rw [vec_succ, vec_succ, ih (fun i hi => h i (by omega))]
      have hc : cols H L j = cols H L' j := by unfold cols; rw [h j (by omega)]
      rw [hc]

end GridGen
