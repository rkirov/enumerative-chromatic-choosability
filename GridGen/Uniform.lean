/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Telescope

/-!
# The uniform futures, and the reference by equality pattern

`F k i s` is the number of sequences of `i` uniform columns — proper colourings of the row graph
from `{0, …, k-1}` — that can follow the state `s`. Along the uniform chain it is the exact
transfer, by definition, so the uniform colouring count is `∑_{s uniform} F k n s`
(`total_uniform`).

The reference used for list chains is `Φ k i s = F k i (patCap k s)`, where `pat s` relabels
the colours of `s` by their rank among the colours `s` uses — two states with the same equality
pattern get the same reference — and `patCap` merges every class of rank `≥ k` into the class
`k - 1`. The merging matters only for states using more than `k` colours, which exist once the
height exceeds `k`; leaving those classes unmatched (so that they constrain nothing) makes the
two-step inequality *fail* for tall grids (`ai_research_notes/cx/k3rev/h4/split.c`: a column
whose palette changes halfway down, `k = 5`, height `≥ 8`), while merging them restores it
(`split2.c`). This is the convention of the note's §5.6.
-/

open Finset SimpleGraph

namespace GridGen

variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- The uniform lists `{0, …, k-1}` at every vertex. -/
def unif (k : ℕ) : Lists V := fun _ => range k

/-- The number of `i`-column uniform continuations of a state. -/
def F (k : ℕ) : ℕ → State V → ℕ
  | 0 => fun _ => 1
  | i + 1 => fun s => ∑ t ∈ (states H (unif k)).filter (Compat s), F k i t

@[simp] theorem F_zero (k : ℕ) (s : State V) : F H k 0 s = 1 := rfl

theorem F_succ (k i : ℕ) (s : State V) :
    F H k (i + 1) s = ∑ t ∈ (states H (unif k)).filter (Compat s), F H k i t := rfl

/-- The uniform sequence of columns. -/
def uniformCols (k : ℕ) : Cols V := fun _ => unif k

/-- Across a uniform seam the `F`-weighted mass is conserved exactly, for every state vector. -/
theorem seam_eq_uniform (k i : ℕ) (S : Finset (State V)) (N : State V → ℕ) :
    ∑ s ∈ S, N s * F H k (i + 1) s = ∑ t ∈ states H (unif k), step S N t * F H k i t := by
  rw [sum_step_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [F_succ]

/-- Along the uniform chain the future-weighted mass is constant. -/
theorem fw_uniform (k n : ℕ) :
    ∀ j, j ≤ n → fw H (F H k) (uniformCols k) n j = fw H (F H k) (uniformCols k) n 0 := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro hj
      rw [← ih (by omega)]
      unfold fw
      have hi : n - j = (n - (j + 1)) + 1 := by omega
      rw [hi, vec_succ]
      exact (seam_eq_uniform H k (n - (j + 1)) _ _).symm

/-- **The uniform total, in closed form**: the uniform states weighted by their `n`-column
futures. -/
theorem total_uniform (k n : ℕ) :
    total (cols H (uniformCols k) n) (vec H (uniformCols k) n)
      = ∑ s ∈ states H (unif k), F H k n s := by
  have h := fw_uniform H k n n le_rfl
  unfold fw at h
  simp only [Nat.sub_self, F_zero, mul_one, Nat.sub_zero, vec_zero, one_mul] at h
  unfold total
  rw [h]
  rfl

/-! ### The reference by equality pattern -/

/-- The equality pattern of a state: each colour is replaced by its rank among the colours the
state uses. -/
def pat (s : State V) : State V :=
  fun v => ((Finset.univ.image s).filter (· < s v)).card

/-- The equality pattern with every class of rank `≥ k` merged into the class `k - 1`. -/
def patCap (k : ℕ) (s : State V) : State V := fun v => min (pat s v) (k - 1)

/-- **The reference**: the uniform future of the state's capped equality pattern. -/
def Φ (k i : ℕ) (s : State V) : ℕ := F H k i (patCap k s)

@[simp] theorem Φ_zero (k : ℕ) (s : State V) : Φ H k 0 s = 1 := rfl

end GridGen
