/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ListColoring

/-!
# The height-three transfer, and the eigenfunctional telescoping

The abstract core of the height-three programme of
`ai_research_notes/GRID_HEIGHT3_EIGENFUNCTIONAL_2026-08-25.md`, with no graph in sight — the
analogue of `Ladder.Transfer` for columns of three vertices.

A column state is a triple `(a, b, c)` of colours, proper on the column (`a ≠ b`, `b ≠ c`). The
transfer `step` extends a state vector across one seam. Two integer sequences `Fne`, `Dp` — the
uniform *future counts* of a state by equality pattern (`Feq = Fne + Dp`) — drive an exact
telescoping identity, and two linear inequalities per seam,

* `(H1)`: `total' ≥ ene · total + eqMass`, and
* `(C1_r)`: `cc · total' + eqMass' ≥ cc · (ene · total + eqMass) + gam · total + del · eqMass`,

together with a one-column initial condition, force the total after `n` seams to be at least the
uniform count. Everything is over `ℕ`; the Perron data of the note is replaced by the integer
`cc = (k-2)((k-1)(k-2)+1)`, which satisfies `cc · Dp i ≤ Fne i` for every horizon `i`.
-/

open Finset

namespace Grid3

/-! ### States, masses, the transfer -/

/-- A column state: top, middle and bottom colours. -/
abbrev State := ℕ × ℕ × ℕ

/-- The states of a column with lists `T`, `M`, `B`: proper colourings of the three-vertex path. -/
def states (T M B : Finset ℕ) : Finset State :=
  (T ×ˢ M ×ˢ B).filter fun s => s.1 ≠ s.2.1 ∧ s.2.1 ≠ s.2.2

theorem mem_states {T M B : Finset ℕ} {s : State} :
    s ∈ states T M B ↔ s.1 ∈ T ∧ s.2.1 ∈ M ∧ s.2.2 ∈ B ∧ s.1 ≠ s.2.1 ∧ s.2.1 ≠ s.2.2 := by
  simp [states, Finset.mem_filter, Finset.mem_product, and_assoc]

/-- Two states of adjacent columns are compatible when they differ in every row. -/
def Compat (s t : State) : Prop := s.1 ≠ t.1 ∧ s.2.1 ≠ t.2.1 ∧ s.2.2 ≠ t.2.2

instance : DecidableRel Compat := fun s t =>
  inferInstanceAs (Decidable (s.1 ≠ t.1 ∧ s.2.1 ≠ t.2.1 ∧ s.2.2 ≠ t.2.2))

/-- The equality pattern: top and bottom colours coincide. -/
def IsEq (s : State) : Prop := s.1 = s.2.2

instance : DecidablePred IsEq := fun s => inferInstanceAs (Decidable (s.1 = s.2.2))

/-- Total mass of a state vector. -/
def total (S : Finset State) (N : State → ℕ) : ℕ := ∑ s ∈ S, N s

/-- Mass on the `eq` states. -/
def eqMass (S : Finset State) (N : State → ℕ) : ℕ := ∑ s ∈ S.filter IsEq, N s

/-- One seam of transfer. -/
def step (S : Finset State) (N : State → ℕ) : State → ℕ :=
  fun t => ∑ s ∈ S.filter (fun s => Compat s t), N s

/-- The number of successors of `s` in the column with lists `T`, `M`, `B`. -/
def succ (T M B : Finset ℕ) (s : State) : ℕ := ((states T M B).filter (Compat s)).card

/-- The number of `eq` successors. -/
def eqSucc (T M B : Finset ℕ) (s : State) : ℕ :=
  ((states T M B).filter fun t => Compat s t ∧ IsEq t).card

/-! ### The integer data of the uniform pattern transfer -/

/-- Uniform successors of an `ne` state: `(k-1)(k-2)² + 2(k-2)`. -/
def ene (k : ℕ) : ℕ := (k - 1) * (k - 2) ^ 2 + 2 * (k - 2)

/-- Uniform `eq` successors of an `ne` state: `(k-2)² + 1 = k² - 4k + 5`. -/
def gam (k : ℕ) : ℕ := (k - 2) ^ 2 + 1

/-- The extra `eq` successors of an `eq` state: `k - 2`. -/
def del (k : ℕ) : ℕ := k - 2

/-- The integer replacing `κ - 1 = 1/(e_ne - λ)`: `cc = (k-2)((k-1)(k-2)+1)`, so that
`cc + del = ene`. -/
def cc (k : ℕ) : ℕ := (k - 2) * ((k - 1) * (k - 2) + 1)

theorem cc_add_del (k : ℕ) : cc k + del k = ene k := by
  unfold cc del ene; ring

mutual
/-- `Fne k i` is the number of uniform `i`-column continuations of an `ne` state, and
`Fne k i + Dp k i` that of an `eq` state. -/
def Fne (k : ℕ) : ℕ → ℕ
  | 0 => 1
  | i + 1 => ene k * Fne k i + gam k * Dp k i
/-- The `eq`–`ne` gap of the uniform future counts. -/
def Dp (k : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => Fne k i + del k * Dp k i
end

@[simp] theorem Fne_zero (k : ℕ) : Fne k 0 = 1 := by rw [Fne]
@[simp] theorem Dp_zero (k : ℕ) : Dp k 0 = 0 := by rw [Dp]
theorem Fne_succ (k i : ℕ) : Fne k (i + 1) = ene k * Fne k i + gam k * Dp k i := by rw [Fne]
theorem Dp_succ (k i : ℕ) : Dp k (i + 1) = Fne k i + del k * Dp k i := by rw [Dp]

/-- **The horizon bound.** `cc · Dp i ≤ Fne i` at every horizon; the induction closes exactly
because `cc + del = ene`. -/
theorem cc_mul_Dp_le (k : ℕ) : ∀ i, cc k * Dp k i ≤ Fne k i := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
      rw [Fne_succ, Dp_succ]
      have h := cc_add_del k
      calc cc k * (Fne k i + del k * Dp k i)
          = cc k * Fne k i + del k * (cc k * Dp k i) := by ring
        _ ≤ cc k * Fne k i + del k * Fne k i := by
            exact Nat.add_le_add_left (Nat.mul_le_mul_left _ ih) _
        _ = ene k * Fne k i := by rw [← h]; ring
        _ ≤ ene k * Fne k i + gam k * Dp k i := Nat.le_add_right _ _

/-- The indicator of the `eq` pattern. -/
def eqInd (s : State) : ℕ := if IsEq s then 1 else 0

/-- The uniform future count of a state by pattern: `Fne` plus `Dp` on `eq` states. -/
def Fpat (k i : ℕ) (s : State) : ℕ := Fne k i + Dp k i * eqInd s

@[simp] theorem Fpat_zero (k : ℕ) (s : State) : Fpat k 0 s = 1 := by simp [Fpat]

/-- The uniform pattern transfer, read off the recursion. -/
theorem Fpat_succ (k i : ℕ) (s : State) :
    Fpat k (i + 1) s = Fne k i * (ene k + eqInd s) + Dp k i * (gam k + del k * eqInd s) := by
  unfold Fpat eqInd
  rw [Fne_succ, Dp_succ]
  split_ifs <;> ring

/-! ### Sums over a seam -/

/-- The `eq` mass as a weighted sum. -/
theorem eqMass_eq_sum (S : Finset State) (N : State → ℕ) :
    eqMass S N = ∑ s ∈ S, N s * eqInd s := by
  unfold eqMass eqInd
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs <;> simp

/-- Summing a function of the next column against a state vector, seam by seam. -/
theorem sum_step_mul (S : Finset State) (N : State → ℕ) (T M B : Finset ℕ) (F : State → ℕ) :
    ∑ t ∈ states T M B, step S N t * F t
      = ∑ s ∈ S, N s * ∑ t ∈ (states T M B).filter (Compat s), F t := by
  classical
  simp only [step, Finset.sum_filter, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  split_ifs <;> simp

/-- The successors of `s`, weighted by pattern. -/
theorem sum_compat_Fpat (k i : ℕ) (T M B : Finset ℕ) (s : State) :
    ∑ t ∈ (states T M B).filter (Compat s), Fpat k i t
      = Fne k i * succ T M B s + Dp k i * eqSucc T M B s := by
  classical
  unfold Fpat succ eqSucc
  rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm, ← Finset.mul_sum]
  congr 1
  unfold eqInd
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one,
    Finset.filter_filter]

/-- The total after a seam. -/
theorem total_step (S : Finset State) (N : State → ℕ) (T M B : Finset ℕ) :
    total (states T M B) (step S N) = ∑ s ∈ S, N s * succ T M B s := by
  have h := sum_step_mul S N T M B (fun _ => 1)
  simp only [mul_one, Finset.sum_const, smul_eq_mul] at h
  simpa [total, succ] using h

/-- The `eq` mass after a seam. -/
theorem eqMass_step (S : Finset State) (N : State → ℕ) (T M B : Finset ℕ) :
    eqMass (states T M B) (step S N) = ∑ s ∈ S, N s * eqSucc T M B s := by
  classical
  rw [eqMass_eq_sum, sum_step_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  unfold eqInd eqSucc
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one,
    Finset.filter_filter]

/-! ### The two seam inequalities -/

/-- `(H1)`: the actual successor total dominates the uniform pattern prediction. -/
def H1 (S : Finset State) (N : State → ℕ) (T M B : Finset ℕ) (k : ℕ) : Prop :=
  ene k * total S N + eqMass S N ≤ total (states T M B) (step S N)

/-- `(C1_r)`: the rational Perron-growth inequality. -/
def C1r (S : Finset State) (N : State → ℕ) (T M B : Finset ℕ) (k : ℕ) : Prop :=
  cc k * (ene k * total S N + eqMass S N) + gam k * total S N + del k * eqMass S N
    ≤ cc k * total (states T M B) (step S N) + eqMass (states T M B) (step S N)

/-- **The seam inequality.** Under `(H1)` and `(C1_r)`, the future-weighted mass does not
decrease across the seam, at every horizon. -/
theorem seam_le (k i : ℕ) (S : Finset State) (N : State → ℕ) (T M B : Finset ℕ)
    (h1 : H1 S N T M B k) (hc : C1r S N T M B k) :
    ∑ s ∈ S, N s * Fpat k (i + 1) s ≤ ∑ t ∈ states T M B, step S N t * Fpat k i t := by
  rw [sum_step_mul]
  simp only [sum_compat_Fpat, Fpat_succ]
  have hl : ∑ s ∈ S, N s * (Fne k i * (ene k + eqInd s) + Dp k i * (gam k + del k * eqInd s))
      = Fne k i * (ene k * total S N + eqMass S N)
        + Dp k i * (gam k * total S N + del k * eqMass S N) := by
    simp only [total, eqMass_eq_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  have hr : ∑ s ∈ S, N s * (Fne k i * succ T M B s + Dp k i * eqSucc T M B s)
      = Fne k i * total (states T M B) (step S N) + Dp k i * eqMass (states T M B) (step S N) := by
    rw [total_step, eqMass_step]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  rw [hl, hr]
  unfold H1 at h1
  unfold C1r at hc
  have hcd := cc_mul_Dp_le k i
  -- in `ℤ`: `D·(C1_r)` plus `(F - c·D)·(A' - X) ≥ 0` is exactly the goal
  zify at h1 hc hcd ⊢
  nlinarith [mul_le_mul_of_nonneg_left hc (Int.natCast_nonneg (Dp k i)),
    mul_nonneg (sub_nonneg.mpr hcd) (sub_nonneg.mpr h1)]

/-! ### Chains -/

/-- The three lists carried by one column. -/
abbrev ColumnLists := Finset ℕ × Finset ℕ × Finset ℕ

/-- A sequence of columns. -/
abbrev Cols := ℕ → ColumnLists

/-- The proper states supported by one column. -/
def columnStates (C : ColumnLists) : Finset State := states C.1 C.2.1 C.2.2

/-- The states of column `j`. -/
def cols (L : Cols) (j : ℕ) : Finset State := columnStates (L j)

/-- The chain of state vectors: all ones on the first column, then one seam at a time. -/
def vec (L : Cols) : ℕ → (State → ℕ)
  | 0 => fun _ => 1
  | j + 1 => step (cols L j) (vec L j)

@[simp] theorem vec_zero (L : Cols) : vec L 0 = fun _ => 1 := rfl
@[simp] theorem vec_succ (L : Cols) (j : ℕ) : vec L (j + 1) = step (cols L j) (vec L j) := rfl

/-- Both seam inequalities hold at seam `j` of the chain. -/
def SeamOK (k : ℕ) (L : Cols) (j : ℕ) : Prop :=
  H1 (cols L j) (vec L j) (L (j+1)).1 (L (j+1)).2.1 (L (j+1)).2.2 k
    ∧ C1r (cols L j) (vec L j) (L (j+1)).1 (L (j+1)).2.1 (L (j+1)).2.2 k

/-- The future-weighted mass at column `j` of a chain of `n + 1` columns. -/
def fw (k : ℕ) (L : Cols) (n j : ℕ) : ℕ := ∑ s ∈ cols L j, vec L j s * Fpat k (n - j) s

theorem fw_succ_ge (k : ℕ) (L : Cols) (n j : ℕ) (hj : j < n) (h : SeamOK k L j) :
    fw k L n j ≤ fw k L n (j + 1) := by
  unfold fw
  have hi : n - j = (n - (j + 1)) + 1 := by omega
  rw [hi, vec_succ]
  exact seam_le k (n - (j + 1)) _ _ _ _ _ h.1 h.2

/-- **The telescoping bound.** If every seam is `OK`, the total after `n` seams is at least the
first column's states weighted by their uniform `n`-column futures. -/
theorem total_vec_ge_fw (k : ℕ) (L : Cols) (n : ℕ) (h : ∀ j, j < n → SeamOK k L j) :
    ∑ s ∈ cols L 0, Fpat k n s ≤ total (cols L n) (vec L n) := by
  have hmono : ∀ j, j ≤ n → fw k L n 0 ≤ fw k L n j := by
    intro j
    induction j with
    | zero => intro _; exact le_rfl
    | succ j ih =>
        intro hj
        exact le_trans (ih (by omega)) (fw_succ_ge k L n j (by omega) (h j (by omega)))
  have h0 : fw k L n 0 = ∑ s ∈ cols L 0, Fpat k n s := by
    simp [fw]
  have hn : fw k L n n = total (cols L n) (vec L n) := by
    simp [fw, total]
  rw [← h0, ← hn]
  exact hmono n le_rfl


/-! ### Congruence, and the uniform chain -/

/-- The transfer only reads the vector on the states summed over. -/
theorem step_congr {S : Finset State} {N N' : State → ℕ} (h : ∀ s ∈ S, N s = N' s) :
    step S N = step S N' := by
  funext t
  unfold step
  exact Finset.sum_congr rfl fun s hs => h s (Finset.mem_filter.mp hs).1

/-- The chain up to column `j` depends only on the first `j` columns of lists. -/
theorem vec_congr {L L' : Cols} : ∀ j, (∀ i, i ≤ j → L i = L' i) → vec L j = vec L' j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro h
      rw [vec_succ, vec_succ, ih (fun i hi => h i (by omega))]
      have hc : cols L j = cols L' j := by unfold cols; rw [h j (by omega)]
      rw [hc]

/-- A seam whose successor counts are exactly the uniform pattern counts is an equality at every
horizon. -/
theorem seam_eq_of_uniform (k i : ℕ) (S : Finset State) (N : State → ℕ) (T M B : Finset ℕ)
    (hs : ∀ s ∈ S, succ T M B s = ene k + eqInd s)
    (he : ∀ s ∈ S, eqSucc T M B s = gam k + del k * eqInd s) :
    ∑ s ∈ S, N s * Fpat k (i + 1) s = ∑ t ∈ states T M B, step S N t * Fpat k i t := by
  rw [sum_step_mul]
  refine Finset.sum_congr rfl fun s hs' => ?_
  rw [sum_compat_Fpat, hs s hs', he s hs', Fpat_succ]

/-- The uniform sequence of columns. -/
def uniformCols (k : ℕ) : Cols := fun _ => (Finset.range k, Finset.range k, Finset.range k)

/-- Along the uniform chain the future-weighted mass is constant. -/
theorem fw_uniform (k : ℕ) (n : ℕ)
    (hs : ∀ s ∈ states (Finset.range k) (Finset.range k) (Finset.range k),
      succ (Finset.range k) (Finset.range k) (Finset.range k) s = ene k + eqInd s)
    (he : ∀ s ∈ states (Finset.range k) (Finset.range k) (Finset.range k),
      eqSucc (Finset.range k) (Finset.range k) (Finset.range k) s = gam k + del k * eqInd s) :
    ∀ j, j ≤ n → fw k (uniformCols k) n j = fw k (uniformCols k) n 0 := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro hj
      rw [← ih (by omega)]
      unfold fw
      have hi : n - j = (n - (j + 1)) + 1 := by omega
      rw [hi, vec_succ]
      exact (seam_eq_of_uniform k (n - (j + 1)) _ _ _ _ _ hs he).symm

/-- **The uniform total, in closed form**: the first column's states weighted by their
`n`-column futures. -/
theorem total_uniform (k : ℕ) (n : ℕ)
    (hs : ∀ s ∈ states (Finset.range k) (Finset.range k) (Finset.range k),
      succ (Finset.range k) (Finset.range k) (Finset.range k) s = ene k + eqInd s)
    (he : ∀ s ∈ states (Finset.range k) (Finset.range k) (Finset.range k),
      eqSucc (Finset.range k) (Finset.range k) (Finset.range k) s = gam k + del k * eqInd s) :
    total (cols (uniformCols k) n) (vec (uniformCols k) n)
      = ∑ s ∈ states (Finset.range k) (Finset.range k) (Finset.range k), Fpat k n s := by
  have h := fw_uniform k n hs he n le_rfl
  unfold fw at h
  simp only [Nat.sub_self, Fpat_zero, mul_one, Nat.sub_zero, vec_zero, one_mul] at h
  unfold total
  rw [h]
  rfl

/-- A sum of `Fpat` over a column, in terms of its state count and `eq` count. -/
theorem sum_Fpat (k i : ℕ) (S : Finset State) :
    ∑ s ∈ S, Fpat k i s = Fne k i * S.card + Dp k i * (S.filter IsEq).card := by
  unfold Fpat eqInd
  rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm, ← Finset.mul_sum,
    Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]

end Grid3
