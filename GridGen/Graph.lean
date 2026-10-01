/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Column

/-!
# `H □ P_{n+1}` as a graph, and its colouring transfer

The colouring counts of `H □ pathG n`, graded by the colours of the last column, obey exactly
the abstract transfer `GridGen.step` of the chain of the assignment's columns. This is
`Grid3.Graph` with the three explicit rows replaced by an arbitrary row graph `H`; the proofs
get shorter, not longer, because there is no case analysis on rows.
-/

namespace GridGen

open SimpleGraph ListColoring Finset
open scoped SimpleGraph

variable {V : Type*} (H : SimpleGraph V) {n : ℕ}

/-! ### The three kinds of edge -/

/-- Older columns: the induced subgraph on `some` is the shorter grid. -/
lemma adj_some_some {x y : V} {v w : PathV n} :
    (H □ pathG (n + 1)).Adj (x, (some v : PathV (n + 1))) (y, (some w : PathV (n + 1)))
      ↔ (H □ pathG n).Adj (x, v) (y, w) := by
  rw [boxProd_adj, boxProd_adj]
  constructor
  · rintro (⟨hxy, he⟩ | ⟨hadj, hxy⟩)
    · exact Or.inl ⟨hxy, Option.some_inj.mp (show (some v : Option (PathV n)) = some w from he)⟩
    · exact Or.inr ⟨hadj, hxy⟩
  · rintro (⟨hxy, he⟩ | ⟨hadj, hxy⟩)
    · exact Or.inl ⟨hxy, show (some v : PathV (n + 1)) = some w from
        congrArg some (show v = w from he)⟩
    · exact Or.inr ⟨hadj, hxy⟩

/-- The new column. -/
lemma adj_none_none {x y : V} :
    (H □ pathG (n + 1)).Adj (x, (none : PathV (n + 1))) (y, (none : PathV (n + 1)))
      ↔ H.Adj x y := by
  rw [boxProd_adj]
  constructor
  · rintro (⟨hxy, _⟩ | ⟨hadj, _⟩)
    · exact hxy
    · exact absurd rfl hadj.ne
  · intro h; exact Or.inl ⟨h, rfl⟩

/-- The rails: a new-column vertex is adjacent to the old last column in its own row only. -/
lemma adj_none_some {x y : V} {w : PathV n} :
    (H □ pathG (n + 1)).Adj (x, (none : PathV (n + 1))) (y, (some w : PathV (n + 1)))
      ↔ x = y ∧ w = pathEnd n := by
  rw [boxProd_adj]
  constructor
  · rintro (⟨_, he⟩ | ⟨hw, hxy⟩)
    · exact absurd he (Option.some_ne_none w).symm
    · exact ⟨hxy, (show (pathG (n + 1)).Adj none (some w) from hw)⟩
  · rintro ⟨rfl, rfl⟩
    exact Or.inr ⟨show (pathG (n + 1)).Adj none (some (pathEnd n)) from rfl, rfl⟩

variable [Fintype V] [DecidableEq V] [DecidableRel H.Adj]

/-! ### Counting colourings by the colours of the last column -/

/-- The state of a colouring: the colours of its last column. -/
def stateOf (n : ℕ) (f : V × PathV n → ℕ) : State V := fun v => f (v, pathEnd n)

/-- The states available to the last column. -/
def col (M : ListAssignment (V × PathV n)) : Finset (State V) :=
  states H (fun v => M (v, pathEnd n))

/-- The number of colourings from `M` whose last column is in state `s`. -/
def cnt (n : ℕ) (M : ListAssignment (V × PathV n)) (s : State V) : ℕ :=
  (((H □ pathG n).colorings M).filter fun f => stateOf n f = s).card

/-- **Grading by the last column.** -/
theorem card_filter_eq_sum (M : ListAssignment (V × PathV n))
    (P : State V → Prop) [DecidablePred P] :
    (((H □ pathG n).colorings M).filter fun f => P (stateOf n f)).card
      = ∑ s ∈ (col H M).filter P, cnt H n M s := by
  classical
  have hmem : ∀ f ∈ ((H □ pathG n).colorings M).filter (fun f => P (stateOf n f)),
      stateOf n f ∈ (col H M).filter P := by
    intro f hf
    rw [Finset.mem_filter] at hf ⊢
    refine ⟨(mem_states H).mpr ⟨fun v => mem_list_of_mem_colorings hf.1 _, ?_⟩, hf.2⟩
    intro v w hvw
    exact isProperColoring_of_mem_colorings hf.1 (boxProd_adj.mpr (Or.inl ⟨hvw, rfl⟩))
  rw [Finset.card_eq_sum_card_fiberwise hmem]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hPq : P q := (Finset.mem_filter.mp hq).2
  congr 1
  ext f
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨hf, _⟩, h⟩; exact ⟨hf, h⟩
  · rintro ⟨hf, h⟩
    exact ⟨⟨hf, by rw [h]; exact hPq⟩, h⟩

/-- The colouring count is the total mass on the last column. -/
theorem col_eq_total (M : ListAssignment (V × PathV n)) :
    (H □ pathG n).col M = total (col H M) (cnt H n M) := by
  classical
  have := card_filter_eq_sum H M (fun _ => True)
  simpa [SimpleGraph.col, total, Finset.filter_true_of_mem] using this

/-! ### One more column -/

/-- The list assignment inherited by the older columns. -/
def restrM (M : ListAssignment (V × PathV (n + 1))) : ListAssignment (V × PathV n) :=
  fun q => M (q.1, (some q.2 : PathV (n + 1)))

/-- Restricting a colouring to the older columns. -/
def restr (f : V × PathV (n + 1) → ℕ) : V × PathV n → ℕ :=
  fun q => f (q.1, (some q.2 : PathV (n + 1)))

/-- Extending a colouring of the older columns by a new column in state `s`. -/
def extd (s : State V) (h : V × PathV n → ℕ) : V × PathV (n + 1) → ℕ :=
  fun q => Option.elim (show Option (PathV n) from q.2) (s q.1) fun v => h (q.1, v)

omit [Fintype V] [DecidableEq V] [DecidableRel H.Adj] in
@[simp] lemma extd_some (s : State V) (h : V × PathV n → ℕ) (x : V) (v : PathV n) :
    extd s h (x, (some v : PathV (n + 1))) = h (x, v) := rfl

omit [Fintype V] [DecidableEq V] [DecidableRel H.Adj] in
lemma extd_none (s : State V) (h : V × PathV n → ℕ) (x : V) :
    extd s h (x, (none : PathV (n + 1))) = s x := rfl

omit [Fintype V] [DecidableEq V] [DecidableRel H.Adj] in
lemma stateOf_extd (s : State V) (h : V × PathV n → ℕ) : stateOf (n + 1) (extd s h) = s := by
  funext v; rfl

/-- A colouring is compatible with the old last column iff its new column is compatible with the
state of the restriction. -/
lemma compat_iff (f : V × PathV (n + 1) → ℕ) (hf : (H □ pathG (n + 1)).IsProperColoring f) :
    Compat (stateOf n (restr f)) (stateOf (n + 1) f) := by
  intro v
  exact (hf ((adj_none_some H).mpr ⟨rfl, rfl⟩)).symm

/-- **The column bijection.** -/
theorem cnt_succ_aux (M : ListAssignment (V × PathV (n + 1))) {s : State V}
    (hs : s ∈ col H M) :
    cnt H (n + 1) M s
      = (((H □ pathG n).colorings (restrM M)).filter
          fun h => Compat (stateOf n h) s).card := by
  classical
  obtain ⟨hmemS, hprop⟩ := (mem_states H).mp hs
  rw [cnt]
  refine Finset.card_bij' (fun f _ => restr f) (fun h _ => extd s h) ?_ ?_ ?_ ?_
  · -- restriction lands in the shorter grid, compatible with `s`
    intro f hf
    rw [Finset.mem_filter, mem_colorings] at hf
    obtain ⟨⟨hmem, hpropf⟩, hst⟩ := hf
    rw [Finset.mem_filter, mem_colorings]
    refine ⟨⟨fun q => hmem _, fun a b hab => hpropf ((adj_some_some H).mpr hab)⟩, ?_⟩
    rw [← hst]
    exact compat_iff H f hpropf
  · -- extension lands in the longer grid, with the prescribed last column
    intro h hh
    rw [Finset.mem_filter, mem_colorings] at hh
    obtain ⟨⟨hmem, hproph⟩, hcomp⟩ := hh
    have hmix : ∀ x : V, extd s h (x, (none : PathV (n + 1)))
        ≠ extd s h (x, (some (pathEnd n) : PathV (n + 1))) := by
      intro x
      rw [extd_none, extd_some]
      exact fun hc => hcomp x hc.symm
    rw [Finset.mem_filter, mem_colorings]
    refine ⟨⟨?_, ?_⟩, stateOf_extd s h⟩
    · rintro ⟨x, q⟩
      match q with
      | some v => exact hmem (x, v)
      | none => rw [extd_none]; exact hmemS x
    · rintro ⟨x, qx⟩ ⟨y, qy⟩ hab
      match qx, qy with
      | some v, some w => exact hproph ((adj_some_some H).mp hab)
      | none, none =>
          rw [extd_none, extd_none]
          exact hprop ((adj_none_none H).mp hab)
      | none, some w =>
          obtain ⟨rfl, rfl⟩ := (adj_none_some H).mp hab
          exact hmix x
      | some v, none =>
          obtain ⟨rfl, rfl⟩ := (adj_none_some H).mp hab.symm
          exact Ne.symm (hmix y)
  · -- round trip on the longer grid
    intro f hf
    rw [Finset.mem_filter] at hf
    funext q
    match q with
    | (x, some v) => rfl
    | (x, none) =>
        rw [extd_none, ← hf.2]
        rfl
  · -- round trip on the shorter grid
    intro h _
    funext q
    rfl

/-- The last-column counts obey exactly the abstract transfer. -/
theorem cnt_succ (M : ListAssignment (V × PathV (n + 1))) {s : State V} (hs : s ∈ col H M) :
    cnt H (n + 1) M s = step (col H (restrM M)) (cnt H n (restrM M)) s := by
  classical
  rw [cnt_succ_aux H M hs, step]
  exact card_filter_eq_sum H (restrM M) (fun q => Compat q s)

/-! ### The first column -/

/-- A single column has exactly one colouring per state. -/
theorem cnt_zero (M : ListAssignment (V × PathV 0)) {s : State V} (hs : s ∈ col H M) :
    cnt H 0 M s = 1 := by
  classical
  obtain ⟨hmemS, hprop⟩ := (mem_states H).mp hs
  set g : V × PathV 0 → ℕ := fun q => s q.1 with hgdef
  have hset : (((H □ pathG 0).colorings M).filter fun f => stateOf 0 f = s) = {g} := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_singleton, mem_colorings]
    constructor
    · rintro ⟨_, hst⟩
      funext q
      obtain ⟨x, u⟩ := q
      have hu : u = pathEnd 0 := Subsingleton.elim u ()
      subst hu
      exact congrFun hst x
    · rintro rfl
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rintro ⟨x, u⟩
        have hu : u = pathEnd 0 := Subsingleton.elim u ()
        subst hu
        exact hmemS x
      · intro a b hab
        rcases boxProd_adj.mp hab with ⟨hadj, _⟩ | ⟨hadj, _⟩
        · exact hprop hadj
        · exact absurd hadj (show ¬ (pathG 0).Adj a.2 b.2 from id)
      · rfl
  rw [cnt, hset, Finset.card_singleton]

/-! ### Columns by index, and the chain of an assignment -/

/-- The vertex of `pathG n` in column `j` (counted from the far end; column `n` is `pathEnd n`). -/
def colVtx : (n j : ℕ) → PathV n
  | 0, _ => ()
  | n + 1, j => if j = n + 1 then (none : PathV (n + 1)) else (some (colVtx n j) : PathV (n + 1))

omit [Fintype V] [DecidableEq V] [DecidableRel H.Adj] in
@[simp] lemma colVtx_self (n : ℕ) : colVtx n n = pathEnd n := by
  cases n with
  | zero => rfl
  | succ n => exact ite_eq_left rfl

omit [Fintype V] [DecidableEq V] [DecidableRel H.Adj] in
lemma colVtx_succ_of_le {n j : ℕ} (h : j ≤ n) :
    colVtx (n + 1) j = (some (colVtx n j) : PathV (n + 1)) :=
  ite_eq_right (by omega)

/-- The lists of the columns of an assignment, as an abstract sequence. -/
def Lof (n : ℕ) (M : ListAssignment (V × PathV n)) : Cols V :=
  fun j v => M (v, colVtx n j)

omit [Fintype V] [DecidableEq V] [DecidableRel H.Adj] in
lemma Lof_restrM (M : ListAssignment (V × PathV (n + 1))) {j : ℕ} (hj : j ≤ n) :
    Lof n (restrM M) j = Lof (n + 1) M j := by
  funext v
  simp [Lof, restrM, colVtx_succ_of_le hj]

lemma col_eq_cols (M : ListAssignment (V × PathV n)) : col H M = cols H (Lof n M) n := by
  unfold col cols Lof
  simp only [colVtx_self]

/-- The last-column counts are the abstract chain of the assignment's lists. -/
theorem cnt_eq_vec : ∀ (n : ℕ) (M : ListAssignment (V × PathV n)), ∀ s ∈ col H M,
    cnt H n M s = vec H (Lof n M) n s := by
  intro n
  induction n with
  | zero => intro M s hs; rw [cnt_zero H M hs]; rfl
  | succ n ih =>
      intro M s hs
      rw [cnt_succ H M hs, vec_succ]
      have hL : vec H (Lof n (restrM M)) n = vec H (Lof (n + 1) M) n :=
        vec_congr H n fun i hi => Lof_restrM M hi
      have hcol : col H (restrM M) = cols H (Lof (n + 1) M) n := by
        rw [col_eq_cols]
        unfold cols
        rw [Lof_restrM M le_rfl]
      rw [step_congr (fun t ht => ih (restrM M) t ht), hL, hcol]

end GridGen
