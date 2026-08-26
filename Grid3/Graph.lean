/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Grid3.Transfer

/-!
# The `3 × (n+1)` grid as a graph, and its colouring transfer

`Grid3.Transfer` proves inequalities about abstract state vectors. This file connects them to
`pathG 2 □ pathG n` — the `3 × (n+1)` grid, `P_3 □ P_{n+1}` — by showing that the colouring
counts of that graph, graded by the colours of the last column, obey exactly the abstract
transfer `Grid3.step`. It is `Ladder/Graph.lean` with three rows instead of two.
-/

namespace Grid3

open SimpleGraph ListColoring Finset
open scoped SimpleGraph

/-! ### The three rows -/

/-- The top row: the pendant vertex of `pathG 2`. -/
def rowT : PathV 2 := (none : Option (PathV 1))

/-- The middle row. -/
def rowM : PathV 2 := (some (none : Option (PathV 0)) : Option (PathV 1))

/-- The bottom row. -/
def rowB : PathV 2 := (some (some () : Option (PathV 0)) : Option (PathV 1))

lemma rowT_ne_rowM : rowT ≠ rowM := fun h => Option.some_ne_none _ (show (some none : Option (PathV 1)) = none from h.symm)
lemma rowM_ne_rowB : rowM ≠ rowB := fun h => by
  have h' : (none : Option (PathV 0)) = some () := Option.some_inj.mp (show (some (none : Option (PathV 0)) : Option (PathV 1)) = some (some ()) from h)
  exact Option.some_ne_none _ h'.symm
lemma rowT_ne_rowB : rowT ≠ rowB := fun h => Option.some_ne_none _ (show (some (some ()) : Option (PathV 1)) = none from h.symm)

/-- Every vertex of `pathG 2` is one of the three rows. -/
lemma row_eq (x : PathV 2) : x = rowT ∨ x = rowM ∨ x = rowB := by
  match x with
  | none => exact Or.inl rfl
  | some none => exact Or.inr (Or.inl rfl)
  | some (some u) => exact Or.inr (Or.inr (by rw [rowB, Subsingleton.elim u ()]))

/-- Adjacency in `pathG 2`: top–middle and middle–bottom. -/
lemma pathTwo_adj_iff {x y : PathV 2} :
    (pathG 2).Adj x y ↔ (x = rowT ∧ y = rowM) ∨ (x = rowM ∧ y = rowT)
      ∨ (x = rowM ∧ y = rowB) ∨ (x = rowB ∧ y = rowM) := by
  revert x y
  decide

lemma adj_rowT_rowM : (pathG 2).Adj rowT rowM := pathTwo_adj_iff.mpr (Or.inl ⟨rfl, rfl⟩)
lemma adj_rowM_rowB : (pathG 2).Adj rowM rowB := pathTwo_adj_iff.mpr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))

/-! ### The grid's three kinds of edge -/

variable {n : ℕ}

/-- Older columns: the induced subgraph on `some` is the shorter grid. -/
lemma adj_some_some {x y : PathV 2} {v w : PathV n} :
    (pathG 2 □ pathG (n + 1)).Adj (x, (some v : PathV (n + 1))) (y, (some w : PathV (n + 1)))
      ↔ (pathG 2 □ pathG n).Adj (x, v) (y, w) := by
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
lemma adj_none_none {x y : PathV 2} :
    (pathG 2 □ pathG (n + 1)).Adj (x, (none : PathV (n + 1))) (y, (none : PathV (n + 1)))
      ↔ (pathG 2).Adj x y := by
  rw [boxProd_adj]
  constructor
  · rintro (⟨hxy, _⟩ | ⟨hadj, _⟩)
    · exact hxy
    · exact absurd rfl hadj.ne
  · intro h; exact Or.inl ⟨h, rfl⟩

/-- The rails: a new-column vertex is adjacent to the old last column in its own row only. -/
lemma adj_none_some {x y : PathV 2} {w : PathV n} :
    (pathG 2 □ pathG (n + 1)).Adj (x, (none : PathV (n + 1))) (y, (some w : PathV (n + 1)))
      ↔ x = y ∧ w = pathEnd n := by
  rw [boxProd_adj]
  constructor
  · rintro (⟨_, he⟩ | ⟨hw, hxy⟩)
    · exact absurd he (Option.some_ne_none w).symm
    · exact ⟨hxy, (show (pathG (n + 1)).Adj none (some w) from hw)⟩
  · rintro ⟨rfl, rfl⟩
    exact Or.inr ⟨show (pathG (n + 1)).Adj none (some (pathEnd n)) from rfl, rfl⟩

/-! ### Counting colourings by the colours of the last column -/

/-- The three vertices of the last column. -/
def lastT (n : ℕ) : PathV 2 × PathV n := (rowT, pathEnd n)
def lastM (n : ℕ) : PathV 2 × PathV n := (rowM, pathEnd n)
def lastB (n : ℕ) : PathV 2 × PathV n := (rowB, pathEnd n)

lemma lastT_adj_lastM : (pathG 2 □ pathG n).Adj (lastT n) (lastM n) :=
  boxProd_adj.mpr (Or.inl ⟨adj_rowT_rowM, rfl⟩)
lemma lastM_adj_lastB : (pathG 2 □ pathG n).Adj (lastM n) (lastB n) :=
  boxProd_adj.mpr (Or.inl ⟨adj_rowM_rowB, rfl⟩)

/-- The states available to the last column. -/
def col (M : ListAssignment (PathV 2 × PathV n)) : Finset State :=
  states (M (lastT n)) (M (lastM n)) (M (lastB n))

/-- The state of a colouring: the colours of its last column. -/
def stateOf (n : ℕ) (f : PathV 2 × PathV n → ℕ) : State := (f (lastT n), f (lastM n), f (lastB n))

/-- The number of colourings from `M` whose last column is in state `s`. -/
def cnt (n : ℕ) (M : ListAssignment (PathV 2 × PathV n)) (s : State) : ℕ :=
  (((pathG 2 □ pathG n).colorings M).filter fun f => stateOf n f = s).card

/-- **Grading by the last column.** -/
theorem card_filter_eq_sum (M : ListAssignment (PathV 2 × PathV n))
    (P : State → Prop) [DecidablePred P] :
    (((pathG 2 □ pathG n).colorings M).filter fun f => P (stateOf n f)).card
      = ∑ s ∈ (col M).filter P, cnt n M s := by
  classical
  have hmem : ∀ f ∈ ((pathG 2 □ pathG n).colorings M).filter (fun f => P (stateOf n f)),
      stateOf n f ∈ (col M).filter P := by
    intro f hf
    rw [Finset.mem_filter] at hf ⊢
    refine ⟨mem_states.mpr ⟨mem_list_of_mem_colorings hf.1 _, mem_list_of_mem_colorings hf.1 _,
      mem_list_of_mem_colorings hf.1 _, isProperColoring_of_mem_colorings hf.1 lastT_adj_lastM,
      isProperColoring_of_mem_colorings hf.1 lastM_adj_lastB⟩, hf.2⟩
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
theorem col_eq_total (M : ListAssignment (PathV 2 × PathV n)) :
    (pathG 2 □ pathG n).col M = total (col M) (cnt n M) := by
  classical
  have := card_filter_eq_sum M (fun _ => True)
  simpa [SimpleGraph.col, total, Finset.filter_true_of_mem] using this

/-! ### One more column -/

/-- The list assignment inherited by the older columns. -/
def restrM (M : ListAssignment (PathV 2 × PathV (n + 1))) : ListAssignment (PathV 2 × PathV n) :=
  fun q => M (q.1, (some q.2 : PathV (n + 1)))

/-- Restricting a colouring to the older columns. -/
def restr (f : PathV 2 × PathV (n + 1) → ℕ) : PathV 2 × PathV n → ℕ :=
  fun q => f (q.1, (some q.2 : PathV (n + 1)))

/-- The colour a state gives to a row. -/
def rowColor (s : State) (x : PathV 2) : ℕ :=
  if x = rowT then s.1 else if x = rowM then s.2.1 else s.2.2

@[simp] lemma rowColor_rowT (s : State) : rowColor s rowT = s.1 := by simp [rowColor]
@[simp] lemma rowColor_rowM (s : State) : rowColor s rowM = s.2.1 := by
  simp [rowColor, Ne.symm rowT_ne_rowM]
@[simp] lemma rowColor_rowB (s : State) : rowColor s rowB = s.2.2 := by
  simp [rowColor, Ne.symm rowT_ne_rowB, Ne.symm rowM_ne_rowB]

/-- Extending a colouring of the older columns by a new column in state `s`. -/
def extd (s : State) (h : PathV 2 × PathV n → ℕ) : PathV 2 × PathV (n + 1) → ℕ :=
  fun q => Option.elim (show Option (PathV n) from q.2) (rowColor s q.1) fun v => h (q.1, v)

@[simp] lemma extd_some (s : State) (h : PathV 2 × PathV n → ℕ) (x : PathV 2) (v : PathV n) :
    extd s h (x, (some v : PathV (n + 1))) = h (x, v) := rfl

lemma extd_none (s : State) (h : PathV 2 × PathV n → ℕ) (x : PathV 2) :
    extd s h (x, (none : PathV (n + 1))) = rowColor s x := rfl

lemma stateOf_extd (s : State) (h : PathV 2 × PathV n → ℕ) : stateOf (n + 1) (extd s h) = s := by
  obtain ⟨a, b, c⟩ := s
  simp [stateOf, lastT, lastM, lastB, extd_none]

/-- The last column of the restriction is the old last column. -/
lemma stateOf_restr (f : PathV 2 × PathV (n + 1) → ℕ) :
    stateOf n (restr f) = (f (rowT, some (pathEnd n)), f (rowM, some (pathEnd n)),
      f (rowB, some (pathEnd n))) := rfl

/-- A colouring is compatible with the old last column iff its new column is compatible with the
state of the restriction. -/
lemma compat_iff (f : PathV 2 × PathV (n + 1) → ℕ) (hf : (pathG 2 □ pathG (n + 1)).IsProperColoring f) :
    Compat (stateOf n (restr f)) (stateOf (n + 1) f) := by
  refine ⟨?_, ?_, ?_⟩ <;> · exact hf (adj_none_some.mpr ⟨rfl, rfl⟩).symm

/-- **The column bijection.** -/
theorem cnt_succ_aux (M : ListAssignment (PathV 2 × PathV (n + 1))) {s : State}
    (hs : s ∈ col M) :
    cnt (n + 1) M s
      = (((pathG 2 □ pathG n).colorings (restrM M)).filter
          fun h => Compat (stateOf n h) s).card := by
  classical
  obtain ⟨h1, h2, h3, h12, h23⟩ := mem_states.mp hs
  rw [cnt]
  refine Finset.card_bij' (fun f _ => restr f) (fun h _ => extd s h) ?_ ?_ ?_ ?_
  · -- restriction lands in the shorter grid, compatible with `s`
    intro f hf
    rw [Finset.mem_filter, mem_colorings] at hf
    obtain ⟨⟨hmem, hprop⟩, hst⟩ := hf
    rw [Finset.mem_filter, mem_colorings]
    refine ⟨⟨fun q => hmem _, fun a b hab => hprop (adj_some_some.mpr hab)⟩, ?_⟩
    rw [← hst]
    exact compat_iff f hprop
  · -- extension lands in the longer grid, with the prescribed last column
    intro h hh
    rw [Finset.mem_filter, mem_colorings] at hh
    obtain ⟨⟨hmem, hprop⟩, hcomp⟩ := hh
    have hmix : ∀ x : PathV 2, extd s h (x, (none : PathV (n + 1)))
        ≠ extd s h (x, (some (pathEnd n) : PathV (n + 1))) := by
      intro x
      rw [extd_none, extd_some]
      obtain ⟨c1, c2, c3⟩ := hcomp
      rcases row_eq x with rfl | rfl | rfl
      · simp only [rowColor_rowT]; exact fun hc => c1 hc.symm
      · simp only [rowColor_rowM]; exact fun hc => c2 hc.symm
      · simp only [rowColor_rowB]; exact fun hc => c3 hc.symm
    rw [Finset.mem_filter, mem_colorings]
    refine ⟨⟨?_, ?_⟩, stateOf_extd s h⟩
    · rintro ⟨x, q⟩
      match q with
      | some v => exact hmem (x, v)
      | none =>
          rw [extd_none]
          rcases row_eq x with rfl | rfl | rfl
          · simp only [rowColor_rowT]; exact h1
          · simp only [rowColor_rowM]; exact h2
          · simp only [rowColor_rowB]; exact h3
    · rintro ⟨x, qx⟩ ⟨y, qy⟩ hab
      match qx, qy with
      | some v, some w => exact hprop (adj_some_some.mp hab)
      | none, none =>
          have hxy := pathTwo_adj_iff.mp (adj_none_none.mp hab)
          rw [extd_none, extd_none]
          rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · simp only [rowColor_rowT, rowColor_rowM]; exact h12
          · simp only [rowColor_rowT, rowColor_rowM]; exact Ne.symm h12
          · simp only [rowColor_rowM, rowColor_rowB]; exact h23
          · simp only [rowColor_rowM, rowColor_rowB]; exact Ne.symm h23
      | none, some w =>
          obtain ⟨rfl, rfl⟩ := adj_none_some.mp hab
          exact hmix x
      | some v, none =>
          obtain ⟨rfl, rfl⟩ := adj_none_some.mp hab.symm
          exact Ne.symm (hmix y)
  · -- round trip on the longer grid
    intro f hf
    rw [Finset.mem_filter] at hf
    funext q
    match q with
    | (x, some v) => rfl
    | (x, none) =>
        rw [extd_none, ← hf.2]
        rcases row_eq x with rfl | rfl | rfl
        · rw [rowColor_rowT]; rfl
        · rw [rowColor_rowM]; rfl
        · rw [rowColor_rowB]; rfl
  · -- round trip on the shorter grid
    intro h _
    funext q
    rfl

/-- The last-column counts obey exactly the abstract transfer. -/
theorem cnt_succ (M : ListAssignment (PathV 2 × PathV (n + 1))) {s : State} (hs : s ∈ col M) :
    cnt (n + 1) M s = step (col (restrM M)) (cnt n (restrM M)) s := by
  classical
  rw [cnt_succ_aux M hs, step]
  exact card_filter_eq_sum (restrM M) (fun q => Compat q s)

/-! ### The first column -/

/-- `pathG 2 □ pathG 0` is just the three vertices of one column. -/
lemma vertex_zero (q : PathV 2 × PathV 0) : q = lastT 0 ∨ q = lastM 0 ∨ q = lastB 0 := by
  obtain ⟨x, u⟩ := q
  have hu : u = pathEnd 0 := Subsingleton.elim u ()
  subst hu
  rcases row_eq x with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- A single column has exactly one colouring per state. -/
theorem cnt_zero (M : ListAssignment (PathV 2 × PathV 0)) {s : State} (hs : s ∈ col M) :
    cnt 0 M s = 1 := by
  classical
  obtain ⟨h1, h2, h3, h12, h23⟩ := mem_states.mp hs
  set g : PathV 2 × PathV 0 → ℕ := fun q => rowColor s q.1 with hgdef
  have hgT : g (lastT 0) = s.1 := by simp [hgdef, lastT]
  have hgM : g (lastM 0) = s.2.1 := by simp [hgdef, lastM]
  have hgB : g (lastB 0) = s.2.2 := by simp [hgdef, lastB]
  have hset : (((pathG 2 □ pathG 0).colorings M).filter fun f => stateOf 0 f = s) = {g} := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_singleton, mem_colorings]
    constructor
    · rintro ⟨_, hst⟩
      have hst' : (f (lastT 0), f (lastM 0), f (lastB 0)) = s := hst
      funext q
      rcases vertex_zero q with rfl | rfl | rfl
      · rw [hgT]; exact congrArg Prod.fst hst'
      · rw [hgM]; exact congrArg (fun t : State => t.2.1) hst'
      · rw [hgB]; exact congrArg (fun t : State => t.2.2) hst'
    · rintro rfl
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro q
        rcases vertex_zero q with rfl | rfl | rfl
        · rw [hgT]; exact h1
        · rw [hgM]; exact h2
        · rw [hgB]; exact h3
      · intro a b hab
        have hab' := boxProd_adj.mp hab
        rcases hab' with ⟨hadj, he⟩ | ⟨hadj, _⟩
        · obtain ⟨x, u⟩ := a; obtain ⟨y, w⟩ := b
          simp only at he hadj
          subst he
          show rowColor s x ≠ rowColor s y
          rcases pathTwo_adj_iff.mp hadj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · simp only [rowColor_rowT, rowColor_rowM]; exact h12
          · simp only [rowColor_rowT, rowColor_rowM]; exact Ne.symm h12
          · simp only [rowColor_rowM, rowColor_rowB]; exact h23
          · simp only [rowColor_rowM, rowColor_rowB]; exact Ne.symm h23
        · exact absurd hadj (show ¬ (pathG 0).Adj a.2 b.2 from id)
      · show (g (lastT 0), g (lastM 0), g (lastB 0)) = s
        rw [hgT, hgM, hgB]
  rw [cnt, hset, Finset.card_singleton]


/-! ### Columns by index, and the chain of an assignment -/

/-- The vertex of `pathG n` in column `j` (counted from the far end; column `n` is `pathEnd n`). -/
def colVtx : (n j : ℕ) → PathV n
  | 0, _ => ()
  | n + 1, j => if j = n + 1 then (none : PathV (n + 1)) else (some (colVtx n j) : PathV (n + 1))

@[simp] lemma colVtx_self (n : ℕ) : colVtx n n = pathEnd n := by
  cases n with
  | zero => rfl
  | succ n => exact if_pos rfl

lemma colVtx_succ_of_le {n j : ℕ} (h : j ≤ n) :
    colVtx (n + 1) j = (some (colVtx n j) : PathV (n + 1)) :=
  if_neg (by omega)

/-- The lists of the columns of an assignment, as an abstract sequence. -/
def Lof (n : ℕ) (M : ListAssignment (PathV 2 × PathV n)) : Cols :=
  fun j => (M (rowT, colVtx n j), M (rowM, colVtx n j), M (rowB, colVtx n j))

lemma Lof_restrM (M : ListAssignment (PathV 2 × PathV (n + 1))) {j : ℕ} (hj : j ≤ n) :
    Lof n (restrM M) j = Lof (n + 1) M j := by
  simp [Lof, restrM, colVtx_succ_of_le hj]

lemma col_eq_cols (M : ListAssignment (PathV 2 × PathV n)) : col M = cols (Lof n M) n := by
  simp [col, cols, columnStates, Lof, lastT, lastM, lastB]

/-- The last-column counts are the abstract chain of the assignment's lists. -/
theorem cnt_eq_vec : ∀ (n : ℕ) (M : ListAssignment (PathV 2 × PathV n)), ∀ s ∈ col M,
    cnt n M s = vec (Lof n M) n s := by
  intro n
  induction n with
  | zero => intro M s hs; rw [cnt_zero M hs]; rfl
  | succ n ih =>
      intro M s hs
      rw [cnt_succ M hs, vec_succ]
      have hL : vec (Lof n (restrM M)) n = vec (Lof (n + 1) M) n :=
        vec_congr n fun i hi => Lof_restrM M hi
      have hcol : col (restrM M) = cols (Lof (n + 1) M) n := by
        rw [col_eq_cols]
        unfold cols
        rw [Lof_restrM M le_rfl]
      rw [step_congr (fun t ht => ih (restrM M) t ht), hL, hcol]

end Grid3
