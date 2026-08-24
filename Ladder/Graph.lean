import Ladder.Transfer
import ListColoring

/-!
# The ladder as a graph, and its colouring transfer

`Ladder.Transfer` proves an inequality about abstract vectors on state sets. This file connects it
to `pathG 1 □ pathG n` — the `2 × (n+1)` grid — by showing that the colouring counts of that graph,
graded by the colours of the last rung, obey exactly the abstract recursion.

The point of working with the product directly, rather than with an iterated cone, is that no
isomorphism is needed: the induced subgraph of `pathG 1 □ pathG (n+1)` on the vertices whose second
coordinate is `some _` **is** `pathG 1 □ pathG n`, definitionally enough for `adj_some_some` below.
-/

namespace Ladder

open SimpleGraph ListColoring Finset
open scoped SimpleGraph

/-! ### The two rows -/

/-- The top row of the ladder: `pathG 1` has exactly two vertices, and this is the pendant one. -/
def rowT : PathV 1 := (none : Option (PathV 0))

/-- The bottom row of the ladder. -/
def rowB : PathV 1 := (some () : Option (PathV 0))

/-- `Option.noConfusion` cannot see through `PathV (m+1)`; this states it once, in the form the
`show ... from` idiom of `ListColoring.PathColorable` makes available. -/
lemma pathV_none_ne_some {m : ℕ} (v : PathV m) :
    (none : PathV (m + 1)) ≠ (some v : PathV (m + 1)) :=
    by
  intro h
  exact Option.some_ne_none v (show (some v : Option (PathV m)) = none from h.symm)

lemma rowT_ne_rowB : rowT ≠ rowB := pathV_none_ne_some (m := 0) ()

/-- `pathG 1` is a single edge, so adjacency in it is just distinctness. -/
lemma pathOne_adj_iff {x y : PathV 1} : (pathG 1).Adj x y ↔ x ≠ y := by
  match x, y with
  | none, none => exact iff_of_false (fun h => h.ne rfl) (fun h => h rfl)
  | none, some b =>
      exact iff_of_true (show b = pathEnd 0 from Subsingleton.elim b ())
        (pathV_none_ne_some (m := 0) b)
  | some a, none =>
      exact iff_of_true (show a = pathEnd 0 from Subsingleton.elim a ())
        (fun h => pathV_none_ne_some (m := 0) a h.symm)
  | some a, some b =>
      have hab : a = b := Subsingleton.elim a b
      subst hab
      exact iff_of_false (fun h => (show (pathG 0).Adj a a from h).ne rfl) (fun h => h rfl)

/-- Every vertex of `pathG 1` is one of the two rows. -/
lemma row_eq (x : PathV 1) : x = rowT ∨ x = rowB := by
  match x with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (by rw [rowB, Subsingleton.elim a ()])

/-! ### The ladder's three kinds of edge -/

variable {n : ℕ}

/-- Older columns: the induced subgraph on `some` is the shorter ladder. -/
lemma adj_some_some {x y : PathV 1} {v w : PathV n} :
    (pathG 1 □ pathG (n + 1)).Adj (x, (some v : PathV (n + 1))) (y, (some w : PathV (n + 1)))
      ↔ (pathG 1 □ pathG n).Adj (x, v) (y, w) := by
  rw [boxProd_adj, boxProd_adj]
  constructor
  · rintro (⟨hxy, he⟩ | ⟨hadj, hxy⟩)
    · exact Or.inl ⟨hxy, Option.some_inj.mp (show (some v : Option (PathV n)) = some w from he)⟩
    · exact Or.inr ⟨hadj, hxy⟩
  · rintro (⟨hxy, he⟩ | ⟨hadj, hxy⟩)
    · exact Or.inl ⟨hxy, show (some v : PathV (n + 1)) = some w from
        congrArg some (show v = w from he)⟩
    · exact Or.inr ⟨hadj, hxy⟩

/-- The new rung. -/
lemma adj_none_none {x y : PathV 1} :
    (pathG 1 □ pathG (n + 1)).Adj (x, (none : PathV (n + 1))) (y, (none : PathV (n + 1)))
      ↔ x ≠ y := by
  rw [boxProd_adj]
  constructor
  · rintro (⟨hxy, _⟩ | ⟨hadj, _⟩)
    · exact pathOne_adj_iff.mp hxy
    · exact absurd rfl hadj.ne
  · intro hxy
    exact Or.inl ⟨pathOne_adj_iff.mpr hxy, rfl⟩

/-- The two new rails. -/
lemma adj_none_some {x y : PathV 1} {w : PathV n} :
    (pathG 1 □ pathG (n + 1)).Adj (x, (none : PathV (n + 1))) (y, (some w : PathV (n + 1)))
      ↔ (x = y ∧ w = pathEnd n) := by
  rw [boxProd_adj]
  constructor
  · rintro (⟨_, he⟩ | ⟨hadj, hxy⟩)
    · exact absurd he (pathV_none_ne_some w)
    · exact ⟨hxy, show w = pathEnd n from hadj⟩
  · rintro ⟨hxy, hw⟩
    exact Or.inr ⟨show (pathG (n + 1)).Adj none (some w) from hw, hxy⟩

/-! ### Counting colourings by the colours of the last rung -/

/-- The top end of the last rung. -/
def lastT (n : ℕ) : PathV 1 × PathV n := (rowT, pathEnd n)

/-- The bottom end of the last rung. -/
def lastB (n : ℕ) : PathV 1 × PathV n := (rowB, pathEnd n)

lemma lastT_adj_lastB : (pathG 1 □ pathG n).Adj (lastT n) (lastB n) :=
  boxProd_adj.mpr (Or.inl ⟨pathOne_adj_iff.mpr rowT_ne_rowB, rfl⟩)

/-- The states available to the last rung. -/
def rung (M : ListAssignment (PathV 1 × PathV n)) : Finset (ℕ × ℕ) :=
  states (M (lastT n)) (M (lastB n))

/-- The number of colourings from `M` whose last rung is coloured `p`. -/
def cnt (n : ℕ) (M : ListAssignment (PathV 1 × PathV n)) (p : ℕ × ℕ) : ℕ :=
  (((pathG 1 □ pathG n).colorings M).filter fun f => f (lastT n) = p.1 ∧ f (lastB n) = p.2).card

/-- **Grading by the last rung.** Any property of the last rung's colours splits the colouring
count into the corresponding states. With `P = True` this is `col_eq_total`; with
`P = (· ≠ c ∧ · ≠ d)` it is the sum appearing in `Ladder.step`. -/
theorem card_filter_eq_sum (M : ListAssignment (PathV 1 × PathV n))
    (P : ℕ × ℕ → Prop) [DecidablePred P] :
    (((pathG 1 □ pathG n).colorings M).filter fun f => P (f (lastT n), f (lastB n))).card
      = ∑ p ∈ (rung M).filter P, cnt n M p := by
  classical
  have hmem : ∀ f ∈ ((pathG 1 □ pathG n).colorings M).filter
      (fun f => P (f (lastT n), f (lastB n))),
      (f (lastT n), f (lastB n)) ∈ (rung M).filter P := by
    intro f hf
    rw [Finset.mem_filter] at hf ⊢
    exact ⟨mem_states.mpr ⟨mem_list_of_mem_colorings hf.1 _, mem_list_of_mem_colorings hf.1 _,
      isProperColoring_of_mem_colorings hf.1 lastT_adj_lastB⟩, hf.2⟩
  rw [Finset.card_eq_sum_card_fiberwise hmem]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hPq : P q := (Finset.mem_filter.mp hq).2
  congr 1
  ext f
  simp only [Finset.mem_filter, cnt, Prod.ext_iff]
  constructor
  · rintro ⟨⟨hf, _⟩, h1, h2⟩; exact ⟨hf, h1, h2⟩
  · rintro ⟨hf, h1, h2⟩
    exact ⟨⟨hf, by rw [h1, h2]; exact hPq⟩, h1, h2⟩

/-- The colouring count is the total mass on the last rung. -/
theorem col_eq_total (M : ListAssignment (PathV 1 × PathV n)) :
    (pathG 1 □ pathG n).col M = total (rung M) (cnt n M) := by
  classical
  have := card_filter_eq_sum M (fun _ => True)
  simpa [col, total, Finset.filter_true_of_mem] using this

/-! ### One more column -/

/-- The list assignment inherited by the older columns. -/
def restrM (M : ListAssignment (PathV 1 × PathV (n + 1))) : ListAssignment (PathV 1 × PathV n) :=
  fun q => M (q.1, (some q.2 : PathV (n + 1)))

/-- Restricting a colouring to the older columns. -/
def restr (f : PathV 1 × PathV (n + 1) → ℕ) : PathV 1 × PathV n → ℕ :=
  fun q => f (q.1, (some q.2 : PathV (n + 1)))

/-- Extending a colouring of the older columns by a new rung coloured `p`. -/
def extd (p : ℕ × ℕ) (h : PathV 1 × PathV n → ℕ) : PathV 1 × PathV (n + 1) → ℕ :=
  fun q => Option.elim (show Option (PathV n) from q.2) (if q.1 = rowT then p.1 else p.2)
    fun v => h (q.1, v)

@[simp] lemma extd_some (p : ℕ × ℕ) (h : PathV 1 × PathV n → ℕ) (x : PathV 1) (v : PathV n) :
    extd p h (x, (some v : PathV (n + 1))) = h (x, v) := rfl

@[simp] lemma extd_lastT (p : ℕ × ℕ) (h : PathV 1 × PathV n → ℕ) :
    extd p h (lastT (n + 1)) = p.1 := by
  show (if rowT = rowT then p.1 else p.2) = p.1
  simp

@[simp] lemma extd_lastB (p : ℕ × ℕ) (h : PathV 1 × PathV n → ℕ) :
    extd p h (lastB (n + 1)) = p.2 := by
  show (if rowB = rowT then p.1 else p.2) = p.2
  simp [Ne.symm rowT_ne_rowB]

/-- **The column bijection.** Colourings of the longer ladder whose last rung is coloured `p`
correspond exactly to colourings of the shorter ladder that avoid `p` on the rung they abut:
restrict one way, extend by `p` the other. -/
theorem cnt_succ_aux (M : ListAssignment (PathV 1 × PathV (n + 1))) {p : ℕ × ℕ}
    (hp : p ∈ rung M) :
    cnt (n + 1) M p
      = (((pathG 1 □ pathG n).colorings (restrM M)).filter
          fun h => ¬ h (lastT n) = p.1 ∧ ¬ h (lastB n) = p.2).card := by
  classical
  obtain ⟨hp1, hp2, hpne⟩ := mem_states.mp hp
  rw [cnt]
  refine Finset.card_bij' (fun f _ => restr f) (fun h _ => extd p h) ?_ ?_ ?_ ?_
  · -- restriction lands in the shorter ladder, and avoids `p` on the abutting rung
    intro f hf
    rw [Finset.mem_filter, mem_colorings] at hf
    obtain ⟨⟨hmem, hprop⟩, hT, hB⟩ := hf
    rw [Finset.mem_filter, mem_colorings]
    refine ⟨⟨fun q => hmem _, fun a b hab => hprop (adj_some_some.mpr hab)⟩, ?_, ?_⟩
    · rw [← hT]
      exact hprop (SimpleGraph.Adj.symm
        (show (pathG 1 □ pathG (n + 1)).Adj (rowT, (none : PathV (n + 1)))
          (rowT, (some (pathEnd n) : PathV (n + 1))) from adj_none_some.mpr ⟨rfl, rfl⟩))
    · rw [← hB]
      exact hprop (SimpleGraph.Adj.symm
        (show (pathG 1 □ pathG (n + 1)).Adj (rowB, (none : PathV (n + 1)))
          (rowB, (some (pathEnd n) : PathV (n + 1))) from adj_none_some.mpr ⟨rfl, rfl⟩))
  · -- extension lands in the longer ladder, with the prescribed rung
    intro h hh
    rw [Finset.mem_filter, mem_colorings] at hh
    obtain ⟨⟨hmem, hprop⟩, hne1, hne2⟩ := hh
    -- the value at a new-column vertex, by row
    have hnew : ∀ x : PathV 1, extd p h (x, (none : PathV (n + 1)))
        = if x = rowT then p.1 else p.2 := fun _ => rfl
    -- a rail edge always separates
    have hmix : ∀ x : PathV 1, extd p h (x, (none : PathV (n + 1)))
        ≠ extd p h (x, (some (pathEnd n) : PathV (n + 1))) := by
      intro x
      rw [hnew, extd_some]
      rcases row_eq x with rfl | rfl
      · rw [if_pos rfl]
        exact fun hc => hne1 hc.symm
      · rw [if_neg (Ne.symm rowT_ne_rowB)]
        exact fun hc => hne2 hc.symm
    rw [Finset.mem_filter, mem_colorings]
    refine ⟨⟨?_, ?_⟩, extd_lastT p h, extd_lastB p h⟩
    · rintro ⟨x, q⟩
      match q with
      | some v => exact hmem (x, v)
      | none =>
          rw [hnew]
          rcases row_eq x with rfl | rfl
          · rw [if_pos rfl]; exact hp1
          · rw [if_neg (Ne.symm rowT_ne_rowB)]; exact hp2
    · rintro ⟨x, qx⟩ ⟨y, qy⟩ hab
      match qx, qy with
      | some v, some w => exact hprop (adj_some_some.mp hab)
      | none, none =>
          have hxy : x ≠ y := adj_none_none.mp hab
          rw [hnew, hnew]
          rcases row_eq x with rfl | rfl <;> rcases row_eq y with rfl | rfl
          · exact absurd rfl hxy
          · rw [if_pos rfl, if_neg (Ne.symm rowT_ne_rowB)]; exact hpne
          · rw [if_neg (Ne.symm rowT_ne_rowB), if_pos rfl]; exact Ne.symm hpne
          · exact absurd rfl hxy
      | none, some w =>
          obtain ⟨rfl, rfl⟩ := adj_none_some.mp hab
          exact hmix x
      | some v, none =>
          obtain ⟨rfl, rfl⟩ := adj_none_some.mp hab.symm
          exact Ne.symm (hmix y)
  · -- round trip on the longer ladder
    intro f hf
    rw [Finset.mem_filter] at hf
    funext q
    match q with
    | (x, some v) => rfl
    | (x, none) =>
        show (if x = rowT then p.1 else p.2) = f (x, (none : PathV (n + 1)))
        rcases row_eq x with rfl | rfl
        · rw [if_pos rfl]; exact hf.2.1.symm
        · rw [if_neg (Ne.symm rowT_ne_rowB)]; exact hf.2.2.symm
  · -- round trip on the shorter ladder
    intro h _
    funext q
    rfl

/-- The last-rung counts obey exactly the abstract transfer of `Ladder.step`. -/
theorem cnt_succ (M : ListAssignment (PathV 1 × PathV (n + 1))) {p : ℕ × ℕ} (hp : p ∈ rung M) :
    cnt (n + 1) M p = step (rung (restrM M)) (cnt n (restrM M)) p := by
  classical
  rw [cnt_succ_aux M hp, step]
  exact card_filter_eq_sum (restrM M) (fun q => ¬ q.1 = p.1 ∧ ¬ q.2 = p.2)

/-! ### The first column -/

/-- `pathG 1 □ pathG 0` has just the two ends of one rung. -/
lemma vertex_zero (q : PathV 1 × PathV 0) : q = lastT 0 ∨ q = lastB 0 := by
  obtain ⟨x, u⟩ := q
  have hu : u = pathEnd 0 := Subsingleton.elim u ()
  subst hu
  rcases row_eq x with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- A single rung has exactly one colouring per state. -/
theorem cnt_zero (M : ListAssignment (PathV 1 × PathV 0)) {p : ℕ × ℕ} (hp : p ∈ rung M) :
    cnt 0 M p = 1 := by
  classical
  obtain ⟨hp1, hp2, hpne⟩ := mem_states.mp hp
  set g : PathV 1 × PathV 0 → ℕ := fun q => if q.1 = rowT then p.1 else p.2 with hgdef
  have hgT : g (lastT 0) = p.1 := by
    show (if rowT = rowT then p.1 else p.2) = p.1
    simp
  have hgB : g (lastB 0) = p.2 := by
    show (if rowB = rowT then p.1 else p.2) = p.2
    simp [Ne.symm rowT_ne_rowB]
  have hset : (((pathG 1 □ pathG 0).colorings M).filter
      fun f => f (lastT 0) = p.1 ∧ f (lastB 0) = p.2) = {g} := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_singleton, mem_colorings]
    constructor
    · rintro ⟨_, hT, hB⟩
      funext q
      rcases vertex_zero q with rfl | rfl
      · rw [hgT]; exact hT
      · rw [hgB]; exact hB
    · rintro rfl
      refine ⟨⟨?_, ?_⟩, hgT, hgB⟩
      · intro q
        rcases vertex_zero q with rfl | rfl
        · rw [hgT]; exact hp1
        · rw [hgB]; exact hp2
      · intro a b hab
        rcases vertex_zero a with rfl | rfl <;> rcases vertex_zero b with rfl | rfl
        · exact absurd rfl hab.ne
        · rw [hgT, hgB]; exact hpne
        · rw [hgT, hgB]; exact Ne.symm hpne
        · exact absurd rfl hab.ne
  rw [cnt, hset, Finset.card_singleton]

/-! ### The theorem -/

/-- **The ladder transfer, on the graph.** At every column the last-rung counts satisfy the
invariant, and their total is at least the uniform count. -/
theorem ladder_main {k : ℕ} (hk : 3 ≤ k) :
    ∀ (n : ℕ) (M : ListAssignment (PathV 1 × PathV n)), IsNListAssignment M k →
      Inv (rung M) (cnt n M) ∧ k * (k - 1) * lam k ^ n ≤ total (rung M) (cnt n M) := by
  intro n
  induction n with
  | zero =>
      intro M hM
      have hagree : ∀ p ∈ rung M, (1 : ℕ) = cnt 0 M p := fun p hp => (cnt_zero M hp).symm
      refine ⟨inv_congr hagree (inv_ones hk (hM _) (hM _)), ?_⟩
      rw [← total_congr hagree]
      have hones : total (rung M) (fun _ => 1) = (rung M).card :=
        (Finset.card_eq_sum_ones _).symm
      have hge := card_states_ge (M (lastT 0)) (M (lastB 0))
      have hint : (M (lastT 0) ∩ M (lastB 0)).card ≤ k := by
        rw [← hM (lastT 0)]
        exact Finset.card_le_card Finset.inter_subset_left
      rw [hM (lastT 0), hM (lastB 0)] at hge
      rw [hones, pow_zero, Nat.mul_one]
      have : k * (k - 1) + k = k * k := by
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
        rw [show (j + 3 : ℕ) - 1 = j + 2 from rfl]
        ring
      have hrung : rung M = states (M (lastT 0)) (M (lastB 0)) := rfl
      rw [hrung]
      omega
  | succ n ih =>
      intro M hM
      have hM' : IsNListAssignment (restrM M) k := fun q => hM _
      obtain ⟨hInv, hTot⟩ := ih (restrM M) hM'
      have hagree : ∀ p ∈ rung M, step (rung (restrM M)) (cnt n (restrM M)) p = cnt (n + 1) M p :=
        fun p hp => (cnt_succ M hp).symm
      have hrung : rung M = states (M (lastT (n + 1))) (M (lastB (n + 1))) := rfl
      have hsub : ∀ p ∈ rung (restrM M), p.1 ≠ p.2 := fun p hp => states_ne hp
      refine ⟨inv_congr hagree ?_, ?_⟩
      · rw [hrung]
        exact inv_step hk (hM _) (hM _) hsub hInv
      · rw [← total_congr hagree, hrung, total_step]
        calc k * (k - 1) * lam k ^ (n + 1)
            = lam k * (k * (k - 1) * lam k ^ n) := by ring
          _ ≤ lam k * total (rung (restrM M)) (cnt n (restrM M)) := Nat.mul_le_mul_left _ hTot
          _ ≤ _ := lam_mul_total_le hk (hM _) (hM _) hsub hInv

/-- **Every `2 × (n+1)` grid is `k`-ECC for `k ≥ 3`**, in the counting form: no assignment of
`k`-element lists admits fewer colourings than `k(k-1)·lam k ^ n`. -/
theorem col_ge {k : ℕ} (hk : 3 ≤ k) (n : ℕ) (M : ListAssignment (PathV 1 × PathV n))
    (hM : IsNListAssignment M k) :
    k * (k - 1) * lam k ^ n ≤ (pathG 1 □ pathG n).col M := by
  rw [col_eq_total]
  exact (ladder_main hk n M hM).2

/-! ### The uniform count, exactly -/

/-- With uniform lists every rung offers exactly `lam k` successors, so the count is exactly
`k(k-1)·lam k ^ n`. This is what makes `col_ge` tight, and it is what `ECCAt` compares against. -/
theorem total_const {k : ℕ} (hk : 3 ≤ k) (n : ℕ) :
    total (rung (constList (PathV 1 × PathV n) k)) (cnt n (constList (PathV 1 × PathV n) k))
      = k * (k - 1) * lam k ^ n := by
  classical
  induction n with
  | zero =>
      have hagree : ∀ p ∈ rung (constList (PathV 1 × PathV 0) k),
          (1 : ℕ) = cnt 0 (constList (PathV 1 × PathV 0) k) p := fun p hp => (cnt_zero _ hp).symm
      rw [← total_congr hagree, show total (rung (constList (PathV 1 × PathV 0) k)) (fun _ => 1)
        = (rung (constList (PathV 1 × PathV 0) k)).card from (Finset.card_eq_sum_ones _).symm]
      have hadd := card_states_add (Finset.range k) (Finset.range k)
      rw [Finset.inter_self, Finset.card_range] at hadd
      have hrung : (rung (constList (PathV 1 × PathV 0) k)).card
          = (states (Finset.range k) (Finset.range k)).card := rfl
      have hkk : k * (k - 1) + k = k * k := by
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
        rw [show (j + 3 : ℕ) - 1 = j + 2 from rfl]
        ring
      rw [hrung, pow_zero, Nat.mul_one]
      omega
  | succ n ih =>
      have hagree : ∀ p ∈ rung (constList (PathV 1 × PathV (n + 1)) k),
          step (rung (restrM (constList (PathV 1 × PathV (n + 1)) k)))
            (cnt n (restrM (constList (PathV 1 × PathV (n + 1)) k))) p
          = cnt (n + 1) (constList (PathV 1 × PathV (n + 1)) k) p :=
        fun p hp => (cnt_succ _ hp).symm
      have hrestr : restrM (constList (PathV 1 × PathV (n + 1)) k)
          = constList (PathV 1 × PathV n) k := rfl
      rw [← total_congr hagree,
        show rung (constList (PathV 1 × PathV (n + 1)) k)
          = states (Finset.range k) (Finset.range k) from rfl, total_step, hrestr]
      have hext : ∀ p ∈ rung (constList (PathV 1 × PathV n) k),
          cnt n (constList (PathV 1 × PathV n) k) p
              * ext (Finset.range k) (Finset.range k) p.1 p.2
            = lam k * cnt n (constList (PathV 1 × PathV n) k) p := by
        intro p hp
        obtain ⟨h1, h2, hne⟩ := mem_states.mp hp
        rw [ext_const h1 h2 hne, mul_comm]
      rw [Finset.sum_congr rfl hext, ← Finset.mul_sum, ← total, ih]
      ring

/-- The uniform count on the `2 × (n+1)` grid. -/
theorem colConst_eq {k : ℕ} (hk : 3 ≤ k) (n : ℕ) :
    (pathG 1 □ pathG n).colConst k = k * (k - 1) * lam k ^ n := by
  rw [colConst, col_eq_total]
  exact total_const hk n

/-- **Ladders are `k`-ECC for every `k ≥ 3`.** The `2 × (n+1)` grid is enumeratively
chromatic-choosable at every list size `k ≥ 3`: no assignment of `k`-element lists admits fewer
colourings than the constant one. -/
theorem ecc_ladder {k : ℕ} (hk : 3 ≤ k) (n : ℕ) : (pathG 1 □ pathG n).ECCAt k := by
  intro M hM
  rw [colConst_eq hk n]
  exact col_ge hk n M hM

end Ladder
