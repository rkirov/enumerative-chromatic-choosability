/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Eight.Holes

/-!
# Realizing a label permutation in a prescribed order

At a row edge the moves make the lower row's labels of the shared colours agree with the upper
row's. `realizeH` builds them one at a time through an arbitrary mismatched colour. At `k = 7` the
order matters: each move is charged to the star of its colour, and a star used at two consecutive
edges should see its two moves with as few moves in between as possible. `realizeOrd` processes
the colours in the order of a given list. It returns the moves in application order, each tagged
with its colour, as `(colour, current lower label, upper label)`.

* `realizeOrd_spec`: the moves are small, at most one per colour of the list, and they realize the
  permutation when the list contains every mismatched colour;
* `realizeOrd_get`: the move of a colour is through that colour's *current* lower label, i.e. its
  initial lower label moved by the moves applied before.
-/

open Finset

set_option linter.unusedSectionVars false

namespace GridGen.Gauge

/-- Apply transpositions in list order (the head first). -/
def compA : List (ℕ × ℕ) → ℕ → ℕ
  | [] => id
  | p :: ts => fun z => compA ts (Equiv.swap p.1 p.2 z)

theorem compA_nil (z : ℕ) : compA [] z = z := rfl

theorem compA_cons (p : ℕ × ℕ) (ts : List (ℕ × ℕ)) (z : ℕ) :
    compA (p :: ts) z = compA ts (Equiv.swap p.1 p.2 z) := rfl

theorem compA_append : ∀ (ts ts' : List (ℕ × ℕ)) (z : ℕ),
    compA (ts ++ ts') z = compA ts' (compA ts z)
  | [], _, _ => rfl
  | p :: ts, ts', z => by
      simp only [List.cons_append, compA_cons]
      exact compA_append ts ts' _

/-- `comp` applies the head last; `compA` the head first. -/
theorem comp_reverse : ∀ (ts : List (ℕ × ℕ)) (z : ℕ), comp ts.reverse z = compA ts z
  | [], _ => rfl
  | p :: ts, z => by
      rw [List.reverse_cons, comp_append, comp_cons, comp_nil, compA_cons]
      exact comp_reverse ts _

theorem compA_injective : ∀ ts : List (ℕ × ℕ), Function.Injective (compA ts)
  | [] => fun _ _ h => h
  | p :: ts => fun _ _ h => (Equiv.swap p.1 p.2).injective (compA_injective ts h)

/-- **The ordered realization.** The moves in application order, as
`(colour, current lower label, upper label)`. -/
def realizeOrd (h : ℕ → ℕ) : List ℕ → (ℕ → ℕ) → List (ℕ × ℕ × ℕ)
  | [], _ => []
  | c :: rest, g =>
      if g c = h c then realizeOrd h rest g
      else (c, g c, h c) :: realizeOrd h rest (fun z => Equiv.swap (g c) (h c) (g z))

/-- The transpositions of the realization. -/
def movesOf (L : List (ℕ × ℕ × ℕ)) : List (ℕ × ℕ) := L.map fun t => (t.2.1, t.2.2)

theorem swap_lt {k a b z : ℕ} (ha : a < k) (hb : b < k) (hz : z < k) : Equiv.swap a b z < k := by
  rcases eq_or_ne z a with rfl | h1
  · rw [Equiv.swap_apply_left]; exact hb
  rcases eq_or_ne z b with rfl | h2
  · rw [Equiv.swap_apply_right]; exact ha
  rw [Equiv.swap_apply_of_ne_of_ne h1 h2]; exact hz

/-- **The ordered realization realizes the permutation.** If `g` and `h` are injective on `C` with
values below `k`, the list has no duplicates, lies in `C`, and contains every colour of `C` where
`g` and `h` differ, then the moves are small, there is at most one per colour of the list, and
they carry `g` to `h` on `C`. -/
theorem realizeOrd_spec {k : ℕ} (C : Finset ℕ) (h : ℕ → ℕ) :
    ∀ (ord : List ℕ) (g : ℕ → ℕ), ord.Nodup → (∀ c ∈ ord, c ∈ C) →
      Set.InjOn g C → Set.InjOn h C → (∀ c ∈ C, g c < k) → (∀ c ∈ C, h c < k) →
      (∀ c ∈ C, g c ≠ h c → c ∈ ord) →
        Small k (movesOf (realizeOrd h ord g)) ∧ (realizeOrd h ord g).length ≤ ord.length ∧
          (∀ c ∈ C, compA (movesOf (realizeOrd h ord g)) (g c) = h c) ∧
            (∀ t ∈ realizeOrd h ord g, t.1 ∈ ord ∧ g t.1 ≠ h t.1) := by
  intro ord
  induction ord with
  | nil =>
      intro g _ _ _ _ _ _ hmis
      refine ⟨fun p hp => by simp [realizeOrd, movesOf] at hp, by simp [realizeOrd], fun c hc => ?_,
        fun t ht => by simp [realizeOrd] at ht⟩
      by_contra hne
      exact absurd (hmis c hc hne) (List.not_mem_nil)
  | cons c₀ rest ih =>
      intro g hnd hord hg hh hgk hhk hmis
      rw [List.nodup_cons] at hnd
      have hc₀ : c₀ ∈ C := hord c₀ (by simp)
      have hrest : ∀ c ∈ rest, c ∈ C := fun c hc => hord c (by simp [hc])
      by_cases e₀ : g c₀ = h c₀
      · -- already matched: skip
        simp only [realizeOrd, ite_eq_left e₀]
        have hmis' : ∀ c ∈ C, g c ≠ h c → c ∈ rest := by
          intro c hc hne
          rcases List.mem_cons.mp (hmis c hc hne) with rfl | h'
          · exact absurd e₀ hne
          · exact h'
        obtain ⟨h1, h2, h3, h4⟩ := ih g hnd.2 hrest hg hh hgk hhk hmis'
        refine ⟨h1, by simp only [List.length_cons]; omega, h3, fun t ht => ?_⟩
        obtain ⟨ht1, ht2⟩ := h4 t ht
        exact ⟨List.mem_cons_of_mem _ ht1, ht2⟩
      · simp only [realizeOrd, ite_eq_right e₀]
        set a := g c₀
        set b := h c₀
        set g' : ℕ → ℕ := fun z => Equiv.swap a b (g z) with hg'
        have hg'inj : Set.InjOn g' C := fun c hc c' hc' e =>
          hg hc hc' ((Equiv.swap a b).injective e)
        have hg'k : ∀ c ∈ C, g' c < k := fun c hc =>
          swap_lt (hgk c₀ hc₀) (hhk c₀ hc₀) (hgk c hc)
        -- after the swap, `c₀` is matched and matched colours stay matched
        have hmis' : ∀ c ∈ C, g' c ≠ h c → c ∈ rest := by
          intro c hc hne
          have hne' : g c ≠ h c := by
            intro e
            apply hne
            show Equiv.swap a b (g c) = h c
            have hca : g c ≠ a := by
              intro e'
              have := hg hc hc₀ e'
              subst this; exact e₀ e
            have hcb : g c ≠ b := by
              intro e'
              have := hh hc hc₀ (e.symm.trans e')
              subst this; exact e₀ e
            rw [Equiv.swap_apply_of_ne_of_ne hca hcb, e]
          rcases List.mem_cons.mp (hmis c hc hne') with e | h'
          · exfalso; apply hne
            rw [e]
            show Equiv.swap a b (g c₀) = h c₀
            have ha : g c₀ = a := rfl
            rw [ha, Equiv.swap_apply_left]
          · exact h'
        obtain ⟨h1, h2, h3, h4⟩ := ih g' hnd.2 hrest hg'inj hh hg'k hhk hmis'
        refine ⟨?_, by simp only [List.length_cons]; omega, fun c hc => ?_, fun t ht => ?_⟩
        · intro p hp
          simp only [movesOf, List.map_cons, List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact ⟨hgk c₀ hc₀, hhk c₀ hc₀⟩
          · exact h1 p hp
        · simp only [movesOf, List.map_cons, compA_cons]
          exact h3 c hc
        · rcases List.mem_cons.mp ht with rfl | ht
          · exact ⟨by simp, e₀⟩
          · obtain ⟨ht1, ht2⟩ := h4 t ht
            refine ⟨List.mem_cons_of_mem _ ht1, fun e => ?_⟩
            -- `t.1` is mismatched for `g'`, hence for `g`
            apply ht2
            show Equiv.swap a b (g t.1) = h t.1
            have htC := hrest t.1 ht1
            have hne : t.1 ≠ c₀ := fun e' => hnd.1 (e' ▸ ht1)
            have hca : g t.1 ≠ a := fun e' => hne (hg htC hc₀ e')
            have hcb : g t.1 ≠ b := fun e' => hne (hh htC hc₀ (e.symm.trans e'))
            rw [Equiv.swap_apply_of_ne_of_ne hca hcb, e]

/-- The colours of the moves form a sublist of the order. -/
theorem realizeOrd_sublist (h : ℕ → ℕ) :
    ∀ (ord : List ℕ) (g : ℕ → ℕ), ((realizeOrd h ord g).map Prod.fst).Sublist ord := by
  intro ord
  induction ord with
  | nil => intro g; simp [realizeOrd]
  | cons c₀ rest ih =>
      intro g
      by_cases e₀ : g c₀ = h c₀
      · simp only [realizeOrd, ite_eq_left e₀]
        exact (ih g).cons c₀
      · simp only [realizeOrd, ite_eq_right e₀, List.map_cons]
        exact (ih _).cons_cons c₀

/-- **Each move goes through the current lower label of its colour.** The `i`-th move is
`(c, x, h c)` with `x` the initial lower label `g c` moved by the moves applied before. -/
theorem realizeOrd_get (h : ℕ → ℕ) :
    ∀ (ord : List ℕ) (g : ℕ → ℕ) (i : ℕ) (hi : i < (realizeOrd h ord g).length),
      ((realizeOrd h ord g)[i]).2.1 =
          compA (movesOf ((realizeOrd h ord g).take i)) (g (realizeOrd h ord g)[i].1) ∧
        ((realizeOrd h ord g)[i]).2.2 = h (realizeOrd h ord g)[i].1 := by
  intro ord
  induction ord with
  | nil => intro g i hi; simp [realizeOrd] at hi
  | cons c₀ rest ih =>
      intro g i hi
      by_cases e₀ : g c₀ = h c₀
      · simp only [realizeOrd, ite_eq_left e₀] at hi ⊢
        exact ih g i hi
      · simp only [realizeOrd, ite_eq_right e₀] at hi ⊢
        cases i with
        | zero => simp [movesOf, compA_nil]
        | succ i =>
            simp only [List.length_cons] at hi
            have := ih (fun z => Equiv.swap (g c₀) (h c₀) (g z)) i (by omega)
            simp only [List.getElem_cons_succ, List.take_succ_cons, movesOf, List.map_cons,
              compA_cons] at this ⊢
            exact this

/-! ### The ordered gauge of a seam -/

section GlueO

open scoped Classical

variable (k : ℕ) (Ax Bx : ℕ → Finset ℕ) (βx : ℕ → ℕ → ℕ)

/-- A *double* of row `v`: a colour new in row `v`, shared with both neighbouring rows, mismatched
at both edges of row `v`, and old in row `v + 1`. Its star in row `v` serves two moves. -/
def Dbl (v c : ℕ) : Prop :=
  1 ≤ v ∧ c ∈ Bx (v - 1) ∧ c ∈ Bx v ∧ c ∈ Bx (v + 1) ∧ c ∉ Ax v ∧ c ∈ Ax (v + 1) ∧
    βx v c ≠ βx (v - 1) c ∧ βx (v + 1) c ≠ βx v c

/-- The order of the shared colours at the edge below row `v`: the doubles of row `v` first, the
doubles of row `v + 1` last, each part increasing. -/
noncomputable def ordO (v : ℕ) : List ℕ :=
  ((Bx v ∩ Bx (v + 1)).sort (· ≤ ·)).filter (fun c => Dbl Ax Bx βx v c) ++
    ((Bx v ∩ Bx (v + 1)).sort (· ≤ ·)).filter
      (fun c => ¬ Dbl Ax Bx βx v c ∧ ¬ Dbl Ax Bx βx (v + 1) c) ++
    ((Bx v ∩ Bx (v + 1)).sort (· ≤ ·)).filter (fun c => Dbl Ax Bx βx (v + 1) c)

/-- The moves at the edge below row `v`, in the order `ordO`, after the rows above have been
conjugated by `comp pl`. In `comp` convention (the head applied last). -/
noncomputable def rhoO (v : ℕ) (pl : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  (movesOf (realizeOrd (fun c => comp pl (βx v c)) (ordO Ax Bx βx v)
    (fun c => comp pl (βx (v + 1) c)))).reverse

/-- The accumulated conjugation of row `v`. -/
noncomputable def piLO : ℕ → List (ℕ × ℕ)
  | 0 => []
  | v + 1 => rhoO Ax Bx βx v (piLO v) ++ piLO v

/-- **The glued labelling, in the prescribed order.** -/
noncomputable def glueLabO (v : ℕ) (a : ℕ) : ℕ := comp (piLO Ax Bx βx v) (βx v a)

variable {k Ax Bx βx}

theorem not_dbl_and (v c : ℕ) : ¬ (Dbl Ax Bx βx v c ∧ Dbl Ax Bx βx (v + 1) c) := by
  rintro ⟨h1, h2⟩
  exact h2.2.2.2.2.1 h1.2.2.2.2.2.1

theorem mem_ordO {v c : ℕ} : c ∈ ordO Ax Bx βx v ↔ c ∈ Bx v ∩ Bx (v + 1) := by
  unfold ordO
  simp only [List.mem_append, List.mem_filter, mem_sort, decide_eq_true_eq]
  constructor
  · rintro ((⟨h, -⟩ | ⟨h, -⟩) | ⟨h, -⟩) <;> exact h
  · intro h
    by_cases h1 : Dbl Ax Bx βx v c
    · exact Or.inl (Or.inl ⟨h, h1⟩)
    by_cases h2 : Dbl Ax Bx βx (v + 1) c
    · exact Or.inr ⟨h, h2⟩
    · exact Or.inl (Or.inr ⟨h, h1, h2⟩)

theorem nodup_ordO (v : ℕ) : (ordO Ax Bx βx v).Nodup := by
  have hL := sort_nodup (Bx v ∩ Bx (v + 1)) (· ≤ ·)
  unfold ordO
  refine List.Nodup.append (List.Nodup.append (hL.filter _) (hL.filter _) ?_) (hL.filter _) ?_
  · intro a ha hb
    simp only [List.mem_filter, decide_eq_true_eq] at ha hb
    exact hb.2.1 ha.2
  · intro a ha hb
    simp only [List.mem_append, List.mem_filter, decide_eq_true_eq] at ha hb
    rcases ha with ⟨-, h⟩ | ⟨-, -, h⟩
    · exact not_dbl_and v a ⟨h, hb.2⟩
    · exact h hb.2

/-- **The moves at one edge, in order.** -/
theorem rhoO_spec (hR : RowLab k Bx βx) {pl : List (ℕ × ℕ)} (hpl : Small k pl) (v : ℕ) :
    (rhoO Ax Bx βx v pl).length ≤ ((Bx v ∩ Bx (v + 1)).filter
        fun c => comp pl (βx (v + 1) c) ≠ comp pl (βx v c)).card ∧
      Small k (rhoO Ax Bx βx v pl) ∧ (∀ c ∈ Bx v ∩ Bx (v + 1),
        comp (rhoO Ax Bx βx v pl) (comp pl (βx (v + 1) c)) = comp pl (βx v c)) := by
  obtain ⟨hg, hh, hgk, hhk⟩ := rgood hR hpl v
  obtain ⟨h1, -, h3, h4⟩ := realizeOrd_spec (k := k) (Bx v ∩ Bx (v + 1))
    (fun c => comp pl (βx v c)) (ordO Ax Bx βx v) (fun c => comp pl (βx (v + 1) c))
    (nodup_ordO v) (fun c hc => mem_ordO.mp hc) hg hh hgk hhk
    (fun c hc _ => mem_ordO.mpr hc)
  set R := realizeOrd (fun c => comp pl (βx v c)) (ordO Ax Bx βx v)
    (fun c => comp pl (βx (v + 1) c))
  refine ⟨?_, fun p hp => h1 p (List.mem_reverse.mp hp), fun c hc => ?_⟩
  · -- one move per mismatched colour
    have hnd : (R.map Prod.fst).Nodup := (nodup_ordO v).sublist (realizeOrd_sublist _ _ _)
    have hsub : (R.map Prod.fst).toFinset ⊆ (Bx v ∩ Bx (v + 1)).filter
        fun c => comp pl (βx (v + 1) c) ≠ comp pl (βx v c) := by
      intro c hc
      rw [List.mem_toFinset, List.mem_map] at hc
      obtain ⟨t, ht, rfl⟩ := hc
      obtain ⟨ht1, ht2⟩ := h4 t ht
      exact mem_filter.mpr ⟨mem_ordO.mp ht1, ht2⟩
    have := card_le_card hsub
    rw [List.toFinset_card_of_nodup hnd, List.length_map] at this
    simp only [rhoO, movesOf, List.length_reverse, List.length_map]
    exact this
  · simp only [rhoO]
    rw [comp_reverse]
    exact h3 c hc

theorem small_piLO (hR : RowLab k Bx βx) : ∀ v, Small k (piLO Ax Bx βx v)
  | 0 => fun _ hp => by simp [piLO] at hp
  | v + 1 => by
      intro p hp
      simp only [piLO, List.mem_append] at hp
      rcases hp with hp | hp
      · exact (rhoO_spec hR (small_piLO hR v) v).2.1 p hp
      · exact small_piLO hR v p hp

/-- **Vertical consistency of the ordered gauge.** -/
theorem glueLabO_vc (hR : RowLab k Bx βx) (v : ℕ) {c : ℕ} (hc : c ∈ Bx v ∩ Bx (v + 1)) :
    glueLabO Ax Bx βx (v + 1) c = glueLabO Ax Bx βx v c := by
  unfold glueLabO
  simp only [piLO]
  rw [comp_append]
  exact (rhoO_spec hR (small_piLO hR v) v).2.2 c hc

theorem glueLabO_injOn (hR : RowLab k Bx βx) (v : ℕ) : Set.InjOn (glueLabO Ax Bx βx v) (Bx v) :=
  fun _ ha _ ha' e => (hR v).1 ha ha' (comp_injective _ e)

theorem glueLabO_lt (hR : RowLab k Bx βx) (v : ℕ) {a : ℕ} (ha : a ∈ Bx v) :
    glueLabO Ax Bx βx v a < k :=
  comp_lt (small_piLO hR v) ((hR v).2 a ha)

/-- **The moves at one edge**: at most the new colours of the lower row plus the vertical
difference of the old column. -/
theorem length_rhoO_le (hR : RowLab k Bx βx) (hN : NewMis Ax Bx βx) (v : ℕ) :
    (rhoO Ax Bx βx v (piLO Ax Bx βx v)).length ≤
      (Bx (v + 1) \ Ax (v + 1)).card + (Ax (v + 1) \ Ax v).card := by
  refine le_trans (rhoO_spec hR (small_piLO hR v) v).1 (le_trans (le_of_eq ?_)
    (card_mismatchH_le hN v))
  congr 1
  ext c
  simp only [mem_filter]
  exact and_congr_right fun _ =>
    ⟨fun h e => h (by rw [e]), fun h e => h (comp_injective _ e)⟩

end GlueO

/-! ### The lookahead process

At the edge below row `e`, a colour `c` that is new in row `e + 1` and old in row `e + 2` uses the
star of row `e + 1` twice when it is mismatched at both edges. The process then first applies the
move at the edge below row `e + 1` (making row `e + 2` agree with row `e + 1`), and immediately
after, the move at the edge below row `e`. Moves at the edge below row `e + 1` do not touch rows
`≤ e + 1`, so restricted to the edge below row `e` the process is the ordered realization. -/

section Lookahead

open scoped Classical

variable (Ax Bx : ℕ → Finset ℕ) (βx : ℕ → ℕ → ℕ)

/-- A global move: `(edge, x, y)` swaps `x, y` in the keys of the rows below the edge. -/
abbrev GOp := ℕ × ℕ × ℕ

/-- The moves that act on row `u`, in application order. -/
def actOn (O : List GOp) (u : ℕ) : List (ℕ × ℕ) :=
  (O.filter (fun o => o.1 < u)).map fun o => (o.2.1, o.2.2)

/-- The current label in row `u` of the label `z`. -/
def curL (O : List GOp) (u z : ℕ) : ℕ := compA (actOn O u) z

/-- Colours that may look ahead at the edge below row `e`. -/
def Look (e c : ℕ) : Prop := c ∈ Bx (e + 2) ∧ c ∉ Ax (e + 1) ∧ c ∈ Ax (e + 2)

/-- One colour at the edge below row `e`. -/
noncomputable def stepC (e : ℕ) (O : List GOp) (c : ℕ) : List GOp :=
  if curL O (e + 1) (βx (e + 1) c) = curL O e (βx e c) then O
  else if Look Ax Bx e c ∧ curL O (e + 2) (βx (e + 2) c) ≠ curL O (e + 1) (βx (e + 1) c) then
    O ++ [(e + 1, curL O (e + 2) (βx (e + 2) c), curL O (e + 1) (βx (e + 1) c)),
      (e, curL O (e + 1) (βx (e + 1) c), curL O e (βx e c))]
  else O ++ [(e, curL O (e + 1) (βx (e + 1) c), curL O e (βx e c))]

/-- The order of the shared colours at an edge. -/
noncomputable def ordE (e : ℕ) : List ℕ := (Bx e ∩ Bx (e + 1)).sort (· ≤ ·)

/-- The edge below row `e`. -/
noncomputable def runEdge (e : ℕ) (O : List GOp) : List GOp :=
  (ordE Bx e).foldl (stepC Ax Bx βx e) O

/-- The process over the edges `0, …, e - 1`. -/
noncomputable def proc : ℕ → List GOp
  | 0 => []
  | e + 1 => runEdge Ax Bx βx e (proc e)

/-- **The lookahead gauge.** -/
noncomputable def glue7 (n v a : ℕ) : ℕ := curL (proc Ax Bx βx n) v (βx v a)

variable {k : ℕ} {Ax Bx βx}

theorem actOn_append (O O' : List GOp) (u : ℕ) : actOn (O ++ O') u = actOn O u ++ actOn O' u := by
  simp [actOn, List.filter_append]

theorem curL_append (O O' : List GOp) (u z : ℕ) : curL (O ++ O') u z = compA (actOn O' u) (curL O u z) := by
  simp only [curL, actOn_append, compA_append]

/-- Moves at edges `≥ u` do not act on row `u`. -/
theorem actOn_eq_nil {O : List GOp} {u : ℕ} (h : ∀ o ∈ O, u ≤ o.1) : actOn O u = [] := by
  simp only [actOn, List.map_eq_nil_iff, List.filter_eq_nil_iff, decide_eq_true_eq, not_lt]
  exact h

theorem curL_append_ge {O O' : List GOp} {u : ℕ} (h : ∀ o ∈ O', u ≤ o.1) (z : ℕ) :
    curL (O ++ O') u z = curL O u z := by
  rw [curL_append, actOn_eq_nil h]; rfl

theorem actOn_single (e x y u : ℕ) :
    actOn [((e, x, y) : GOp)] u = if e < u then [(x, y)] else [] := by
  unfold actOn; split_ifs with h <;> simp [h]

/-- **One edge, projected on itself, is the ordered realization.** -/
theorem foldl_stepC_spec (e : ℕ) :
    ∀ (ord : List ℕ) (O₀ : List GOp), ∃ N : List GOp,
      ord.foldl (stepC Ax Bx βx e) O₀ = O₀ ++ N ∧ (∀ o ∈ N, o.1 = e ∨ o.1 = e + 1) ∧
        actOn N (e + 1) = movesOf (realizeOrd (fun c => curL O₀ e (βx e c)) ord
          (fun c => curL O₀ (e + 1) (βx (e + 1) c))) := by
  intro ord
  induction ord with
  | nil => intro O₀; exact ⟨[], by simp, by simp, by simp [actOn, realizeOrd, movesOf]⟩
  | cons c rest ih =>
      intro O₀
      simp only [List.foldl_cons]
      by_cases e₀ : curL O₀ (e + 1) (βx (e + 1) c) = curL O₀ e (βx e c)
      · have hs : stepC Ax Bx βx e O₀ c = O₀ := by
          unfold stepC; rw [ite_eq_left e₀]
        rw [hs]
        obtain ⟨N, h1, h2, h3⟩ := ih O₀
        refine ⟨N, h1, h2, ?_⟩
        rw [h3]
        simp only [realizeOrd]
        rw [ite_eq_left e₀]
      · -- the step appends `S`, whose only move acting on row `e + 1` is `(g, h)`
        obtain ⟨S, hS, hSe, hSact⟩ : ∃ S : List GOp, stepC Ax Bx βx e O₀ c = O₀ ++ S ∧
            (∀ o ∈ S, o.1 = e ∨ o.1 = e + 1) ∧
            actOn S (e + 1) = [(curL O₀ (e + 1) (βx (e + 1) c), curL O₀ e (βx e c))] := by
          unfold stepC
          rw [ite_eq_right e₀]
          split_ifs with hl
          · exact ⟨_, rfl, by simp, by simp [actOn]⟩
          · exact ⟨_, rfl, by simp, by simp [actOn]⟩
        rw [hS]
        obtain ⟨N, h1, h2, h3⟩ := ih (O₀ ++ S)
        refine ⟨S ++ N, by rw [h1, List.append_assoc], ?_, ?_⟩
        · intro o ho
          rcases List.mem_append.mp ho with ho | ho
          · exact hSe o ho
          · exact h2 o ho
        · have hrow : ∀ z, curL (O₀ ++ S) e z = curL O₀ e z := fun z =>
            curL_append_ge (fun o ho => by rcases hSe o ho with h' | h' <;> omega) z
          have hrow1 : ∀ z, curL (O₀ ++ S) (e + 1) z = Equiv.swap (curL O₀ (e + 1) (βx (e + 1) c))
              (curL O₀ e (βx e c)) (curL O₀ (e + 1) z) := by
            intro z; rw [curL_append, hSact]; rfl
          rw [actOn_append, hSact, h3]
          simp only [hrow, hrow1]
          conv_rhs => rw [realizeOrd, ite_eq_right e₀]
          rfl

/-- **The edge below row `e` makes rows `e` and `e + 1` agree**, and adds only moves at the edges
below rows `e` and `e + 1`. -/
theorem runEdge_spec (hR : RowLab k Bx βx) (e : ℕ) (O₀ : List GOp)
    (hO : Small k (actOn O₀ (e + 1))) (hO' : Small k (actOn O₀ e)) :
    ∃ N : List GOp, runEdge Ax Bx βx e O₀ = O₀ ++ N ∧ (∀ o ∈ N, o.1 = e ∨ o.1 = e + 1) ∧
      (∀ c ∈ Bx e ∩ Bx (e + 1),
        curL (runEdge Ax Bx βx e O₀) (e + 1) (βx (e + 1) c) =
          curL (runEdge Ax Bx βx e O₀) e (βx e c)) ∧
      Small k (actOn N (e + 1)) := by
  obtain ⟨N, h1, h2, h3⟩ := foldl_stepC_spec (Ax := Ax) (Bx := Bx) (βx := βx) e (ordE Bx e) O₀
  have hg : Set.InjOn (fun c => curL O₀ (e + 1) (βx (e + 1) c))
      ((Bx e ∩ Bx (e + 1) : Finset ℕ) : Set ℕ) :=
    fun c hc c' hc' h => by
      rw [mem_coe, mem_inter] at hc hc'
      exact (hR (e + 1)).1 hc.2 hc'.2 (compA_injective _ h)
  have hh : Set.InjOn (fun c => curL O₀ e (βx e c)) ((Bx e ∩ Bx (e + 1) : Finset ℕ) : Set ℕ) :=
    fun c hc c' hc' h => by
      rw [mem_coe, mem_inter] at hc hc'
      exact (hR e).1 hc.1 hc'.1 (compA_injective _ h)
  have hlt : ∀ (u : ℕ) (O : List GOp), Small k (actOn O u) → ∀ z, z < k → curL O u z < k := by
    intro u O hO z hz
    unfold curL
    rw [← comp_reverse]
    exact comp_lt (fun p hp => hO p (List.mem_reverse.mp hp)) hz
  obtain ⟨s1, -, s3, -⟩ := realizeOrd_spec (k := k) (Bx e ∩ Bx (e + 1))
    (fun c => curL O₀ e (βx e c)) (ordE Bx e) (fun c => curL O₀ (e + 1) (βx (e + 1) c))
    (sort_nodup _ _) (fun c hc => (mem_sort _).mp hc) hg hh
    (fun c hc => hlt _ _ hO _ ((hR (e + 1)).2 c (mem_inter.mp hc).2))
    (fun c hc => hlt _ _ hO' _ ((hR e).2 c (mem_inter.mp hc).1))
    (fun c hc _ => (mem_sort _).mpr hc)
  have hrun : runEdge Ax Bx βx e O₀ = O₀ ++ N := h1
  refine ⟨N, hrun, h2, fun c hc => ?_, by rw [h3]; exact s1⟩
  rw [hrun, curL_append, h3, curL_append_ge (fun o ho => by rcases h2 o ho with h' | h' <;> omega)]
  exact s3 c hc

/-- Colour `c` is matched at the edge below row `e` after the moves `O`. -/
def Matched (O : List GOp) (e c : ℕ) : Prop := curL O (e + 1) (βx (e + 1) c) = curL O e (βx e c)

/-- A move *on colour `d`* at the edge below row `e'`: it swaps `d`'s current labels in rows
`e' + 1` and `e'`, which differ. -/
def OnColour (O : List GOp) (e' d : ℕ) (o : GOp) : Prop :=
  d ∈ Bx e' ∧ d ∈ Bx (e' + 1) ∧ o = (e', curL O (e' + 1) (βx (e' + 1) d), curL O e' (βx e' d)) ∧
    ¬ Matched (βx := βx) O e' d

theorem curL_snoc (O : List GOp) (o : GOp) (u z : ℕ) :
    curL (O ++ [o]) u z = if o.1 < u then Equiv.swap o.2.1 o.2.2 (curL O u z) else curL O u z := by
  rw [curL_append]
  obtain ⟨e, x, y⟩ := o
  rw [actOn_single]
  split_ifs <;> rfl

/-- **A move on one colour keeps every other match.** -/
theorem matched_snoc (hR : RowLab k Bx βx) {O : List GOp} {e' d : ℕ} {o : GOp}
    (ho : OnColour (Bx := Bx) (βx := βx) O e' d o) {e c : ℕ} (hc : c ∈ Bx e ∧ c ∈ Bx (e + 1))
    (hm : Matched (βx := βx) O e c) : Matched (βx := βx) (O ++ [o]) e c := by
  obtain ⟨hd1, hd2, rfl, hne⟩ := ho
  unfold Matched at hm ⊢
  rw [curL_snoc, curL_snoc]
  simp only
  by_cases h1 : e' < e
  · rw [ite_eq_left (by omega), ite_eq_left h1, hm]
  by_cases h2 : e' = e
  · subst h2
    rw [ite_eq_left (by omega), ite_eq_right (lt_irrefl _), hm]
    have hcd : c ≠ d := fun h => hne (h ▸ hm)
    refine Equiv.swap_apply_of_ne_of_ne (fun h => hcd ?_) (fun h => hcd ?_)
    · exact (hR (e' + 1)).1 hc.2 hd2 (compA_injective _ (hm.trans h))
    · exact (hR e').1 hc.1 hd1 (compA_injective _ h)
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), hm]

/-- **A move on a colour matches it.** -/
theorem matched_snoc_self {O : List GOp} {e' d : ℕ} {o : GOp}
    (ho : OnColour (Bx := Bx) (βx := βx) O e' d o) : Matched (βx := βx) (O ++ [o]) e' d := by
  obtain ⟨-, -, rfl, -⟩ := ho
  unfold Matched
  rw [curL_snoc, curL_snoc]
  simp only
  rw [ite_eq_left (by omega), ite_eq_right (lt_irrefl _), Equiv.swap_apply_left]

/-- **One colour at one edge**: nothing (matched), one move, or the lookahead pair. -/
theorem stepC_cases (e : ℕ) (O : List GOp) {c : ℕ} (hc : c ∈ Bx e ∩ Bx (e + 1)) :
    (Matched (βx := βx) O e c ∧ stepC Ax Bx βx e O c = O) ∨
    (¬ Matched (βx := βx) O e c ∧ ¬ (Look Ax Bx e c ∧ ¬ Matched (βx := βx) O (e + 1) c) ∧
      ∃ o, OnColour (Bx := Bx) (βx := βx) O e c o ∧ stepC Ax Bx βx e O c = O ++ [o]) ∨
    (¬ Matched (βx := βx) O e c ∧ Look Ax Bx e c ∧ ¬ Matched (βx := βx) O (e + 1) c ∧
      ∃ o₂ o₁, OnColour (Bx := Bx) (βx := βx) O (e + 1) c o₂ ∧
        OnColour (Bx := Bx) (βx := βx) (O ++ [o₂]) e c o₁ ∧
        stepC Ax Bx βx e O c = O ++ [o₂] ++ [o₁]) := by
  rw [mem_inter] at hc
  by_cases hm : Matched (βx := βx) O e c
  · left
    refine ⟨hm, ?_⟩
    unfold stepC
    rw [ite_eq_left (show curL O (e + 1) (βx (e + 1) c) = curL O e (βx e c) from hm)]
  · by_cases hl : Look Ax Bx e c ∧ ¬ Matched (βx := βx) O (e + 1) c
    · right; right
      refine ⟨hm, hl.1, hl.2, (e + 1, curL O (e + 2) (βx (e + 2) c), curL O (e + 1) (βx (e + 1) c)),
        (e, curL O (e + 1) (βx (e + 1) c), curL O e (βx e c)), ⟨hc.2, hl.1.1, rfl, hl.2⟩, ?_, ?_⟩
      · have h1 : curL (O ++ [((e + 1, curL O (e + 2) (βx (e + 2) c),
            curL O (e + 1) (βx (e + 1) c)) : GOp)]) (e + 1) (βx (e + 1) c) =
              curL O (e + 1) (βx (e + 1) c) := by
          rw [curL_snoc]; simp
        have h0 : curL (O ++ [((e + 1, curL O (e + 2) (βx (e + 2) c),
            curL O (e + 1) (βx (e + 1) c)) : GOp)]) e (βx e c) = curL O e (βx e c) := by
          rw [curL_snoc]; simp
        refine ⟨hc.1, hc.2, by rw [h1, h0], ?_⟩
        unfold Matched; rw [h1, h0]; exact hm
      · unfold stepC
        rw [ite_eq_right (show ¬ curL O (e + 1) (βx (e + 1) c) = curL O e (βx e c) from hm),
          ite_eq_left (show Look Ax Bx e c ∧ curL O (e + 2) (βx (e + 2) c) ≠
            curL O (e + 1) (βx (e + 1) c) from ⟨hl.1, hl.2⟩)]
        simp
    · right; left
      refine ⟨hm, hl, (e, curL O (e + 1) (βx (e + 1) c), curL O e (βx e c)),
        ⟨hc.1, hc.2, rfl, hm⟩, ?_⟩
      unfold stepC
      rw [ite_eq_right (show ¬ curL O (e + 1) (βx (e + 1) c) = curL O e (βx e c) from hm),
        ite_eq_right (show ¬ (Look Ax Bx e c ∧ curL O (e + 2) (βx (e + 2) c) ≠
          curL O (e + 1) (βx (e + 1) c)) from hl)]

end Lookahead

end GridGen.Gauge
