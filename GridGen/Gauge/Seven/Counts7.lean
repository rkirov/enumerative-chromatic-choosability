/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Seven.Chordless

/-!
# Counting chordless crossing paths

A chordless path has no *U-turn*: if three consecutive steps are `d₁, d₂, d₃` with `d₃` the
reverse of `d₁`, then cells `i` and `i + 3` are adjacent (`noU_dirsOf`). So the shape of a
chordless crossing path is a `WOK` walk without U-turns (`WOK3`). These are counted by `cnt3`,
whose state is the position and the last two steps.

The chordless crossing paths for the cut below row `w` split four ways:
* **H-absorbed**: head at row `w + 1`; at most `A7 L` with `L` cells (`card_chordless_HA`);
* **H-residual**: head at row `≥ w + 2`; at most `R7 L` (`card_chordless_HR`);
* **D-absorbed**: last cell at row `w`; at most `A7 L` (`card_chordless_DA`);
* **D-residual**: last cell at row `≤ w - 1`; at most `R7 L` (`card_chordless_DR`).

Here `A7 L` counts the U-turn-free shapes from start offset `1` and `R7 L` those from start
offsets `2, …, L - 1`. A D-absorbed path is determined by its shape and `w`, and a D-residual path
is an H-residual path for the cut below row `w - 1`.

The counts up to twenty cells come from a level-by-level grid evaluation of `cnt3` (sixteen
grids, one per pair of last steps; each grid column packed into one number with `40`-bit fields),
checked by `decide +kernel` in about five seconds (`dp7_vals`, `A7_vals`, `R7_vals`):

* `A7`: `1, 1, 1, 2, 4, 8, 18, 38, 91, 185, 451, 910, 2238, 4543, 11273, 23026, 57463, 118102,
  295618` for `L = 2, …, 20`;
* `R7`: `0, 1, 2, 4, 10, 24, 56, 134, 312, 741, 1712, 4036, 9290, 21877, 50430, 118802, 274460,
  646950, 1497708`.

Beyond twenty cells: from a state with two previous steps, two more steps branch at most seven
ways, so the counts grow by at most `√7` per cell (`A7_le_tail`, `R7_le_tail`), from the largest
entry `M7 = 208774` of the grids at seventeen steps: `tailA L = 9 · M7 · tB (L - 20)` and
`tailR L = (L - 2) · tailA L`, with `tB j = 7^⌊j/2⌋ · (3 if j odd)`. The weighted sums are
`sum_chordless_HA`, `…_HR`, `…_DA`, `…_DR`; for weights `(1/4)^L` the tails sum to at most
`81/4 · M7 / 4^20` and `1701/4 · M7 / 4^20` (`tailA_sum_le`, `tailR_sum_le`).
-/

open Finset
open scoped Classical

set_option linter.unusedSectionVars false

namespace GridGen.Gauge

theorem opp_opp (d : Fin 4) : opp (opp d) = d := by fin_cases d <;> rfl

/-! ### U-turn-free shape walks -/

/-- No U-turn: the third of three consecutive steps never reverses the first. -/
def NoU : List (Fin 4) → Prop
  | d₁ :: d₂ :: d₃ :: rest => d₃ ≠ opp d₁ ∧ NoU (d₂ :: d₃ :: rest)
  | _ => True

/-- A valid U-turn-free shape walk from `(x, y)` after the steps `pp`, `p`. -/
def WOK3 : ℤ → ℤ → Option (Fin 4) → Option (Fin 4) → List (Fin 4) → Prop
  | x, y, _, _, [] => x = 0 ∧ y ≤ 0
  | x, y, pp, p, d :: ds => p ≠ some (opp d) ∧ pp ≠ some (opp d) ∧ 0 ≤ x + dx d ∧
      WOK3 (x + dx d) (y + dy d) p (some d) ds

theorem wok3_of_wok : ∀ (ds : List (Fin 4)) (x y : ℤ) (pp p : Option (Fin 4)),
    WOK x y p ds → NoU (pp.toList ++ p.toList ++ ds) → (pp.isSome → p.isSome) →
      WOK3 x y pp p ds := by
  intro ds
  induction ds with
  | nil => intro x y pp p h _ _; simpa [WOK, WOK3] using h
  | cons d ds ih =>
      intro x y pp p h hu hs
      simp only [WOK] at h
      refine ⟨h.1, ?_, h.2.1, ih _ _ _ _ h.2.2 ?_ (fun _ => rfl)⟩
      · cases pp with
        | none => simp
        | some a =>
            obtain ⟨b, rfl⟩ := Option.isSome_iff_exists.mp (hs rfl)
            simp only [Option.toList_some, List.cons_append, List.nil_append, NoU] at hu
            intro e
            apply hu.1
            rw [Option.some.injEq] at e
            rw [e, opp_opp]
      · cases pp with
        | none => simpa using hu
        | some a =>
            obtain ⟨b, rfl⟩ := Option.isSome_iff_exists.mp (hs rfl)
            simp only [Option.toList_some, List.cons_append, List.nil_append, NoU] at hu
            simpa using hu.2

/-- The U-turn-free enumerator. -/
def enum3 : ℕ → ℤ → ℤ → Option (Fin 4) → Option (Fin 4) → List (List (Fin 4))
  | 0, x, y, _, _ => if x = 0 ∧ y ≤ 0 then [[]] else []
  | n + 1, x, y, pp, p => ([0, 1, 2, 3] : List (Fin 4)).flatMap fun d =>
      if p ≠ some (opp d) ∧ pp ≠ some (opp d) ∧ 0 ≤ x + dx d then
        (enum3 n (x + dx d) (y + dy d) p (some d)).map (d :: ·)
      else []

theorem mem_enum3 : ∀ (ds : List (Fin 4)) (x y : ℤ) (pp p : Option (Fin 4)),
    WOK3 x y pp p ds → ds ∈ enum3 ds.length x y pp p := by
  intro ds
  induction ds with
  | nil => intro x y _ _ h; simp only [WOK3] at h; simp [enum3, h.1, h.2]
  | cons d ds ih =>
      intro x y pp p h
      simp only [WOK3] at h
      simp only [List.length_cons, enum3]
      rw [List.mem_flatMap]
      refine ⟨d, by fin_cases d <;> simp, ?_⟩
      rw [ite_eq_left ⟨h.1, h.2.1, h.2.2.1⟩]
      exact List.mem_map.mpr ⟨ds, ih _ _ _ _ h.2.2.2, rfl⟩

/-- One step of the count: the sum over the allowed next steps. -/
def expand3 (f : ℤ → ℤ → Option (Fin 4) → Option (Fin 4) → ℕ) (x y : ℤ) (pp p : Option (Fin 4)) :
    ℕ :=
  ([0, 1, 2, 3] : List (Fin 4)).foldr (fun d acc =>
    (if p ≠ some (opp d) ∧ pp ≠ some (opp d) ∧ 0 ≤ x + dx d then f (x + dx d) (y + dy d) p (some d)
      else 0) + acc) 0

/-- The number of U-turn-free shape walks with `n` steps (`enum3`, counted). -/
def cnt3 : ℕ → ℤ → ℤ → Option (Fin 4) → Option (Fin 4) → ℕ
  | 0, x, y, _, _ => if x = 0 ∧ y ≤ 0 then 1 else 0
  | n + 1, x, y, pp, p => expand3 (cnt3 n) x y pp p

theorem cnt3_zero (x y : ℤ) (pp p : Option (Fin 4)) :
    cnt3 0 x y pp p = if x = 0 ∧ y ≤ 0 then 1 else 0 := rfl

theorem cnt3_succ (n : ℕ) (x y : ℤ) (pp p : Option (Fin 4)) :
    cnt3 (n + 1) x y pp p = expand3 (cnt3 n) x y pp p := rfl

theorem length_enum3 : ∀ (n : ℕ) (x y : ℤ) (pp p : Option (Fin 4)),
    (enum3 n x y pp p).length = cnt3 n x y pp p := by
  intro n
  induction n with
  | zero => intro x y pp p; simp only [enum3, cnt3]; split_ifs <;> rfl
  | succ n ih =>
      intro x y pp p
      have key : ∀ d : Fin 4, (if p ≠ some (opp d) ∧ pp ≠ some (opp d) ∧ 0 ≤ x + dx d then
          (enum3 n (x + dx d) (y + dy d) p (some d)).map (d :: ·) else []).length =
          if p ≠ some (opp d) ∧ pp ≠ some (opp d) ∧ 0 ≤ x + dx d then
            cnt3 n (x + dx d) (y + dy d) p (some d) else 0 := by
        intro d; split_ifs <;> simp [ih]
      simp only [enum3, cnt3_succ, expand3, List.flatMap_cons, List.flatMap_nil, List.length_append,
        List.foldr_cons, List.foldr_nil, List.append_nil, key, add_zero]

/-- **Congruence of one step.** Only the values at the next states matter. -/
theorem expand3_congr (f g : ℤ → ℤ → Option (Fin 4) → Option (Fin 4) → ℕ) (x y : ℤ)
    (pp p : Option (Fin 4)) (h : ∀ x' y' d, 0 ≤ x' → f x' y' p (some d) = g x' y' p (some d)) :
    expand3 f x y pp p = expand3 g x y pp p := by
  have key : ∀ d : Fin 4, (if p ≠ some (opp d) ∧ pp ≠ some (opp d) ∧ 0 ≤ x + dx d then
      f (x + dx d) (y + dy d) p (some d) else 0) =
      if p ≠ some (opp d) ∧ pp ≠ some (opp d) ∧ 0 ≤ x + dx d then
        g (x + dx d) (y + dy d) p (some d) else 0 := by
    intro d; split_ifs with hc
    · exact h _ _ _ hc.2.2
    · rfl
  simp only [expand3, List.foldr_cons, List.foldr_nil, key]

/-- **A bound for one step.** -/
theorem expand3_le (f : ℤ → ℤ → Option (Fin 4) → Option (Fin 4) → ℕ) (x y : ℤ)
    (pp p : Option (Fin 4)) (B : Fin 4 → ℕ)
    (h : ∀ x' y' d, 0 ≤ x' → f x' y' p (some d) ≤ B d) :
    expand3 f x y pp p ≤ ([0, 1, 2, 3] : List (Fin 4)).foldr (fun d acc =>
      (if p ≠ some (opp d) ∧ pp ≠ some (opp d) ∧ 0 ≤ x + dx d then B d else 0) + acc) 0 := by
  have key : ∀ d : Fin 4, (if p ≠ some (opp d) ∧ pp ≠ some (opp d) ∧ 0 ≤ x + dx d then
      f (x + dx d) (y + dy d) p (some d) else 0) ≤
      if p ≠ some (opp d) ∧ pp ≠ some (opp d) ∧ 0 ≤ x + dx d then B d else 0 := by
    intro d; split_ifs with hc
    · exact h _ _ _ hc.2.2
    · exact le_rfl
  simp only [expand3, List.foldr_cons, List.foldr_nil, add_zero]
  exact add_le_add (key 0) (add_le_add (key 1) (add_le_add (key 2) (key 3)))

/-- Walks too short to return count zero. -/
theorem cnt3_eq_zero : ∀ (n : ℕ) (x y : ℤ) (pp p : Option (Fin 4)),
    (n : ℤ) < x + max y 0 → cnt3 n x y pp p = 0
  | 0, x, y, pp, p, h => by
      rw [cnt3_zero, ite_eq_right_iff]
      rintro ⟨rfl, hy⟩
      have : max y 0 = 0 := max_eq_right hy
      omega
  | n + 1, x, y, pp, p, h => by
      rw [cnt3_succ]
      have hz : ∀ d : Fin 4, cnt3 n (x + dx d) (y + dy d) p (some d) = 0 := by
        intro d
        refine cnt3_eq_zero n _ _ _ _ ?_
        fin_cases d <;> simp [dx, dy] <;> push_cast at h <;> omega
      simp only [expand3, List.foldr_cons, List.foldr_nil, hz, ite_self, add_zero]

/-- **Below the reach of the walk the counts do not depend on `y`.** -/
theorem cnt3_clamp : ∀ (n : ℕ) (x y y' : ℤ) (pp p : Option (Fin 4)),
    y ≤ -(n : ℤ) → y' ≤ -(n : ℤ) → cnt3 n x y pp p = cnt3 n x y' pp p
  | 0, x, y, y', pp, p, h, h' => by
      rw [cnt3_zero, cnt3_zero]
      have h1 : y ≤ 0 := by omega
      have h2 : y' ≤ 0 := by omega
      simp [h1, h2]
  | n + 1, x, y, y', pp, p, h, h' => by
      rw [cnt3_succ, cnt3_succ]
      have hc : ∀ d : Fin 4, cnt3 n (x + dx d) (y + dy d) p (some d) =
          cnt3 n (x + dx d) (y' + dy d) p (some d) := by
        intro d
        refine cnt3_clamp n _ _ _ _ _ ?_ ?_ <;> fin_cases d <;> simp [dy] <;> push_cast at h h' <;>
          omega
      simp only [expand3, List.foldr_cons, List.foldr_nil, hc]

/-! ### Chordless paths have no U-turn -/

variable {c m : ℕ}

theorem chordless_tail {a : Cell c m} {l : List (Cell c m)} (h : Chordless (a :: l)) :
    Chordless l := by
  intro i j hi hj hij
  have := h (i + 1) (j + 1) (by simp; omega) (by simp; omega) (by omega)
  simpa using this

theorem adj_of_move {a e : Cell c m} {d : Fin 4} (h1 : (e.1.val : ℤ) = a.1.val + dx d)
    (h2 : (e.2.val : ℤ) = a.2.val + dy d) : slabAdj a e := by
  unfold slabAdj
  simp only [Fin.ext_iff]
  fin_cases d <;> simp only [dx, dy] at h1 h2 <;> omega

/-- **The shape of a chordless path has no U-turn.** -/
theorem noU_dirsOf : ∀ l : List (Cell c m), l.IsChain slabAdj → Chordless l → NoU (dirsOf l)
  | [], _, _ => trivial
  | [_], _, _ => trivial
  | [_, _], _, _ => trivial
  | [_, _, _], _, _ => trivial
  | a :: b :: c' :: e :: rest, hch, hcl => by
      have hch1 := List.isChain_cons_cons.mp hch
      have hch2 := List.isChain_cons_cons.mp hch1.2
      have hch3 := List.isChain_cons_cons.mp hch2.2
      show NoU (dirOf a b :: dirOf b c' :: dirOf c' e :: dirsOf (e :: rest))
      refine ⟨fun heq => ?_, noU_dirsOf (b :: c' :: e :: rest) hch1.2 (chordless_tail hcl)⟩
      have m1 := move hch1.1
      have m2 := move hch2.1
      have m3 := move hch3.1
      rw [heq] at m3
      apply hcl 0 3 (by simp) (by simp) (by omega)
      simp only [List.getElem_cons_zero, List.getElem_cons_succ]
      generalize dirOf a b = d₁ at m1 m3
      generalize dirOf b c' = d₂ at m2
      apply adj_of_move (d := d₂) <;> fin_cases d₁ <;> simp only [dx, dy, opp] at m1 m3 <;> omega

/-! ### From chordless crossing paths to shapes -/

/-- The row of the head. -/
def headRow (l : List (Cell c m)) : ℕ := (l.head?.map fun z => z.2.val).getD 0

/-- The row of the last cell. -/
def lastRow (l : List (Cell c m)) : ℕ := (l.getLast?.map fun z => z.2.val).getD 0

/-- The shape of a chordless crossing path, in coordinates relative to any row `u` at or above
its last cell. -/
theorem shape_of_cross {hc : 1 ≤ c} {w : ℕ} {l : List (Cell c m)} (hl : CrossPath hc w l)
    (hcl : Chordless l) {v₁ : Fin m} (h1 : l.head? = some (fut0 hc, v₁)) (u : ℕ)
    (hu : lastRow l ≤ u) :
    WOK 0 ((v₁.val : ℤ) - u) none (dirsOf l) ∧ WOK3 0 ((v₁.val : ℤ) - u) none none (dirsOf l) := by
  obtain ⟨hnd, hch, hfut, _, ⟨v₂, _, h2⟩⟩ := hl
  have hwok := wok_dirsOf u l hch hnd hfut (fut0 hc, v₁) (by rw [h1]; rfl)
    (fun z hz => by
      rw [h2] at hz; simp at hz; subst hz
      refine ⟨rfl, ?_⟩
      simpa [lastRow, h2] using hu) none (by simp)
  simp only [fut0, Option.map_none] at hwok
  rw [show ((2 : ℕ) : ℤ) - 2 = 0 by norm_num] at hwok
  exact ⟨hwok, wok3_of_wok _ _ _ none none hwok (by simpa using noU_dirsOf l hch hcl)
    (by simp)⟩

/-- The row displacement of a chain is the sum of the `y`-steps of its shape. -/
theorem sum_dy_dirsOf : ∀ l : List (Cell c m), l.IsChain slabAdj → ∀ a ∈ l.head?,
    ∀ z ∈ l.getLast?, (z.2.val : ℤ) = a.2.val + ((dirsOf l).map dy).sum
  | [], _, _, ha, _, _ => by simp at ha
  | [a'], _, a, ha, z, hz => by
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at ha
      simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hz
      subst ha hz; simp [dirsOf]
  | a' :: b :: rest, hch, a, ha, z, hz => by
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at ha
      subst ha
      have hch' := List.isChain_cons_cons.mp hch
      have ih := sum_dy_dirsOf (b :: rest) hch'.2 b (by simp) z
        (by simpa [List.getLast?_cons_cons] using hz)
      have hm := move hch'.1
      simp only [dirsOf, List.map_cons, List.sum_cons]
      omega

/-- The shapes of the crossing paths with head offset in `P` and `L` cells. -/
theorem card_chordless_head_le (hc : 1 ≤ c) (w L : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (((crossPaths (m := m) hc w).filter fun l => Chordless l ∧ P (headRow l - w)).filter
      fun l => l.length = L).card ≤ ∑ d ∈ (range L).filter P, cnt3 (L - 1) 0 d none none := by
  set S : Finset (ℕ × List (Fin 4)) := ((range L).filter P).biUnion fun d =>
    (enum3 (L - 1) 0 (d : ℤ) none none).toFinset.image fun ds => (d, ds)
  have hS : S.card ≤ ∑ d ∈ (range L).filter P, cnt3 (L - 1) 0 d none none := by
    calc S.card ≤ ∑ d ∈ (range L).filter P,
          ((enum3 (L - 1) 0 (d : ℤ) none none).toFinset.image fun ds => (d, ds)).card :=
          card_biUnion_le
      _ ≤ _ := sum_le_sum fun d _ => by
          rw [← length_enum3]; exact le_trans card_image_le (List.toFinset_card_le _)
  refine le_trans (card_le_card_of_injOn (fun l => (headRow l - w, dirsOf l)) ?_ ?_) hS
  · intro l hl
    rw [mem_coe, mem_filter, mem_filter] at hl
    obtain ⟨⟨hl, hcl, hP⟩, hlen⟩ := hl
    have hcp : CrossPath hc w l := (mem_filter.mp hl).2
    obtain ⟨v₁, hw₁, h1⟩ := hcp.2.2.2.1
    obtain ⟨v₂, hw₂, h2⟩ := hcp.2.2.2.2
    have hhr : headRow l = v₁.val := by simp [headRow, h1]
    obtain ⟨hwok, hwok3⟩ := shape_of_cross hcp hcl h1 w (by simp [lastRow, h2]; exact hw₂)
    have e : ((v₁.val : ℤ) - w) = ((v₁.val - w : ℕ) : ℤ) := by push_cast [hw₁.le]; ring
    rw [e] at hwok hwok3
    have hr := reach_of_WOK _ _ _ _ hwok
    rw [length_dirsOf, hlen] at hr
    have hmem := mem_enum3 _ _ _ _ _ hwok3
    rw [length_dirsOf, hlen] at hmem
    rw [mem_coe, mem_biUnion]
    refine ⟨headRow l - w, mem_filter.mpr ⟨mem_range.mpr ?_, hP⟩,
      mem_image.mpr ⟨dirsOf l, List.mem_toFinset.mpr ?_, rfl⟩⟩
    · rw [hhr]; simp only [max_def] at hr; split_ifs at hr <;> omega
    · rw [hhr]; exact hmem
  · intro l hl l' hl' he
    rw [mem_coe, mem_filter, mem_filter] at hl hl'
    have hcp := (mem_filter.mp hl.1.1).2
    have hcp' := (mem_filter.mp hl'.1.1).2
    obtain ⟨_, hch, _, ⟨v₁, hw₁, h1⟩, _⟩ := hcp
    obtain ⟨_, hch', _, ⟨v₁', hw₁', h1'⟩, _⟩ := hcp'
    simp only [Prod.mk.injEq, headRow, h1, h1', Option.map_some, Option.getD_some] at he
    have hv : v₁ = v₁' := Fin.ext (by omega)
    subst hv
    exact eq_of_dirsOf l l' hch hch' (by rw [h1, h1']) he.2

/-! ### The four types -/

/-- The H-absorbed count: U-turn-free shapes with `L` cells from start offset `1`. -/
def A7 (L : ℕ) : ℕ := cnt3 (L - 1) 0 1 none none

/-- The residual count: U-turn-free shapes with `L` cells from start offsets `2, …, L - 1`. -/
def R7 (L : ℕ) : ℕ := ∑ d ∈ Ico 2 L, cnt3 (L - 1) 0 (d : ℤ) none none

/-- **H-absorbed: head at row `w + 1`.** -/
theorem card_chordless_HA (hc : 1 ≤ c) (w L : ℕ) :
    (((crossPaths (m := m) hc w).filter fun l => Chordless l ∧ headRow l = w + 1).filter
      fun l => l.length = L).card ≤ A7 L := by
  have e : ((crossPaths (m := m) hc w).filter fun l => Chordless l ∧ headRow l = w + 1) =
      (crossPaths (m := m) hc w).filter fun l => Chordless l ∧ headRow l - w = 1 := by
    refine filter_congr fun l hl => ?_
    obtain ⟨v₁, hw₁, h1⟩ := (mem_filter.mp hl).2.2.2.2.1
    have : headRow l = v₁.val := by simp [headRow, h1]
    rw [this]; constructor <;> rintro ⟨h, h'⟩ <;> exact ⟨h, by omega⟩
  rw [e]
  refine le_trans (card_chordless_head_le hc w L (· = 1)) ?_
  unfold A7
  by_cases hL : 1 < L
  · rw [show (range L).filter (· = 1) = {1} by
      ext d; simp only [mem_filter, mem_range, mem_singleton]; omega, sum_singleton]
    simp
  · rw [show (range L).filter (· = 1) = ∅ by
      ext d; simp only [mem_filter, mem_range]; simp; omega, sum_empty]
    exact Nat.zero_le _

/-- **H-residual: head at row `≥ w + 2`.** -/
theorem card_chordless_HR (hc : 1 ≤ c) (w L : ℕ) :
    (((crossPaths (m := m) hc w).filter fun l => Chordless l ∧ w + 2 ≤ headRow l).filter
      fun l => l.length = L).card ≤ R7 L := by
  have e : ((crossPaths (m := m) hc w).filter fun l => Chordless l ∧ w + 2 ≤ headRow l) =
      (crossPaths (m := m) hc w).filter fun l => Chordless l ∧ 2 ≤ headRow l - w := by
    refine filter_congr fun l _ => ?_
    constructor <;> rintro ⟨h, h'⟩ <;> exact ⟨h, by omega⟩
  rw [e]
  refine le_trans (card_chordless_head_le hc w L (2 ≤ ·)) (le_of_eq ?_)
  unfold R7
  congr 1
  ext d; simp only [mem_filter, mem_range, mem_Ico]; omega

/-- **D-absorbed: last cell at row `w`.** The shape determines the head. -/
theorem card_chordless_DA (hc : 1 ≤ c) (w L : ℕ) :
    (((crossPaths (m := m) hc w).filter fun l => Chordless l ∧ lastRow l = w).filter
      fun l => l.length = L).card ≤ A7 L := by
  unfold A7
  rw [← length_enum3]
  refine le_trans (card_le_card_of_injOn dirsOf (t := (enum3 (L - 1) 0 1 none none).toFinset)
    ?_ ?_) (List.toFinset_card_le _)
  · intro l hl
    rw [mem_coe, mem_filter, mem_filter] at hl
    obtain ⟨⟨hl, hcl, hlr⟩, hlen⟩ := hl
    have hcp : CrossPath hc w l := (mem_filter.mp hl).2
    obtain ⟨v₁, hw₁, h1⟩ := hcp.2.2.2.1
    obtain ⟨_, hwok3⟩ := shape_of_cross hcp hcl h1 (v₁.val - 1) (by omega)
    rw [show ((v₁.val : ℤ) - ((v₁.val - 1 : ℕ) : ℤ)) = 1 by omega] at hwok3
    have hmem := mem_enum3 _ _ _ _ _ hwok3
    rw [length_dirsOf, hlen] at hmem
    exact mem_coe.mpr (List.mem_toFinset.mpr hmem)
  · intro l hl l' hl' he
    rw [mem_coe, mem_filter, mem_filter] at hl hl'
    have hcp := (mem_filter.mp hl.1.1).2
    have hcp' := (mem_filter.mp hl'.1.1).2
    obtain ⟨_, hch, _, ⟨v₁, hw₁, h1⟩, ⟨v₂, hw₂, h2⟩⟩ := hcp
    obtain ⟨_, hch', _, ⟨v₁', hw₁', h1'⟩, ⟨v₂', hw₂', h2'⟩⟩ := hcp'
    have hr := hl.1.2.2
    have hr' := hl'.1.2.2
    simp only [lastRow, h2, h2', Option.map_some, Option.getD_some] at hr hr'
    have s1 := sum_dy_dirsOf l hch _ (by rw [h1]; rfl) _ (by rw [h2]; rfl)
    have s2 := sum_dy_dirsOf l' hch' _ (by rw [h1']; rfl) _ (by rw [h2']; rfl)
    simp only at he s1 s2
    rw [he] at s1
    have hv : v₁ = v₁' := Fin.ext (by omega)
    subst hv
    exact eq_of_dirsOf l l' hch hch' (by rw [h1, h1']) he

/-- **D-residual: last cell at row `≤ w - 1`.** It is H-residual for the cut below row `w - 1`. -/
theorem card_chordless_DR (hc : 1 ≤ c) (w L : ℕ) :
    (((crossPaths (m := m) hc w).filter fun l => Chordless l ∧ lastRow l + 1 ≤ w).filter
      fun l => l.length = L).card ≤ R7 L := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · rw [show ((crossPaths (m := m) hc 0).filter fun l => Chordless l ∧ lastRow l + 1 ≤ 0) = ∅ by
      ext l; simp, filter_empty, card_empty]
    exact Nat.zero_le _
  · obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
    refine le_trans (card_le_card ?_) (card_chordless_HR hc w' L)
    intro l hl
    simp only [mem_filter] at hl ⊢
    obtain ⟨⟨hl, hcl, hlr⟩, hlen⟩ := hl
    obtain ⟨hnd, hch, hfut, ⟨v₁, hw₁, h1⟩, ⟨v₂, hw₂, h2⟩⟩ := (mem_filter.mp hl).2
    have e2 : lastRow l = v₂.val := by simp [lastRow, h2]
    have e1 : headRow l = v₁.val := by simp [headRow, h1]
    have hm : l ∈ crossPaths (m := m) hc w' := by
      unfold crossPaths
      exact mem_filter.mpr ⟨(mem_filter.mp hl).1, hnd, hch, hfut, ⟨v₁, by omega, h1⟩,
        ⟨v₂, by omega, h2⟩⟩
    exact ⟨⟨hm, hcl, by omega⟩, hlen⟩

/-! ### Weighted sums -/

/-- Summing a per-length bound. -/
theorem sum_len_le {T : Finset (List (Cell c m))} (hT : ∀ l ∈ T, l.Nodup) (N : ℕ → ℕ)
    (hN : ∀ L, (T.filter fun l => l.length = L).card ≤ N L) (g : ℕ → ℚ) (hg : ∀ L, 0 ≤ g L) :
    ∑ l ∈ T, g l.length ≤ ∑ L ∈ range (Fintype.card (Cell c m) + 1), (N L : ℚ) * g L := by
  rw [← sum_fiberwise_of_maps_to (g := List.length) (t := range (Fintype.card (Cell c m) + 1))]
  · refine sum_le_sum fun L _ => ?_
    rw [sum_congr rfl fun l hl => by rw [(mem_filter.mp hl).2], sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hN L) (hg L)
  · intro l hl
    exact mem_range.mpr (Nat.lt_succ_of_le (hT l hl).length_le_card)

theorem nodup_of_chord {hc : 1 ≤ c} {w : ℕ} {Q : List (Cell c m) → Prop} [DecidablePred Q] :
    ∀ l ∈ (crossPaths (m := m) hc w).filter Q, l.Nodup :=
  fun _ hl => ((mem_filter.mp (mem_filter.mp hl).1).2).1

/-- The number of allowed next steps after `pp`, `p` (ignoring `x ≥ 0`). -/
def cnt1 (pp p : Option (Fin 4)) : ℕ :=
  ([0, 1, 2, 3] : List (Fin 4)).foldr (fun d acc =>
    (if p ≠ some (opp d) ∧ pp ≠ some (opp d) then 1 else 0) + acc) 0

theorem expand3_le_mul (f : ℤ → ℤ → Option (Fin 4) → Option (Fin 4) → ℕ) (x y : ℤ)
    (pp p : Option (Fin 4)) (M : ℕ) (h : ∀ x' y' d, 0 ≤ x' → f x' y' p (some d) ≤ M) :
    expand3 f x y pp p ≤ cnt1 pp p * M := by
  refine le_trans (expand3_le f x y pp p (fun _ => M) h) ?_
  have key : ∀ d : Fin 4, (if p ≠ some (opp d) ∧ pp ≠ some (opp d) ∧ 0 ≤ x + dx d then M else 0) ≤
      (if p ≠ some (opp d) ∧ pp ≠ some (opp d) then 1 else 0) * M := by
    intro d
    by_cases hc : p ≠ some (opp d) ∧ pp ≠ some (opp d)
    · rw [ite_eq_left hc, one_mul]; split_ifs <;> simp
    · rw [ite_eq_right hc, zero_mul, ite_eq_right fun h => hc ⟨h.1, h.2.1⟩]
  simp only [cnt1, List.foldr_cons, List.foldr_nil, add_zero, add_mul]
  exact add_le_add (key 0) (add_le_add (key 1) (add_le_add (key 2) (key 3)))

theorem cnt1_le_four (pp p : Option (Fin 4)) : cnt1 pp p ≤ 4 := by
  unfold cnt1
  simp only [List.foldr_cons, List.foldr_nil]
  split_ifs <;> omega

/-- The counts are at most `4^n`. -/
theorem cnt3_le_pow : ∀ (n : ℕ) (x y : ℤ) (pp p : Option (Fin 4)), cnt3 n x y pp p ≤ 4 ^ n
  | 0, x, y, pp, p => by rw [cnt3_zero]; split_ifs <;> simp
  | n + 1, x, y, pp, p => by
      rw [cnt3_succ, pow_succ, mul_comm]
      exact le_trans (expand3_le_mul _ _ _ _ _ _ fun x' y' d _ => cnt3_le_pow n x' y' p (some d))
        (Nat.mul_le_mul_right _ (cnt1_le_four pp p))

/-! ### The grid evaluation

The counts `cnt3 n x y (some a) (some b)` for `x ∈ [0, N]`, `y ∈ [-N, N]` are evaluated level by
level, sixteen grids per level (one per state `(a, b)`). A grid is a list of columns `x`, and a
column is one natural number holding the entries `y` in `40`-bit fields. The entries stay below
`4^17`, so adding columns never carries between fields (`fld_add`). -/

/-- The field base. -/
def Wd : ℕ := 2 ^ 40

theorem Wd_pos : 0 < Wd := by unfold Wd; positivity

/-- The field `j` of a column. -/
def fld (r j : ℕ) : ℕ := r / Wd ^ j % Wd

theorem fld_zero (r : ℕ) : fld r 0 = r % Wd := by simp [fld]

theorem fld_succ (r j : ℕ) : fld r (j + 1) = fld (r / Wd) j := by
  unfold fld; rw [Nat.div_div_eq_div_mul, pow_succ']

theorem fld_zero_left (j : ℕ) : fld 0 j = 0 := by simp [fld]

/-- **Fields add without carries.** -/
theorem fld_add : ∀ (j r s : ℕ), (∀ i ≤ j, fld r i + fld s i < Wd) →
    fld (r + s) j = fld r j + fld s j
  | 0, r, s, h => by
      have := h 0 le_rfl
      rw [fld_zero, fld_zero] at this
      rw [fld_zero, fld_zero, fld_zero, Nat.add_mod, Nat.mod_eq_of_lt this]
  | j + 1, r, s, h => by
      have h0 := h 0 (Nat.zero_le _)
      rw [fld_zero, fld_zero] at h0
      rw [fld_succ, fld_succ, fld_succ, Nat.add_div Wd_pos, ite_eq_right (by omega), add_zero]
      exact fld_add j _ _ fun i hi => by rw [← fld_succ, ← fld_succ]; exact h (i + 1) (by omega)

/-- Masking to `K` fields. -/
theorem fld_mod (t K j : ℕ) : fld (t % Wd ^ K) j = if j < K then fld t j else 0 := by
  unfold fld
  split_ifs with h
  · obtain ⟨k, rfl⟩ : ∃ k, K = j + (k + 1) := ⟨K - j - 1, by omega⟩
    rw [pow_add, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (dvd_pow_self _ (by omega))]
  · rw [Nat.div_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (pow_pos Wd_pos _))
      (Nat.pow_le_pow_right Wd_pos (by omega)))]
    simp

/-- Read field `j + 1` (zero at the top field `J - 1`). -/
def cYp (J r : ℕ) : ℕ := r / Wd % Wd ^ (J - 1)

theorem fld_cYp (J r j : ℕ) : fld (cYp J r) j = if j + 1 < J then fld r (j + 1) else 0 := by
  unfold cYp
  rw [fld_mod, ← fld_succ]
  split_ifs <;> first | rfl | omega

/-- Read field `j - 1`, repeating field `0`. -/
def cYm (J r : ℕ) : ℕ := (r * Wd + r % Wd) % Wd ^ J

theorem fld_cYm (J r j : ℕ) (hj : j < J) : fld (cYm J r) j = fld r (j - 1) := by
  unfold cYm
  rw [fld_mod, ite_eq_left hj]
  rcases j with _ | j
  · rw [fld_zero, fld_zero]; simp [Nat.add_mod, Nat.mul_mod_left]
  · rw [fld_succ, show (r * Wd + r % Wd) / Wd = r by
      rw [add_comm, Nat.add_mul_div_right _ _ Wd_pos, Nat.div_eq_of_lt (Nat.mod_lt _ Wd_pos),
        zero_add]]
    rfl

/-- `k` fields equal to one. -/
def ones : ℕ → ℕ
  | 0 => 0
  | k + 1 => 1 + Wd * ones k

theorem fld_ones : ∀ k j, fld (ones k) j = if j < k then 1 else 0
  | 0, j => by simp [ones, fld_zero_left]
  | k + 1, 0 => by
      rw [ones, fld_zero, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by unfold Wd; norm_num)]
      simp
  | k + 1, j + 1 => by
      rw [ones, fld_succ, show (1 + Wd * ones k) / Wd = ones k by
        rw [Nat.add_mul_div_left _ _ Wd_pos, Nat.div_eq_of_lt (by unfold Wd; norm_num), zero_add],
        fld_ones k j]
      simp

/-- A grid: one column per `x`. -/
abbrev PGrid := List ℕ

/-- The entry `(x, j)` of a grid (zero off the grid). -/
def pget (g : PGrid) (x j : ℕ) : ℕ := fld (g.getD x 0) j

theorem pget_of_ge {g : PGrid} {x : ℕ} (h : g.length ≤ x) (j : ℕ) : pget g x j = 0 := by
  unfold pget; rw [List.getD_eq_default _ _ h, fld_zero_left]

def padd (g h : PGrid) : PGrid := List.zipWith (· + ·) g h

def pXp (g : PGrid) : PGrid := g.tail ++ [0]

def pXm (g : PGrid) : PGrid := 0 :: g.dropLast

def pYp (J : ℕ) (g : PGrid) : PGrid := g.map (cYp J)

def pYm (J : ℕ) (g : PGrid) : PGrid := g.map (cYm J)

theorem getD_padd {g h : PGrid} (hl : g.length = h.length) (x : ℕ) :
    (padd g h).getD x 0 = g.getD x 0 + h.getD x 0 := by
  unfold padd
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_zipWith]
  rcases Nat.lt_or_ge x g.length with hx | hx
  · rw [List.getElem?_eq_getElem hx, List.getElem?_eq_getElem (by omega)]; rfl
  · rw [List.getElem?_eq_none hx, List.getElem?_eq_none (by omega)]; rfl

theorem length_padd {g h : PGrid} (hl : g.length = h.length) : (padd g h).length = g.length := by
  simp [padd, hl]

theorem getD_pXp {g : PGrid} (hg : 1 ≤ g.length) (x : ℕ) : (pXp g).getD x 0 = g.getD (x + 1) 0 := by
  unfold pXp
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rcases Nat.lt_or_ge x (g.length - 1) with hx | hx
  · rw [List.getElem?_append_left (by rw [List.length_tail]; exact hx), List.getElem?_tail]
  · rw [List.getElem?_append_right (by rw [List.length_tail]; omega),
      List.getElem?_eq_none (show g.length ≤ x + 1 by omega)]
    rcases Nat.lt_or_ge x g.length with hx' | hx'
    · rw [show x - g.tail.length = 0 by rw [List.length_tail]; omega]; rfl
    · rw [List.getElem?_eq_none (by simp only [List.length_singleton, List.length_tail]; omega)]

theorem length_pXp {g : PGrid} (hg : 1 ≤ g.length) : (pXp g).length = g.length := by
  simp [pXp]; omega

theorem getD_pXm {g : PGrid} {x : ℕ} (hx : x < g.length) :
    (pXm g).getD x 0 = if x = 0 then 0 else g.getD (x - 1) 0 := by
  unfold pXm
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · subst h; rfl
  · obtain ⟨x', rfl⟩ : ∃ x', x = x' + 1 := ⟨x - 1, by omega⟩
    rw [List.getElem?_cons_succ, List.getElem?_dropLast, ite_eq_left (by omega),
      List.getD_eq_getElem?_getD, show x' + 1 - 1 = x' by omega]

theorem length_pXm {g : PGrid} (hg : 1 ≤ g.length) : (pXm g).length = g.length := by
  simp [pXm]; omega

theorem getD_map0 {f : ℕ → ℕ} (hf : f 0 = 0) (g : PGrid) (x : ℕ) :
    (g.map f).getD x 0 = f (g.getD x 0) := by
  have := List.getD_map (f := f) (l := g) (n := x) (d := 0)
  rw [hf] at this
  exact this

theorem cYp_zero (J : ℕ) : cYp J 0 = 0 := by simp [cYp]

theorem cYm_zero (J : ℕ) : cYm J 0 = 0 := by simp [cYm]

def L4 : List (Fin 4) := [0, 1, 2, 3]

/-- The grid of the state `(a, b)` (the previous steps `a`, then `b`). -/
def plget (G : List (List PGrid)) (a b : Fin 4) : PGrid := (G.getD a.val []).getD b.val []

def pmk4 (F : Fin 4 → Fin 4 → PGrid) : List (List PGrid) := L4.map fun a => L4.map fun b => F a b

theorem plget_pmk4 (F : Fin 4 → Fin 4 → PGrid) (a b : Fin 4) : plget (pmk4 F) a b = F a b := by
  fin_cases a <;> fin_cases b <;> rfl

/-- The four steps as grid reads: up reads `y - 1`, down `y + 1`, right `x + 1`, left `x - 1`. -/
def pshift (J : ℕ) : Fin 4 → PGrid → PGrid
  | 0 => pYm J | 1 => pYp J | 2 => pXp | 3 => pXm

theorem length_pshift {g : PGrid} (hg : 1 ≤ g.length) (J : ℕ) (d : Fin 4) :
    (pshift J d g).length = g.length := by
  fin_cases d
  · simp [pshift, pYm]
  · simp [pshift, pYp]
  · exact length_pXp hg
  · exact length_pXm hg

/-- The partial sums over the allowed next steps of the state `(a, b)`. -/
def psumL (X : ℕ) (a b : Fin 4) (S : Fin 4 → PGrid) (ds : List (Fin 4)) : PGrid :=
  ds.foldr (fun d acc => if b ≠ opp d ∧ a ≠ opp d then padd (S d) acc else acc) (List.replicate X 0)

theorem psumL_spec {X J K : ℕ} (hK : 4 * K < Wd) {S : Fin 4 → PGrid} (hS : ∀ d, (S d).length = X)
    (hSb : ∀ d x i, i < J → pget (S d) x i ≤ K) (a b : Fin 4) :
    ∀ ds : List (Fin 4), ds.length ≤ 4 →
      (psumL X a b S ds).length = X ∧ (∀ x i, i < J → pget (psumL X a b S ds) x i ≤ ds.length * K) ∧
      ∀ x j, j < J → pget (psumL X a b S ds) x j =
        ds.foldr (fun d acc => (if b ≠ opp d ∧ a ≠ opp d then pget (S d) x j else 0) + acc) 0
  | [], _ => by
      refine ⟨by simp [psumL], fun x i _ => ?_, fun x j _ => ?_⟩ <;>
        simp [psumL, pget, fld_zero_left]
  | d :: ds, hl => by
      obtain ⟨h1, h2, h3⟩ := psumL_spec hK hS hSb a b ds (by simp at hl; omega)
      have hl' : ds.length + 1 ≤ 4 := by simpa using hl
      have hadd : ∀ x i, i < J → pget (padd (S d) (psumL X a b S ds)) x i =
          pget (S d) x i + pget (psumL X a b S ds) x i := by
        intro x i hi
        unfold pget
        rw [getD_padd (by rw [hS d, h1])]
        refine fld_add i _ _ fun i' hi' => ?_
        have := hSb d x i' (by omega)
        have := h2 x i' (by omega)
        unfold pget at *
        nlinarith
      have e : psumL X a b S (d :: ds) = if b ≠ opp d ∧ a ≠ opp d then
          padd (S d) (psumL X a b S ds) else psumL X a b S ds := rfl
      rw [e]
      simp only [List.foldr_cons, List.length_cons]
      split_ifs with hc
      · refine ⟨by rw [length_padd (by rw [hS d, h1]), hS d], fun x i hi => ?_, fun x j hj => ?_⟩
        · rw [hadd x i hi]; have := hSb d x i hi; have := h2 x i hi; nlinarith
        · rw [hadd x j hj, h3 x j hj]
      · refine ⟨h1, fun x i hi => le_trans (h2 x i hi) (by nlinarith), fun x j hj => ?_⟩
        rw [h3 x j hj, zero_add]

/-- One level: each state sums the shifted grids of its allowed next states. -/
def pstep3 (X J : ℕ) (G : List (List PGrid)) : List (List PGrid) :=
  let S := pmk4 fun b d => pshift J d (plget G b d)
  pmk4 fun a b => psumL X a b (plget S b) L4

def pinit (X N : ℕ) : PGrid := (List.range X).map fun x => if x = 0 then ones (N + 1) else 0

/-- The levels: sixteen grids, `x ∈ [0, N]`, `y ∈ [-N, N]` (field `j = y + N`). -/
def plev (N : ℕ) : ℕ → List (List PGrid)
  | 0 => pmk4 fun _ _ => pinit (N + 1) N
  | n + 1 => pstep3 (N + 1) (2 * N + 1) (plev N n)

theorem pget_pinit {X N x j : ℕ} (hx : x < X) :
    pget (pinit X N) x j = if x = 0 ∧ j ≤ N then 1 else 0 := by
  unfold pget pinit
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hx]
  simp only [Option.map_some, Option.getD_some]
  split_ifs with h1 h2 h2
  · rw [fld_ones, ite_eq_left (by omega)]
  · rw [fld_ones, ite_eq_right (by omega)]
  · exact absurd h2.1 h1
  · exact fld_zero_left j

/-- **The grids are the counts.** -/
theorem plev_spec {N : ℕ} (hN : N ≤ 17) : ∀ n, n ≤ N →
    (∀ a b, (plget (plev N n) a b).length = N + 1) ∧
    ∀ (a b : Fin 4) (x j : ℕ), x < N + 1 → j < 2 * N + 1 →
      pget (plget (plev N n) a b) x j = cnt3 n x ((j : ℤ) - N) (some a) (some b)
  | 0, _ => by
      refine ⟨fun a b => by simp [plev, plget_pmk4, pinit], fun a b x j hx hj => ?_⟩
      rw [plev, plget_pmk4, pget_pinit hx, cnt3_zero]
      congr 1
      apply propext
      constructor
      · rintro ⟨rfl, h⟩; exact ⟨rfl, by omega⟩
      · rintro ⟨h1, h2⟩; exact ⟨by exact_mod_cast h1, by omega⟩
  | n + 1, hn => by
      obtain ⟨hlen, ih⟩ := plev_spec hN n (by omega)
      have hlen1 : ∀ a b, 1 ≤ (plget (plev N n) a b).length := fun a b => by rw [hlen]; omega
      -- the shifted reads
      have rd : ∀ (b d : Fin 4) (x j : ℕ), x < N + 1 → j < (2 * N + 1) →
          pget (pshift (2 * N + 1) d (plget (plev N n) b d)) x j =
            if 0 ≤ (x : ℤ) + dx d then cnt3 n (x + dx d) ((j : ℤ) - N + dy d) (some b) (some d)
            else 0 := by
        intro b d x j hx hj
        fin_cases d
        · show fld ((List.map (cYm (2 * N + 1)) (plget (plev N n) b 0)).getD x 0) j = _
          rw [getD_map0 (cYm_zero (2 * N + 1)), fld_cYm (2 * N + 1) _ j hj]
          simp only [dx, dy, add_zero]
          rw [ite_eq_left (by positivity)]
          rcases Nat.eq_zero_or_pos j with rfl | hj0
          · rw [show (0 : ℕ) - 1 = 0 by rfl]
            rw [show fld ((plget (plev N n) b 0).getD x 0) 0 = pget (plget (plev N n) b 0) x 0 from rfl,
              ih b 0 x 0 hx (by omega)]
            exact cnt3_clamp n _ _ _ _ _ (by push_cast; omega) (by push_cast; omega)
          · rw [show fld ((plget (plev N n) b 0).getD x 0) (j - 1) = pget (plget (plev N n) b 0) x (j - 1) from rfl,
              ih b 0 x (j - 1) hx (by omega)]
            congr 1; push_cast [hj0]; ring
        · show fld ((List.map (cYp (2 * N + 1)) (plget (plev N n) b 1)).getD x 0) j = _
          rw [getD_map0 (cYp_zero (2 * N + 1)), fld_cYp]
          simp only [dx, dy, add_zero]
          rw [ite_eq_left (show (0 : ℤ) ≤ (x : ℤ) by positivity)]
          split_ifs with hj1
          · rw [show fld ((plget (plev N n) b 1).getD x 0) (j + 1) = pget (plget (plev N n) b 1) x (j + 1) from rfl,
              ih b 1 x (j + 1) hx hj1]
            congr 1; push_cast; ring
          · refine (cnt3_eq_zero n _ _ _ _ ?_).symm
            have := le_max_left ((j : ℤ) - N + 1) 0
            omega
        · show fld ((pXp (plget (plev N n) b 2)).getD x 0) j = _
          rw [getD_pXp (hlen1 b 2)]
          simp only [dx, dy, add_zero]
          rw [ite_eq_left (by positivity)]
          rcases Nat.lt_or_ge (x + 1) (N + 1) with hx1 | hx1
          · rw [show fld ((plget (plev N n) b 2).getD (x + 1) 0) j = pget (plget (plev N n) b 2) (x + 1) j from rfl,
              ih b 2 (x + 1) j hx1 hj]
            push_cast; rfl
          · rw [show fld ((plget (plev N n) b 2).getD (x + 1) 0) j = pget (plget (plev N n) b 2) (x + 1) j from rfl,
              pget_of_ge (by rw [hlen]; exact hx1)]
            refine (cnt3_eq_zero n _ _ _ _ ?_).symm
            have := le_max_right ((j : ℤ) - N) 0
            omega
        · show fld ((pXm (plget (plev N n) b 3)).getD x 0) j = _
          rw [getD_pXm (by rw [hlen]; exact hx)]
          simp only [dx, dy, add_zero]
          rcases Nat.eq_zero_or_pos x with rfl | hx0
          · simp [fld_zero_left]
          · rw [ite_eq_right (by omega), ite_eq_left (by omega),
              show fld ((plget (plev N n) b 3).getD (x - 1) 0) j = pget (plget (plev N n) b 3) (x - 1) j from rfl,
              ih b 3 (x - 1) j (by omega) hj]
            congr 1; push_cast [hx0]; ring
      have hSl : ∀ b d, (pshift (2 * N + 1) d (plget (plev N n) b d)).length = N + 1 := fun b d => by
        rw [length_pshift (hlen1 b d), hlen]
      have hSb : ∀ b d x i, i < (2 * N + 1) → pget (pshift (2 * N + 1) d (plget (plev N n) b d)) x i ≤ 4 ^ n := by
        intro b d x i hi
        rcases Nat.lt_or_ge x (N + 1) with hx | hx
        · rw [rd b d x i hx hi]; split_ifs
          · exact cnt3_le_pow _ _ _ _ _
          · exact Nat.zero_le _
        · rw [pget_of_ge (by rw [hSl]; exact hx)]; exact Nat.zero_le _
      have hK : 4 * 4 ^ n < Wd := by
        unfold Wd
        calc 4 * 4 ^ n ≤ 4 * 4 ^ 17 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
          _ < 2 ^ 40 := by norm_num
      have hspec := fun b => psumL_spec (J := 2 * N + 1) hK
        (S := plget (pmk4 fun b d => pshift (2 * N + 1) d (plget (plev N n) b d)) b)
        (fun d => by rw [plget_pmk4]; exact hSl b d)
        (fun d x i hi => by rw [plget_pmk4]; exact hSb b d x i hi)
      refine ⟨fun a b => ?_, fun a b x j hx hj => ?_⟩
      · simp only [plev, pstep3, plget_pmk4]
        exact (hspec b a b L4 (by simp [L4])).1
      · simp only [plev, pstep3, plget_pmk4]
        rw [(hspec b a b L4 (by simp [L4])).2.2 x j hj, cnt3_succ]
        have key : ∀ d : Fin 4, (if b ≠ opp d ∧ a ≠ opp d then
            pget (plget (pmk4 fun b d => pshift (2 * N + 1) d (plget (plev N n) b d)) b d) x j else 0) =
            if some b ≠ some (opp d) ∧ some a ≠ some (opp d) ∧ 0 ≤ (x : ℤ) + dx d then
              cnt3 n (x + dx d) ((j : ℤ) - N + dy d) (some b) (some d) else 0 := by
          intro d
          rw [plget_pmk4, rd b d x j hx hj]
          by_cases h1 : b = opp d <;> by_cases h2 : a = opp d <;> simp [h1, h2]
        simp only [L4, expand3, List.foldr_cons, List.foldr_nil, key]

/-- A read of a grid at any position (`y` clamped below, zero outside). -/
def pread (N : ℕ) (g : PGrid) (x y : ℤ) : ℕ :=
  if x < 0 ∨ (N : ℤ) < y then 0 else pget g x.toNat (if y < -(N : ℤ) then 0 else (y + N).toNat)

theorem pread_spec {N n : ℕ} (hN : N ≤ 17) (hn : n ≤ N) (a b : Fin 4) (x y : ℤ) (hx : 0 ≤ x) :
    pread N (plget (plev N n) a b) x y = cnt3 n x y (some a) (some b) := by
  obtain ⟨hlen, hsp⟩ := plev_spec hN n hn
  unfold pread
  by_cases hy : (N : ℤ) < y
  · rw [ite_eq_left (Or.inr hy)]
    refine (cnt3_eq_zero n x y _ _ ?_).symm
    have := le_max_left y 0
    omega
  · rw [ite_eq_right (by omega)]
    obtain ⟨x', rfl⟩ : ∃ x' : ℕ, x = x' := ⟨x.toNat, (Int.toNat_of_nonneg hx).symm⟩
    rw [Int.toNat_natCast]
    by_cases hxN : x' < N + 1
    · by_cases hy2 : y < -(N : ℤ)
      · rw [ite_eq_left hy2, hsp a b x' 0 hxN (by omega)]
        exact cnt3_clamp n _ _ _ _ _ (by push_cast; omega) (by omega)
      · rw [ite_eq_right hy2]
        obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = y + N := ⟨(y + N).toNat, Int.toNat_of_nonneg (by omega)⟩
        rw [← hj, Int.toNat_natCast, hsp a b x' j hxN (by omega)]
        congr 1; omega
    · rw [pget_of_ge (by rw [hlen]; omega)]
      refine (cnt3_eq_zero n _ _ _ _ ?_).symm
      have := le_max_right y 0
      omega

/-- The grid read as a function of the state. -/
def rdL (N : ℕ) (G : List (List PGrid)) (x y : ℤ) : Option (Fin 4) → Option (Fin 4) → ℕ
  | some a, some b => pread N (plget G a b) x y
  | _, _ => 0

/-- The read-out: two explicit steps from the start, then the grids. -/
def F2 (N m : ℕ) (y : ℤ) : ℕ := expand3 (expand3 (rdL N (plev N m))) 0 y none none

theorem F2_eq {N m : ℕ} (hN : N ≤ 17) (hm : m ≤ N) (y : ℤ) :
    F2 N m y = cnt3 (m + 2) 0 y none none := by
  unfold F2
  rw [cnt3_succ]
  refine expand3_congr _ _ _ _ _ _ fun x' y' d hx' => ?_
  rw [cnt3_succ]
  refine expand3_congr _ _ _ _ _ _ fun x'' y'' d' hx'' => ?_
  exact pread_spec hN hm d d' x'' y'' hx''

def aDP (N L : ℕ) : ℕ := F2 N (L - 3) 1

def rDP (N L : ℕ) : ℕ := ((List.range (L - 2)).map fun i : ℕ => F2 N (L - 3) ((i : ℤ) + 2)).sum

theorem A7_eq_aDP {N L : ℕ} (hN : N ≤ 17) (h3 : 3 ≤ L) (hL : L ≤ N + 3) : A7 L = aDP N L := by
  unfold A7 aDP
  rw [F2_eq hN (by omega), show L - 3 + 2 = L - 1 by omega]

theorem R7_eq_rDP {N L : ℕ} (hN : N ≤ 17) (h3 : 3 ≤ L) (hL : L ≤ N + 3) : R7 L = rDP N L := by
  unfold R7 rDP
  rw [sum_Ico_eq_sum_range, sum_range_eq_list]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  rw [F2_eq hN (by omega), show L - 3 + 2 = L - 1 by omega]
  congr 1; push_cast; ring

/-- The largest field of a column. -/
def cmax (J r : ℕ) : ℕ := (List.range J).foldr (fun j acc => max (fld r j) acc) 0

/-- The largest entry of a grid. -/
def pgmax (J : ℕ) (g : PGrid) : ℕ := (g.map (cmax J)).foldr max 0

/-- The largest entry of a level. -/
def plmax (J : ℕ) (G : List (List PGrid)) : ℕ :=
  (G.map fun r => (r.map (pgmax J)).foldr max 0).foldr max 0

theorem le_foldr_max_getD {β : Type*} (f : β → ℕ) (d : β) (hd : f d = 0) :
    ∀ (l : List β) (i : ℕ), f (l.getD i d) ≤ (l.map f).foldr max 0
  | [], i => by simp [hd]
  | x :: l, 0 => by simp
  | x :: l, i + 1 => by
      simp only [List.getD_cons_succ, List.map_cons, List.foldr_cons]
      exact le_trans (le_foldr_max_getD f d hd l i) (le_max_right _ _)

theorem le_foldr_max_mem (f : ℕ → ℕ) : ∀ (l : List ℕ) (j : ℕ), j ∈ l →
    f j ≤ l.foldr (fun j acc => max (f j) acc) 0
  | [], j, h => by simp at h
  | k :: l, j, h => by
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp h with rfl | h
      · exact le_max_left _ _
      · exact le_trans (le_foldr_max_mem f l j h) (le_max_right _ _)

theorem cmax_zero (J : ℕ) : cmax J 0 = 0 := by
  unfold cmax
  induction List.range J with
  | nil => rfl
  | cons k l ih => rw [List.foldr_cons, ih, fld_zero_left, max_self]

theorem pread_le_plmax (N : ℕ) (G : List (List PGrid)) (a b : Fin 4) (x y : ℤ) :
    pread N (plget G a b) x y ≤ plmax (2 * N + 1) G := by
  unfold pread
  split_ifs with h1 h2
  · exact Nat.zero_le _
  all_goals
    refine le_trans ?_ (le_foldr_max_getD (fun r => (r.map (pgmax (2 * N + 1))).foldr max 0) []
      rfl G a.val)
    refine le_trans ?_ (le_foldr_max_getD (pgmax (2 * N + 1)) [] rfl (G.getD a.val []) b.val)
    refine le_trans ?_ (le_foldr_max_getD (cmax (2 * N + 1)) 0 (cmax_zero _) _ x.toNat)
    exact le_foldr_max_mem _ _ _ (List.mem_range.mpr (by omega))

/-! ### The counts to twenty cells -/

set_option maxRecDepth 100000 in
/-- The grid evaluation to seventeen steps, checked by the kernel. -/
theorem dp7_vals :
    (aDP 17 3 = 1 ∧
    aDP 17 4 = 1 ∧
    aDP 17 5 = 2 ∧
    aDP 17 6 = 4 ∧
    aDP 17 7 = 8 ∧
    aDP 17 8 = 18 ∧
    aDP 17 9 = 38 ∧
    aDP 17 10 = 91 ∧
    aDP 17 11 = 185 ∧
    aDP 17 12 = 451 ∧
    aDP 17 13 = 910 ∧
    aDP 17 14 = 2238 ∧
    aDP 17 15 = 4543 ∧
    aDP 17 16 = 11273 ∧
    aDP 17 17 = 23026 ∧
    aDP 17 18 = 57463 ∧
    aDP 17 19 = 118102 ∧
    aDP 17 20 = 295618) ∧
    (rDP 17 3 = 1 ∧
    rDP 17 4 = 2 ∧
    rDP 17 5 = 4 ∧
    rDP 17 6 = 10 ∧
    rDP 17 7 = 24 ∧
    rDP 17 8 = 56 ∧
    rDP 17 9 = 134 ∧
    rDP 17 10 = 312 ∧
    rDP 17 11 = 741 ∧
    rDP 17 12 = 1712 ∧
    rDP 17 13 = 4036 ∧
    rDP 17 14 = 9290 ∧
    rDP 17 15 = 21877 ∧
    rDP 17 16 = 50430 ∧
    rDP 17 17 = 118802 ∧
    rDP 17 18 = 274460 ∧
    rDP 17 19 = 646950 ∧
    rDP 17 20 = 1497708) ∧
    plmax 35 (plev 17 17) = 208774 := by
  decide +kernel

/-- **The H-absorbed (and D-absorbed) counts to twenty cells.** -/
theorem A7_vals :
    A7 2 = 1 ∧
    A7 3 = 1 ∧
    A7 4 = 1 ∧
    A7 5 = 2 ∧
    A7 6 = 4 ∧
    A7 7 = 8 ∧
    A7 8 = 18 ∧
    A7 9 = 38 ∧
    A7 10 = 91 ∧
    A7 11 = 185 ∧
    A7 12 = 451 ∧
    A7 13 = 910 ∧
    A7 14 = 2238 ∧
    A7 15 = 4543 ∧
    A7 16 = 11273 ∧
    A7 17 = 23026 ∧
    A7 18 = 57463 ∧
    A7 19 = 118102 ∧
    A7 20 = 295618 := by
  have h := dp7_vals.1
  rw [← A7_eq_aDP (N := 17) (by norm_num) (L := 3) (by norm_num) (by norm_num),
    ← A7_eq_aDP (N := 17) (by norm_num) (L := 4) (by norm_num) (by norm_num),
    ← A7_eq_aDP (N := 17) (by norm_num) (L := 5) (by norm_num) (by norm_num),
    ← A7_eq_aDP (N := 17) (by norm_num) (L := 6) (by norm_num) (by norm_num),
    ← A7_eq_aDP (N := 17) (by norm_num) (L := 7) (by norm_num) (by norm_num),
    ← A7_eq_aDP (N := 17) (by norm_num) (L := 8) (by norm_num) (by norm_num),
    ← A7_eq_aDP (N := 17) (by norm_num) (L := 9) (by norm_num) (by norm_num),
    ← A7_eq_aDP (N := 17) (by norm_num) (L := 10) (by norm_num) (by norm_num),
    ← A7_eq_aDP (N := 17) (by norm_num) (L := 11) (by norm_num) (by norm_num),
    ← A7_eq_aDP (N := 17) (by norm_num) (L := 12) (by norm_num) (by norm_num),
    ← A7_eq_aDP (N := 17) (by norm_num) (L := 13) (by norm_num) (by norm_num),
    ← A7_eq_aDP (N := 17) (by norm_num) (L := 14) (by norm_num) (by norm_num),
    ← A7_eq_aDP (N := 17) (by norm_num) (L := 15) (by norm_num) (by norm_num),
    ← A7_eq_aDP (N := 17) (by norm_num) (L := 16) (by norm_num) (by norm_num),
    ← A7_eq_aDP (N := 17) (by norm_num) (L := 17) (by norm_num) (by norm_num),
    ← A7_eq_aDP (N := 17) (by norm_num) (L := 18) (by norm_num) (by norm_num),
    ← A7_eq_aDP (N := 17) (by norm_num) (L := 19) (by norm_num) (by norm_num),
    ← A7_eq_aDP (N := 17) (by norm_num) (L := 20) (by norm_num) (by norm_num)] at h
  exact ⟨by decide, h⟩

/-- **The residual counts to twenty cells.** -/
theorem R7_vals :
    R7 2 = 0 ∧
    R7 3 = 1 ∧
    R7 4 = 2 ∧
    R7 5 = 4 ∧
    R7 6 = 10 ∧
    R7 7 = 24 ∧
    R7 8 = 56 ∧
    R7 9 = 134 ∧
    R7 10 = 312 ∧
    R7 11 = 741 ∧
    R7 12 = 1712 ∧
    R7 13 = 4036 ∧
    R7 14 = 9290 ∧
    R7 15 = 21877 ∧
    R7 16 = 50430 ∧
    R7 17 = 118802 ∧
    R7 18 = 274460 ∧
    R7 19 = 646950 ∧
    R7 20 = 1497708 := by
  have h := dp7_vals.2.1
  rw [← R7_eq_rDP (N := 17) (by norm_num) (L := 3) (by norm_num) (by norm_num),
    ← R7_eq_rDP (N := 17) (by norm_num) (L := 4) (by norm_num) (by norm_num),
    ← R7_eq_rDP (N := 17) (by norm_num) (L := 5) (by norm_num) (by norm_num),
    ← R7_eq_rDP (N := 17) (by norm_num) (L := 6) (by norm_num) (by norm_num),
    ← R7_eq_rDP (N := 17) (by norm_num) (L := 7) (by norm_num) (by norm_num),
    ← R7_eq_rDP (N := 17) (by norm_num) (L := 8) (by norm_num) (by norm_num),
    ← R7_eq_rDP (N := 17) (by norm_num) (L := 9) (by norm_num) (by norm_num),
    ← R7_eq_rDP (N := 17) (by norm_num) (L := 10) (by norm_num) (by norm_num),
    ← R7_eq_rDP (N := 17) (by norm_num) (L := 11) (by norm_num) (by norm_num),
    ← R7_eq_rDP (N := 17) (by norm_num) (L := 12) (by norm_num) (by norm_num),
    ← R7_eq_rDP (N := 17) (by norm_num) (L := 13) (by norm_num) (by norm_num),
    ← R7_eq_rDP (N := 17) (by norm_num) (L := 14) (by norm_num) (by norm_num),
    ← R7_eq_rDP (N := 17) (by norm_num) (L := 15) (by norm_num) (by norm_num),
    ← R7_eq_rDP (N := 17) (by norm_num) (L := 16) (by norm_num) (by norm_num),
    ← R7_eq_rDP (N := 17) (by norm_num) (L := 17) (by norm_num) (by norm_num),
    ← R7_eq_rDP (N := 17) (by norm_num) (L := 18) (by norm_num) (by norm_num),
    ← R7_eq_rDP (N := 17) (by norm_num) (L := 19) (by norm_num) (by norm_num),
    ← R7_eq_rDP (N := 17) (by norm_num) (L := 20) (by norm_num) (by norm_num)] at h
  exact ⟨by simp [R7], h⟩

/-- The largest entry at seventeen steps. -/
def M7 : ℕ := 208774

theorem cnt3_le_M7 (x y : ℤ) (a b : Fin 4) (hx : 0 ≤ x) : cnt3 17 x y (some a) (some b) ≤ M7 := by
  rw [← pread_spec (N := 17) le_rfl le_rfl a b x y hx]
  exact le_trans (pread_le_plmax _ _ _ _ _ _) (le_of_eq dp7_vals.2.2)

/-! ### Beyond twenty cells -/

/-- The number of allowed pairs of next steps after `a`, `b`. -/
def cnt2 (a b : Fin 4) : ℕ :=
  ([0, 1, 2, 3] : List (Fin 4)).foldr (fun d acc =>
    (if some b ≠ some (opp d) ∧ some a ≠ some (opp d) then cnt1 (some b) (some d) else 0) + acc) 0

theorem cnt1_le (a b : Fin 4) : cnt1 (some a) (some b) ≤ 3 := by revert a b; decide

theorem cnt1_none_le (d : Fin 4) : cnt1 none (some d) ≤ 3 := by revert d; decide

/-- **Two steps branch at most seven ways.** -/
theorem cnt2_le (a b : Fin 4) : cnt2 a b ≤ 7 := by revert a b; decide

theorem cnt3_one (n M : ℕ) (hM : ∀ x y a b, 0 ≤ x → cnt3 n x y (some a) (some b) ≤ M)
    (x y : ℤ) (a b : Fin 4) : cnt3 (n + 1) x y (some a) (some b) ≤ 3 * M := by
  rw [cnt3_succ]
  exact le_trans (expand3_le_mul _ _ _ _ _ M fun x' y' d hx' => hM _ _ _ _ hx')
    (Nat.mul_le_mul_right _ (cnt1_le a b))

theorem cnt3_two (n M : ℕ) (hM : ∀ x y a b, 0 ≤ x → cnt3 n x y (some a) (some b) ≤ M)
    (x y : ℤ) (a b : Fin 4) : cnt3 (n + 2) x y (some a) (some b) ≤ 7 * M := by
  show cnt3 (n + 1 + 1) x y (some a) (some b) ≤ 7 * M
  rw [cnt3_succ]
  refine le_trans (expand3_le _ x y _ _ (fun d => cnt1 (some b) (some d) * M)
    fun x' y' d _ => ?_) ?_
  · rw [cnt3_succ]
    exact expand3_le_mul _ _ _ _ _ M fun x'' y'' d' hx'' => hM _ _ _ _ hx''
  · have key : ∀ d : Fin 4, (if some b ≠ some (opp d) ∧ some a ≠ some (opp d) ∧ 0 ≤ x + dx d then
        cnt1 (some b) (some d) * M else 0) ≤
        (if some b ≠ some (opp d) ∧ some a ≠ some (opp d) then cnt1 (some b) (some d) else 0) * M := by
      intro d
      by_cases hc : some b ≠ some (opp d) ∧ some a ≠ some (opp d)
      · rw [ite_eq_left hc]; split_ifs <;> simp
      · rw [ite_eq_right hc, zero_mul, ite_eq_right fun h => hc ⟨h.1, h.2.1⟩]
    calc _ ≤ cnt2 a b * M := by
          simp only [cnt2, List.foldr_cons, List.foldr_nil, add_zero, add_mul]
          exact add_le_add (key 0) (add_le_add (key 1) (add_le_add (key 2) (key 3)))
      _ ≤ 7 * M := Nat.mul_le_mul_right _ (cnt2_le a b)

/-- The tail factor: `7` per two steps, `3` for an odd step. -/
def tB (j : ℕ) : ℕ := 7 ^ (j / 2) * (if j % 2 = 1 then 3 else 1)

/-- **Growth at most `√7` per step.** -/
theorem cnt3_tail (n₀ M : ℕ) (hM : ∀ x y a b, 0 ≤ x → cnt3 n₀ x y (some a) (some b) ≤ M) :
    ∀ j (x y : ℤ) (a b : Fin 4), 0 ≤ x → cnt3 (n₀ + j) x y (some a) (some b) ≤ tB j * M
  | 0, x, y, a, b, hx => by simpa [tB] using hM x y a b hx
  | 1, x, y, a, b, _ => by simpa [tB] using cnt3_one n₀ M hM x y a b
  | j + 2, x, y, a, b, _ => by
      rw [show n₀ + (j + 2) = (n₀ + j) + 2 by ring]
      refine le_trans (cnt3_two (n₀ + j) (tB j * M)
        (fun x' y' a' b' hx' => cnt3_tail n₀ M hM j x' y' a' b' hx') x y a b) (le_of_eq ?_)
      rw [tB, tB, show (j + 2) / 2 = j / 2 + 1 by omega, show (j + 2) % 2 = j % 2 by omega, pow_succ]
      ring

/-- The first two steps from the start branch at most nine ways. -/
theorem cnt3_start (n M : ℕ) (hM : ∀ x y a b, 0 ≤ x → cnt3 n x y (some a) (some b) ≤ M)
    (y : ℤ) : cnt3 (n + 2) 0 y none none ≤ 9 * M := by
  show cnt3 (n + 1 + 1) 0 y none none ≤ 9 * M
  rw [cnt3_succ]
  refine le_trans (expand3_le _ 0 y none none (fun _ => 3 * M) fun x' y' d _ => ?_) ?_
  · rw [cnt3_succ]
    exact le_trans (expand3_le_mul _ _ _ _ _ M fun x'' y'' d' hx'' => hM _ _ _ _ hx'')
      (Nat.mul_le_mul_right _ (cnt1_none_le d))
  · simp only [List.foldr_cons, List.foldr_nil, dx]
    norm_num
    omega

/-- The tail bound per cell count, from the largest entry at seventeen steps. -/
def tailA (L : ℕ) : ℕ := 9 * M7 * tB (L - 20)

/-- The residual tail bound: `L - 2` start offsets. -/
def tailR (L : ℕ) : ℕ := (L - 2) * tailA L

theorem cnt3_le_tailA {L : ℕ} (hL : 20 ≤ L) (y : ℤ) : cnt3 (L - 1) 0 y none none ≤ tailA L := by
  unfold tailA
  rw [show L - 1 = (17 + (L - 20)) + 2 by omega]
  calc cnt3 (17 + (L - 20) + 2) 0 y none none ≤ 9 * (tB (L - 20) * M7) :=
        cnt3_start _ _ (fun x y a b hx => cnt3_tail 17 M7 (fun x y a b hx => cnt3_le_M7 x y a b hx)
          (L - 20) x y a b hx) y
    _ = 9 * M7 * tB (L - 20) := by ring

/-- **The absorbed tail.** -/
theorem A7_le_tail {L : ℕ} (hL : 20 ≤ L) : A7 L ≤ tailA L := cnt3_le_tailA hL 1

/-- **The residual tail.** -/
theorem R7_le_tail {L : ℕ} (hL : 20 ≤ L) : R7 L ≤ tailR L := by
  unfold R7 tailR
  calc ∑ d ∈ Ico 2 L, cnt3 (L - 1) 0 (d : ℤ) none none ≤ ∑ _d ∈ Ico 2 L, tailA L :=
        sum_le_sum fun d _ => cnt3_le_tailA hL d
    _ = (L - 2) * tailA L := by rw [sum_const, Nat.card_Ico, smul_eq_mul]

/-! ### The weighted path sums -/

/-- Splitting a weighted count at twenty cells. -/
theorem sum_split_tail (f t : ℕ → ℕ) (ht : ∀ L, 20 < L → f L ≤ t L) (g : ℕ → ℚ)
    (hg : ∀ L, 0 ≤ g L) (N : ℕ) :
    ∑ L ∈ range (N + 1), (f L : ℚ) * g L ≤
      ∑ L ∈ range 21, (f L : ℚ) * g L + ∑ L ∈ Ico 21 (N + 1), (t L : ℚ) * g L := by
  rcases Nat.lt_or_ge (N + 1) 21 with h | h
  · have h1 : ∑ L ∈ range (N + 1), (f L : ℚ) * g L ≤ ∑ L ∈ range 21, (f L : ℚ) * g L :=
      sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr h.le)
        fun L _ _ => mul_nonneg (by positivity) (hg L)
    have h2 : 0 ≤ ∑ L ∈ Ico 21 (N + 1), (t L : ℚ) * g L :=
      sum_nonneg fun L _ => mul_nonneg (by positivity) (hg L)
    linarith
  · rw [← sum_range_add_sum_Ico _ h]
    refine add_le_add le_rfl (sum_le_sum fun L hL => ?_)
    rw [mem_Ico] at hL
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast ht L (by omega)) (hg L)

variable {c m : ℕ}

/-- **H-absorbed paths.** -/
theorem sum_chordless_HA (hc : 1 ≤ c) (w : ℕ) (g : ℕ → ℚ) (hg : ∀ L, 0 ≤ g L) :
    ∑ l ∈ (crossPaths (m := m) hc w).filter (fun l => Chordless l ∧ headRow l = w + 1),
        g l.length ≤
      ∑ L ∈ range 21, (A7 L : ℚ) * g L +
        ∑ L ∈ Ico 21 (Fintype.card (Cell c m) + 1), (tailA L : ℚ) * g L :=
  le_trans (sum_len_le nodup_of_chord A7 (card_chordless_HA hc w) g hg)
    (sum_split_tail A7 tailA (fun _ h => A7_le_tail h.le) g hg _)

/-- **H-residual paths.** -/
theorem sum_chordless_HR (hc : 1 ≤ c) (w : ℕ) (g : ℕ → ℚ) (hg : ∀ L, 0 ≤ g L) :
    ∑ l ∈ (crossPaths (m := m) hc w).filter (fun l => Chordless l ∧ w + 2 ≤ headRow l),
        g l.length ≤
      ∑ L ∈ range 21, (R7 L : ℚ) * g L +
        ∑ L ∈ Ico 21 (Fintype.card (Cell c m) + 1), (tailR L : ℚ) * g L :=
  le_trans (sum_len_le nodup_of_chord R7 (card_chordless_HR hc w) g hg)
    (sum_split_tail R7 tailR (fun _ h => R7_le_tail h.le) g hg _)

/-- **D-absorbed paths.** -/
theorem sum_chordless_DA (hc : 1 ≤ c) (w : ℕ) (g : ℕ → ℚ) (hg : ∀ L, 0 ≤ g L) :
    ∑ l ∈ (crossPaths (m := m) hc w).filter (fun l => Chordless l ∧ lastRow l = w),
        g l.length ≤
      ∑ L ∈ range 21, (A7 L : ℚ) * g L +
        ∑ L ∈ Ico 21 (Fintype.card (Cell c m) + 1), (tailA L : ℚ) * g L :=
  le_trans (sum_len_le nodup_of_chord A7 (card_chordless_DA hc w) g hg)
    (sum_split_tail A7 tailA (fun _ h => A7_le_tail h.le) g hg _)

/-- **D-residual paths.** -/
theorem sum_chordless_DR (hc : 1 ≤ c) (w : ℕ) (g : ℕ → ℚ) (hg : ∀ L, 0 ≤ g L) :
    ∑ l ∈ (crossPaths (m := m) hc w).filter (fun l => Chordless l ∧ lastRow l + 1 ≤ w),
        g l.length ≤
      ∑ L ∈ range 21, (R7 L : ℚ) * g L +
        ∑ L ∈ Ico 21 (Fintype.card (Cell c m) + 1), (tailR L : ℚ) * g L :=
  le_trans (sum_len_le nodup_of_chord R7 (card_chordless_DR hc w) g hg)
    (sum_split_tail R7 tailR (fun _ h => R7_le_tail h.le) g hg _)

/-! ### The tail series for weights `(1/4)^L` -/

theorem tB_le (j : ℕ) : (tB j : ℚ) ≤ 9 / 8 * (8 / 3) ^ j := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' j
  · rw [tB, show 2 * k / 2 = k by omega, show 2 * k % 2 = 0 by omega, pow_mul]
    norm_num
    have : (7 : ℚ) ^ k ≤ (64 / 9) ^ k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
    have h1 : (0 : ℚ) ≤ (64 / 9) ^ k := by positivity
    linarith
  · rw [tB, show (2 * k + 1) / 2 = k by omega, show (2 * k + 1) % 2 = 1 by omega, pow_succ,
      pow_mul]
    norm_num
    have : (7 : ℚ) ^ k ≤ (64 / 9) ^ k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
    nlinarith

theorem geom_two_thirds (K : ℕ) :
    ∑ i ∈ range K, (2 / 3 : ℚ) ^ (i + 1) = 2 - 2 * (2 / 3) ^ K := by
  induction K with
  | zero => simp
  | succ K ih => rw [sum_range_succ, ih, pow_succ]; ring

theorem geom_two_thirds' (K : ℕ) :
    ∑ i ∈ range K, ((i : ℚ) + 19) * (2 / 3) ^ (i + 1) = 42 - (2 * K + 42) * (2 / 3) ^ K := by
  induction K with
  | zero => simp
  | succ K ih => rw [sum_range_succ, ih, pow_succ]; push_cast; ring

theorem tailA_term (i : ℕ) :
    (tailA (21 + i) : ℚ) * (1 / 4) ^ (21 + i) ≤
      9 * M7 * (9 / 8) / 4 ^ 20 * (2 / 3) ^ (i + 1) := by
  unfold tailA
  rw [show 21 + i - 20 = i + 1 by omega]
  push_cast
  have h := tB_le (i + 1)
  have e : (9 * (M7 : ℚ) * (9 / 8) / 4 ^ 20 * (2 / 3) ^ (i + 1)) =
      9 * M7 * (9 / 8 * (8 / 3) ^ (i + 1)) * (1 / 4) ^ (21 + i) := by
    have e1 : (2 / 3 : ℚ) ^ (i + 1) = (8 / 3) ^ (i + 1) * (1 / 4) ^ (i + 1) := by
      rw [← mul_pow]; norm_num
    have e2 : (1 / 4 : ℚ) ^ (21 + i) = (1 / 4) ^ 20 * (1 / 4) ^ (i + 1) := by
      rw [← pow_add]; ring_nf
    rw [e1, e2]
    ring
  rw [e]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-- **The absorbed tail series** for weights `(1/4)^L`. -/
theorem tailA_sum_le (N : ℕ) :
    ∑ L ∈ Ico 21 N, (tailA L : ℚ) * (1 / 4) ^ L ≤ 81 / 4 * M7 / 4 ^ 20 := by
  rw [sum_Ico_eq_sum_range]
  calc ∑ i ∈ range (N - 21), (tailA (21 + i) : ℚ) * (1 / 4) ^ (21 + i)
      ≤ ∑ i ∈ range (N - 21), 9 * M7 * (9 / 8) / 4 ^ 20 * (2 / 3 : ℚ) ^ (i + 1) :=
        sum_le_sum fun i _ => tailA_term i
    _ = 9 * M7 * (9 / 8) / 4 ^ 20 * (2 - 2 * (2 / 3) ^ (N - 21)) := by
        rw [← mul_sum, geom_two_thirds]
    _ ≤ 81 / 4 * M7 / 4 ^ 20 := by
        have : (0 : ℚ) ≤ (2 / 3) ^ (N - 21) := by positivity
        have hM : (0 : ℚ) ≤ M7 := by positivity
        nlinarith

/-- **The residual tail series** for weights `(1/4)^L`. -/
theorem tailR_sum_le (N : ℕ) :
    ∑ L ∈ Ico 21 N, (tailR L : ℚ) * (1 / 4) ^ L ≤ 1701 / 4 * M7 / 4 ^ 20 := by
  rw [sum_Ico_eq_sum_range]
  calc ∑ i ∈ range (N - 21), (tailR (21 + i) : ℚ) * (1 / 4) ^ (21 + i)
      ≤ ∑ i ∈ range (N - 21), 9 * M7 * (9 / 8) / 4 ^ 20 * (((i : ℚ) + 19) * (2 / 3 : ℚ) ^ (i + 1)) :=
        sum_le_sum fun i _ => by
          unfold tailR
          rw [show 21 + i - 2 = i + 19 by omega]
          push_cast
          have := tailA_term i
          have h0 : (0 : ℚ) ≤ (i : ℚ) + 19 := by positivity
          calc ((i : ℚ) + 19) * (tailA (21 + i) : ℚ) * (1 / 4) ^ (21 + i)
              = ((i : ℚ) + 19) * ((tailA (21 + i) : ℚ) * (1 / 4) ^ (21 + i)) := by ring
            _ ≤ ((i : ℚ) + 19) * (9 * M7 * (9 / 8) / 4 ^ 20 * (2 / 3) ^ (i + 1)) :=
                mul_le_mul_of_nonneg_left this h0
            _ = _ := by ring
    _ = 9 * M7 * (9 / 8) / 4 ^ 20 * (42 - (2 * (N - 21 : ℕ) + 42) * (2 / 3) ^ (N - 21)) := by
        rw [← mul_sum, geom_two_thirds']
    _ ≤ 1701 / 4 * M7 / 4 ^ 20 := by
        have : (0 : ℚ) ≤ (2 * ((N - 21 : ℕ) : ℚ) + 42) * (2 / 3) ^ (N - 21) := by positivity
        have hM : (0 : ℚ) ≤ M7 := by positivity
        nlinarith

end GridGen.Gauge
