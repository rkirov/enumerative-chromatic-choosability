/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Nine.Counts

/-!
# Crossing-walk counts by dynamic programming

`cntW x y prev n` counts the `n`-step shape walks from `(x, y)` after the step `prev`. It is
defined by a recursion that branches four ways, so evaluating it costs `3^n`. Here the same
recursion is run level by level on a grid of cells `x ∈ [0, N]`, `y ∈ [-N, N]`, one grid per
previous step (`levL`). A step is a shift of a grid. Three boundaries need care:

* left of `x = 0`, and past `x = N` or `y = N`, the counts are zero (`cntW_eq_zero`);
* below `y = -N` the counts no longer depend on `y`: every walk of at most `N` steps from there
  ends below the cut (`cntW_clamp`), so the downward shift repeats the bottom row.

`levL_spec` identifies the grids with `cntW`, and `cntDP_eq` the read-out with `shapeCnt`.
Kernel evaluation of `cntDP` takes seconds where `cntW` took minutes at twelve cells. This file
proves the counts up to eighteen cells: `33190, 96757, 264376, 772192, 2132440, 6246601`.
-/

open Finset

namespace GridGen.Gauge

/-! ### The recursion of `cntW`, unpruned -/

/-- The four-way branch of `cntW`. -/
def cntS (x y : ℤ) (prev : Option (Fin 4)) (n : ℕ) : ℕ :=
  ([0, 1, 2, 3] : List (Fin 4)).foldr (fun d acc =>
    (if prev ≠ some (opp d) ∧ 0 ≤ x + dx d then cntW (x + dx d) (y + dy d) (some d) n else 0) + acc) 0

theorem cntW_zero_eq (x y : ℤ) (prev : Option (Fin 4)) :
    cntW x y prev 0 = if x = 0 ∧ y ≤ 0 then 1 else 0 := rfl

theorem cntW_succ_eq (x y : ℤ) (prev : Option (Fin 4)) (n : ℕ) :
    cntW x y prev (n + 1) = if (n + 1 : ℤ) < x + max y 0 then 0 else cntS x y prev n := rfl

/-- Walks too short to return count zero. -/
theorem cntW_eq_zero : ∀ (n : ℕ) (x y : ℤ) (prev : Option (Fin 4)),
    (n : ℤ) < x + max y 0 → cntW x y prev n = 0
  | 0, x, y, prev, h => by
      rw [cntW_zero_eq, ite_eq_right]
      rintro ⟨rfl, hy⟩
      have : max y 0 = 0 := max_eq_right hy
      omega
  | n + 1, x, y, prev, h => by
      rw [cntW_succ_eq, ite_eq_left (by exact_mod_cast h)]

/-- The pruning never changes the count. -/
theorem cntW_succ (x y : ℤ) (prev : Option (Fin 4)) (n : ℕ) :
    cntW x y prev (n + 1) = cntS x y prev n := by
  rw [cntW_succ_eq]
  split_ifs with h
  · unfold cntS
    simp only [List.foldr_cons, List.foldr_nil, add_zero]
    have hz : ∀ d : Fin 4, cntW (x + dx d) (y + dy d) (some d) n = 0 := by
      intro d
      refine cntW_eq_zero n _ _ _ ?_
      fin_cases d <;> simp [dx, dy] <;> omega
    simp only [hz, ite_self, add_zero]
  · rfl

/-- **Below the reach of the walk the counts do not depend on `y`.** -/
theorem cntW_clamp : ∀ (n : ℕ) (x y y' : ℤ) (prev : Option (Fin 4)),
    y ≤ -(n : ℤ) → y' ≤ -(n : ℤ) → cntW x y prev n = cntW x y' prev n
  | 0, x, y, y', prev, h, h' => by
      rw [cntW_zero_eq, cntW_zero_eq]
      have h1 : y ≤ 0 := by omega
      have h2 : y' ≤ 0 := by omega
      simp [h1, h2]
  | n + 1, x, y, y', prev, h, h' => by
      rw [cntW_succ_eq, cntW_succ_eq]
      have e1 : max y 0 = 0 := max_eq_right (by omega)
      have e2 : max y' 0 = 0 := max_eq_right (by omega)
      rw [e1, e2]
      split_ifs
      · rfl
      · unfold cntS
        simp only [List.foldr_cons, List.foldr_nil, add_zero]
        have hc : ∀ d : Fin 4, cntW (x + dx d) (y + dy d) (some d) n =
            cntW (x + dx d) (y' + dy d) (some d) n := by
          intro d
          refine cntW_clamp n _ _ _ _ ?_ ?_ <;> fin_cases d <;> simp [dy] <;> omega
        simp only [hc]

/-! ### Grids -/

/-- A grid: rows indexed by `x`, entries by `j = y + N`. -/
abbrev Grid := List (List ℕ)

/-- The entry of a grid (zero off the grid). -/
def gget (g : Grid) (x j : ℕ) : ℕ := (g.getD x []).getD j 0

/-- Every grid here has `X` rows of `J` entries. -/
def Shaped (X J : ℕ) (g : Grid) : Prop := g.length = X ∧ ∀ r ∈ g, r.length = J

def zrow (J : ℕ) : List ℕ := List.replicate J 0

/-- Entrywise sum. -/
def gadd (g h : Grid) : Grid := List.zipWith (List.zipWith (· + ·)) g h

/-- Read `x + 1`. -/
def shXp (J : ℕ) (g : Grid) : Grid := g.tail ++ [zrow J]

/-- Read `x - 1`, zero at `x = 0`. -/
def shXm (J : ℕ) (g : Grid) : Grid := zrow J :: g.dropLast

/-- Read `j + 1`. -/
def shYp (g : Grid) : Grid := g.map fun r => r.tail ++ [0]

/-- Read `j - 1`, repeating the bottom row. -/
def shYm (g : Grid) : Grid := g.map fun r => r.headD 0 :: r.dropLast

theorem getD_eq_getElem? {α : Type*} (l : List α) (i : ℕ) (d : α) :
    l.getD i d = (l[i]?).getD d := by
  rw [List.getD_eq_getElem?_getD]

theorem gget_eq (g : Grid) (x j : ℕ) : gget g x j = ((g[x]?).getD [])[j]?.getD 0 := by
  unfold gget; rw [getD_eq_getElem?, getD_eq_getElem?]

theorem gget_of_ge {X J : ℕ} {g : Grid} (hg : Shaped X J g) {x j : ℕ} (h : X ≤ x ∨ J ≤ j) :
    gget g x j = 0 := by
  rw [gget_eq]
  rcases Nat.lt_or_ge x X with hx | hx
  · have hxg : x < g.length := by rw [hg.1]; exact hx
    have e : g[x]? = some g[x] := List.getElem?_eq_getElem hxg
    have hj : J ≤ j := by omega
    have e2 : g[x][j]? = none := List.getElem?_eq_none (by rw [hg.2 _ (List.getElem_mem _)]; exact hj)
    rw [e, Option.getD_some, e2]; rfl
  · have e : g[x]? = none := List.getElem?_eq_none (by rw [hg.1]; exact hx)
    rw [e]; simp

theorem shaped_gadd {X J : ℕ} {g h : Grid} (hg : Shaped X J g) (hh : Shaped X J h) :
    Shaped X J (gadd g h) := by
  refine ⟨by simp [gadd, hg.1, hh.1], fun r hr => ?_⟩
  unfold gadd at hr
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  rw [List.getElem_zipWith, List.length_zipWith, hg.2 _ (List.getElem_mem _),
    hh.2 _ (List.getElem_mem _), min_self]

theorem gget_gadd {X J : ℕ} {g h : Grid} (hg : Shaped X J g) (hh : Shaped X J h) (x j : ℕ) :
    gget (gadd g h) x j = gget g x j + gget h x j := by
  rcases Nat.lt_or_ge x X with hx | hx
  · rcases Nat.lt_or_ge j J with hj | hj
    · have hxg : x < g.length := by rw [hg.1]; exact hx
      have hxh : x < h.length := by rw [hh.1]; exact hx
      have hjg : j < g[x].length := by rw [hg.2 _ (List.getElem_mem _)]; exact hj
      have hjh : j < h[x].length := by rw [hh.2 _ (List.getElem_mem _)]; exact hj
      rw [gget_eq, gget_eq, gget_eq]
      unfold gadd
      rw [List.getElem?_zipWith, List.getElem?_eq_getElem hxg, List.getElem?_eq_getElem hxh]
      simp only [Option.getD_some]
      rw [List.getElem?_zipWith, List.getElem?_eq_getElem hjg, List.getElem?_eq_getElem hjh]
      simp
    · rw [gget_of_ge (shaped_gadd hg hh) (Or.inr hj), gget_of_ge hg (Or.inr hj),
        gget_of_ge hh (Or.inr hj)]
  · rw [gget_of_ge (shaped_gadd hg hh) (Or.inl hx), gget_of_ge hg (Or.inl hx),
      gget_of_ge hh (Or.inl hx)]

theorem shaped_zrow {J : ℕ} : (zrow J).length = J := by simp [zrow]

theorem shaped_shXp {X J : ℕ} {g : Grid} (hX : 1 ≤ X) (hg : Shaped X J g) :
    Shaped X J (shXp J g) := by
  refine ⟨by simp [shXp, hg.1]; omega, fun r hr => ?_⟩
  simp only [shXp, List.mem_append, List.mem_singleton] at hr
  rcases hr with hr | rfl
  · exact hg.2 r (List.mem_of_mem_tail hr)
  · exact shaped_zrow

theorem gget_shXp {X J : ℕ} {g : Grid} (hX : 1 ≤ X) (hg : Shaped X J g) (x j : ℕ) :
    gget (shXp J g) x j = gget g (x + 1) j := by
  rcases Nat.lt_or_ge x (X - 1) with hx | hx
  · rw [gget_eq, gget_eq]
    unfold shXp
    rw [List.getElem?_append_left (by rw [List.length_tail, hg.1]; exact hx), List.getElem?_tail]
  · rcases Nat.lt_or_ge x X with hx' | hx'
    · have e : x = X - 1 := by omega
      rw [gget_of_ge hg (Or.inl (by omega)), gget_eq]
      unfold shXp
      rw [List.getElem?_append_right (by rw [List.length_tail, hg.1]; omega)]
      rw [show x - g.tail.length = 0 by rw [List.length_tail, hg.1]; omega]
      simp [zrow]
    · rw [gget_of_ge (shaped_shXp hX hg) (Or.inl hx'), gget_of_ge hg (Or.inl (by omega))]

theorem shaped_shXm {X J : ℕ} {g : Grid} (hX : 1 ≤ X) (hg : Shaped X J g) :
    Shaped X J (shXm J g) := by
  refine ⟨by simp [shXm, hg.1]; omega, fun r hr => ?_⟩
  simp only [shXm, List.mem_cons] at hr
  rcases hr with rfl | hr
  · exact shaped_zrow
  · exact hg.2 r (List.mem_of_mem_dropLast hr)

theorem gget_shXm {X J : ℕ} {g : Grid} (hX : 1 ≤ X) (hg : Shaped X J g) {x : ℕ} (hx : x < X)
    (j : ℕ) : gget (shXm J g) x j = if x = 0 then 0 else gget g (x - 1) j := by
  rw [gget_eq]
  unfold shXm
  split_ifs with h
  · subst h; simp [zrow]
  · obtain ⟨x', rfl⟩ : ∃ x', x = x' + 1 := ⟨x - 1, by omega⟩
    rw [List.getElem?_cons_succ, List.getElem?_dropLast, ite_eq_left (by rw [hg.1]; omega), gget_eq,
      show x' + 1 - 1 = x' by omega]

theorem shaped_shYp {X J : ℕ} {g : Grid} (hJ : 1 ≤ J) (hg : Shaped X J g) :
    Shaped X J (shYp g) := by
  refine ⟨by simp [shYp, hg.1], fun r hr => ?_⟩
  simp only [shYp, List.mem_map] at hr
  obtain ⟨r', hr', rfl⟩ := hr
  simp [hg.2 r' hr']; omega

theorem gget_shYp {X J : ℕ} {g : Grid} (hJ : 1 ≤ J) (hg : Shaped X J g) (x j : ℕ) :
    gget (shYp g) x j = gget g x (j + 1) := by
  rcases Nat.lt_or_ge x X with hx | hx
  · have hxg : x < g.length := by rw [hg.1]; exact hx
    have hr := hg.2 _ (List.getElem_mem hxg)
    rw [gget_eq, gget_eq]
    unfold shYp
    rw [List.getElem?_map, List.getElem?_eq_getElem hxg]
    simp only [Option.map_some, Option.getD_some]
    rcases Nat.lt_or_ge j (J - 1) with hj | hj
    · rw [List.getElem?_append_left (by rw [List.length_tail, hr]; exact hj), List.getElem?_tail]
    · rcases Nat.lt_or_ge j J with hj' | hj'
      · have e2 : g[x][j + 1]? = none := List.getElem?_eq_none (by rw [hr]; omega)
        rw [e2, List.getElem?_append_right (by rw [List.length_tail, hr]; omega),
          show j - g[x].tail.length = 0 by rw [List.length_tail, hr]; omega]
        rfl
      · rw [List.getElem?_eq_none (by simp [hr]; omega), List.getElem?_eq_none (by rw [hr]; omega)]
  · rw [gget_of_ge (shaped_shYp hJ hg) (Or.inl hx), gget_of_ge hg (Or.inl hx)]

theorem shaped_shYm {X J : ℕ} {g : Grid} (hJ : 1 ≤ J) (hg : Shaped X J g) :
    Shaped X J (shYm g) := by
  refine ⟨by simp [shYm, hg.1], fun r hr => ?_⟩
  simp only [shYm, List.mem_map] at hr
  obtain ⟨r', hr', rfl⟩ := hr
  simp [hg.2 r' hr']; omega

theorem gget_shYm {X J : ℕ} {g : Grid} (hJ : 1 ≤ J) (hg : Shaped X J g) (x : ℕ) {j : ℕ}
    (hj : j < J) : gget (shYm g) x j = gget g x (j - 1) := by
  rcases Nat.lt_or_ge x X with hx | hx
  · have hxg : x < g.length := by rw [hg.1]; exact hx
    have hr := hg.2 _ (List.getElem_mem hxg)
    rw [gget_eq, gget_eq]
    unfold shYm
    rw [List.getElem?_map, List.getElem?_eq_getElem hxg]
    simp only [Option.map_some, Option.getD_some]
    obtain ⟨a, r, hr'⟩ : ∃ a r, g[x] = a :: r := by
      cases h : g[x] with
      | nil => rw [h] at hr; simp at hr; omega
      | cons a r => exact ⟨a, r, rfl⟩
    rw [hr']
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [List.headD_cons, List.getElem?_cons_succ, List.getElem?_dropLast,
        ite_eq_left (by rw [hr'] at hr; simp only [List.length_cons] at hr ⊢; omega),
        show j' + 1 - 1 = j' by omega]
  · rw [gget_of_ge (shaped_shYm hJ hg) (Or.inl hx), gget_of_ge hg (Or.inl hx)]

/-! ### The levels -/

/-- The four grids of a level, one per previous step. -/
structure Lev where
  g0 : Grid
  g1 : Grid
  g2 : Grid
  g3 : Grid

/-- The grid of a previous step. -/
def Lev.get (G : Lev) : Fin 4 → Grid
  | 0 => G.g0 | 1 => G.g1 | 2 => G.g2 | 3 => G.g3

def initG (X J N : ℕ) : Grid :=
  (List.range X).map fun x => (List.range J).map fun j => if x = 0 ∧ j ≤ N then 1 else 0

/-- One step. After the step `p` the next step is anything but `opp p`. Steps `0, 1` read
`y ∓ 1`, steps `2, 3` read `x ± 1`. -/
def stepL (J : ℕ) (G : Lev) : Lev :=
  let a0 := shYm G.g0
  let a1 := shYp G.g1
  let a2 := shXp J G.g2
  let a3 := shXm J G.g3
  ⟨gadd a0 (gadd a2 a3), gadd a1 (gadd a2 a3), gadd a0 (gadd a1 a2), gadd a0 (gadd a1 a3)⟩

/-- The levels. -/
def levL (X J N : ℕ) : ℕ → Lev
  | 0 => ⟨initG X J N, initG X J N, initG X J N, initG X J N⟩
  | n + 1 => stepL J (levL X J N n)

theorem shaped_initG (X J N : ℕ) : Shaped X J (initG X J N) := by
  refine ⟨by simp [initG], fun r hr => ?_⟩
  simp only [initG, List.mem_map, List.mem_range] at hr
  obtain ⟨x, _, rfl⟩ := hr
  simp

theorem gget_initG {X J N x j : ℕ} (hx : x < X) (hj : j < J) :
    gget (initG X J N) x j = if x = 0 ∧ j ≤ N then 1 else 0 := by
  rw [gget_eq]; simp [initG, hx, hj]

theorem shaped_levL {X J N : ℕ} (hX : 1 ≤ X) (hJ : 1 ≤ J) :
    ∀ n (p : Fin 4), Shaped X J ((levL X J N n).get p)
  | 0, p => by fin_cases p <;> exact shaped_initG X J N
  | n + 1, p => by
      have h := shaped_levL (N := N) hX hJ n
      have s0 := shaped_shYm hJ (h 0)
      have s1 := shaped_shYp hJ (h 1)
      have s2 := shaped_shXp hX (h 2)
      have s3 := shaped_shXm hX (h 3)
      fin_cases p <;> simp only [levL, stepL, Lev.get] <;>
        exact shaped_gadd ‹_› (shaped_gadd ‹_› ‹_›)

/-- **The grids are the counts.** -/
theorem levL_spec (N : ℕ) : ∀ n, n ≤ N → ∀ (p : Fin 4) (x j : ℕ), x < N + 1 → j < 2 * N + 1 →
    gget ((levL (N + 1) (2 * N + 1) N n).get p) x j = cntW x ((j : ℤ) - N) (some p) n
  | 0, _, p, x, j, hx, hj => by
      have e : (levL (N + 1) (2 * N + 1) N 0).get p = initG (N + 1) (2 * N + 1) N := by
        fin_cases p <;> rfl
      rw [e, gget_initG hx hj, cntW_zero_eq]
      congr 1
      apply propext
      constructor
      · rintro ⟨rfl, h⟩; exact ⟨rfl, by omega⟩
      · rintro ⟨h1, h2⟩; exact ⟨by exact_mod_cast h1, by omega⟩
  | n + 1, hn, p, x, j, hx, hj => by
      have hX : 1 ≤ N + 1 := by omega
      have hJ : 1 ≤ 2 * N + 1 := by omega
      have h := shaped_levL (N := N) hX hJ n
      have ih := levL_spec N n (by omega)
      set G := levL (N + 1) (2 * N + 1) N n
      -- the four shifted reads
      have r0 : gget (shYm (G.get 0)) x j = cntW x ((j : ℤ) - N + dy 0) (some 0) n := by
        rw [gget_shYm hJ (h 0) x hj]
        rcases Nat.eq_zero_or_pos j with rfl | hj0
        · rw [ih 0 x 0 hx (by omega)]
          exact cntW_clamp n _ _ _ _ (by push_cast; omega) (by simp [dy]; omega)
        · rw [ih 0 x (j - 1) hx (by omega)]
          congr 1; simp [dy]; omega
      have r1 : gget (shYp (G.get 1)) x j = cntW x ((j : ℤ) - N + dy 1) (some 1) n := by
        rw [gget_shYp hJ (h 1)]
        rcases Nat.lt_or_ge (j + 1) (2 * N + 1) with hj1 | hj1
        · rw [ih 1 x (j + 1) hx hj1]; congr 1; simp [dy]; ring
        · rw [gget_of_ge (h 1) (Or.inr hj1)]
          refine (cntW_eq_zero n _ _ _ ?_).symm
          simp [dy]; omega
      have r2 : gget (shXp (2 * N + 1) (G.get 2)) x j =
          cntW (x + dx 2) ((j : ℤ) - N + dy 2) (some 2) n := by
        rw [gget_shXp hX (h 2)]
        rcases Nat.lt_or_ge (x + 1) (N + 1) with hx1 | hx1
        · rw [ih 2 (x + 1) j hx1 hj]; simp [dx, dy]
        · rw [gget_of_ge (h 2) (Or.inl hx1)]
          refine (cntW_eq_zero n _ _ _ ?_).symm
          simp [dx, dy]; omega
      have r3 : gget (shXm (2 * N + 1) (G.get 3)) x j =
          if 0 ≤ (x : ℤ) + dx 3 then cntW (x + dx 3) ((j : ℤ) - N + dy 3) (some 3) n else 0 := by
        rw [gget_shXm hX (h 3) hx]
        rcases Nat.eq_zero_or_pos x with rfl | hx0
        · simp [dx]
        · rw [ite_eq_right (by omega), ite_eq_left (by simp [dx]; omega), ih 3 (x - 1) j (by omega) hj]
          congr 1 <;> simp [dx, dy]; omega
      rw [cntW_succ]
      unfold cntS
      simp only [List.foldr_cons, List.foldr_nil, add_zero]
      have hx0 : (0 : ℤ) ≤ x + dx 0 := by simp [dx]
      have hx1 : (0 : ℤ) ≤ x + dx 1 := by simp [dx]
      have hx2 : (0 : ℤ) ≤ x + dx 2 := by simp [dx]; omega
      have e0 : (x : ℤ) + dx 0 = x := by simp [dx]
      have e1 : (x : ℤ) + dx 1 = x := by simp [dx]
      have g0 := shaped_shYm hJ (h 0)
      have g1 := shaped_shYp hJ (h 1)
      have g2 := shaped_shXp hX (h 2)
      have g3 := shaped_shXm hX (h 3)
      simp only [hx2, e0, e1, and_true]
      fin_cases p
      · show gget (gadd (shYm (G.get 0)) (gadd (shXp _ (G.get 2)) (shXm _ (G.get 3)))) x j = _
        rw [gget_gadd g0 (shaped_gadd g2 g3), gget_gadd g2 g3, r0, r2, r3]
        simp [opp]
      · show gget (gadd (shYp (G.get 1)) (gadd (shXp _ (G.get 2)) (shXm _ (G.get 3)))) x j = _
        rw [gget_gadd g1 (shaped_gadd g2 g3), gget_gadd g2 g3, r1, r2, r3]
        simp [opp]
      · show gget (gadd (shYm (G.get 0)) (gadd (shYp (G.get 1)) (shXp _ (G.get 2)))) x j = _
        rw [gget_gadd g0 (shaped_gadd g1 g2), gget_gadd g1 g2, r0, r1, r2]
        simp [opp]
      · show gget (gadd (shYm (G.get 0)) (gadd (shYp (G.get 1)) (shXm _ (G.get 3)))) x j = _
        rw [gget_gadd g0 (shaped_gadd g1 g3), gget_gadd g1 g3, r0, r1, r3]
        simp [opp]

/-- The read-out: the shapes with `L` cells. -/
def cntDP (N L : ℕ) : ℕ :=
  ((List.range (L - 1)).map fun d =>
    gget (shYm (levL (N + 1) (2 * N + 1) N (L - 2)).g0) 0 (d + 1 + N) +
      gget (shYp (levL (N + 1) (2 * N + 1) N (L - 2)).g1) 0 (d + 1 + N) +
        gget (shXp (2 * N + 1) (levL (N + 1) (2 * N + 1) N (L - 2)).g2) 0 (d + 1 + N)).sum

/-- **The read-out is the shape count.** -/
theorem cntDP_eq {N L : ℕ} (h2 : 2 ≤ L) (hL : L ≤ N) : cntDP N L = shapeCnt L := by
  unfold cntDP shapeCnt
  congr 1
  refine List.map_congr_left fun d hd => ?_
  rw [List.mem_range] at hd
  have hX : 1 ≤ N + 1 := by omega
  have hJ : 1 ≤ 2 * N + 1 := by omega
  have h := shaped_levL (N := N) hX hJ (L - 2)
  have spec := levL_spec N (L - 2) (by omega)
  have h0 : Shaped (N + 1) (2 * N + 1) (levL (N + 1) (2 * N + 1) N (L - 2)).g0 := h 0
  have h1 : Shaped (N + 1) (2 * N + 1) (levL (N + 1) (2 * N + 1) N (L - 2)).g1 := h 1
  have h2' : Shaped (N + 1) (2 * N + 1) (levL (N + 1) (2 * N + 1) N (L - 2)).g2 := h 2
  rw [show L - 1 = (L - 2) + 1 by omega, cntW_succ]
  unfold cntS
  simp only [List.foldr_cons, List.foldr_nil, add_zero, ne_eq, reduceCtorEq, not_false_eq_true,
    true_and]
  have a0 : gget (shYm (levL (N + 1) (2 * N + 1) N (L - 2)).g0) 0 (d + 1 + N) =
      cntW (0 + dx 0) ((d : ℤ) + 1 + dy 0) (some 0) (L - 2) := by
    rw [gget_shYm hJ h0 0 (by omega)]
    have := spec 0 0 (d + 1 + N - 1) (by omega) (by omega)
    simp only [Lev.get] at this
    rw [this]; congr 1; simp [dy]
  have a1 : gget (shYp (levL (N + 1) (2 * N + 1) N (L - 2)).g1) 0 (d + 1 + N) =
      cntW (0 + dx 1) ((d : ℤ) + 1 + dy 1) (some 1) (L - 2) := by
    rw [gget_shYp hJ h1]
    have := spec 1 0 (d + 1 + N + 1) (by omega) (by omega)
    simp only [Lev.get] at this
    rw [this]; congr 1; simp [dy]; ring
  have a2 : gget (shXp (2 * N + 1) (levL (N + 1) (2 * N + 1) N (L - 2)).g2) 0 (d + 1 + N) =
      cntW (0 + dx 2) ((d : ℤ) + 1 + dy 2) (some 2) (L - 2) := by
    rw [gget_shXp hX h2']
    have := spec 2 1 (d + 1 + N) (by omega) (by omega)
    simp only [Lev.get] at this
    rw [this]; congr 1; simp [dy]
  rw [a0, a1, a2]
  have n3 : ¬ (0 : ℤ) ≤ 0 + dx 3 := by simp [dx]
  simp only [dx, add_zero]
  norm_num
  ring

/-! ### The counts to eighteen cells -/

set_option maxRecDepth 100000 in
theorem shapeCnt_13_18 :
    shapeCnt 13 = 33190 ∧ shapeCnt 14 = 96757 ∧ shapeCnt 15 = 264376 ∧
      shapeCnt 16 = 772192 ∧ shapeCnt 17 = 2132440 ∧ shapeCnt 18 = 6246601 := by
  rw [← cntDP_eq (N := 18) (by norm_num) (by norm_num), ← cntDP_eq (N := 18) (by norm_num) (by norm_num),
    ← cntDP_eq (N := 18) (by norm_num) (by norm_num), ← cntDP_eq (N := 18) (by norm_num) (by norm_num),
    ← cntDP_eq (N := 18) (by norm_num) (by norm_num), ← cntDP_eq (N := 18) (by norm_num) (by norm_num)]
  decide +kernel

end GridGen.Gauge
