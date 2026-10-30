/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Six.BitFast

/-!
# Height six at `k = 6`: the kernel check of the state bits

The certificate check `chkW` over the admissible code vectors, arranged so that most of the work
is shared along the enumeration (one definition per row, `ew1` … `ew6`):

* **The greedy count by levels** (`dpG`, `dpG_eq`): each level computes the intervals ending at
  its row and the count so far, as a pair of naturals (positive and negative part), once for all
  the code vectors below it.
* **The denominators** are a literal binary tree indexed by the row bonuses (`look`, `treeOK`,
  `look_eq`), so the leaf finds its value at once.
* **The pins** are bit masks over the pin list (`maskOf`, `tb`), one per row and code
  (`rowTable`). Each pin's multiplier is added at the last row its conditions read
  (`lastLists`, `fmS`), so the leaf sees the fired multipliers already summed (`sum_last_eq`).

`chkW_spec` gives the leaf inequality of every admissible code vector.
-/

namespace GridGen.Six

open Finset

/-! ### The greedy count by levels -/

/-- The positive and negative parts of the counts of the prefixes, as functions of the sizes
and intersections (the recursion unrolled). -/
def dpG (n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 : ℕ) : ℕ × ℕ :=
  let t1 := Nat.sub (Nat.add e1 e2) n2
  let t2 := Nat.sub (Nat.add e2 e3) n3
  let t3 := Nat.sub (Nat.add e3 e4) n4
  let t4 := Nat.sub (Nat.add e4 e5) n5
  let q1 := minR t1 t2
  let q2 := minR t2 t3
  let q3 := minR t3 t4
  let p1 := Nat.sub (Nat.add q1 q2) t2
  let p2 := Nat.sub (Nat.add q2 q3) t3
  let x := minR p1 p2
  -- G₁ = n₁
  let g1p := n1
  let g1m := 0
  -- G₂ = n₂ G₁ - e₁
  let g2p := Nat.add (Nat.mul n2 g1p) 0
  let g2m := Nat.add (Nat.mul n2 g1m) e1
  -- G₃ = n₃ G₂ - e₂ G₁ + t₁
  let g3p := Nat.add (Nat.add (Nat.mul n3 g2p) (Nat.mul e2 g1m)) t1
  let g3m := Nat.add (Nat.mul n3 g2m) (Nat.mul e2 g1p)
  -- G₄ = n₄ G₃ - e₃ G₂ + t₂ G₁ - q₁
  let g4p := Nat.add (Nat.add (Nat.mul n4 g3p) (Nat.mul e3 g2m)) (Nat.mul t2 g1p)
  let g4m := Nat.add (Nat.add (Nat.add (Nat.mul n4 g3m) (Nat.mul e3 g2p)) (Nat.mul t2 g1m)) q1
  -- G₅ = n₅ G₄ - e₄ G₃ + t₃ G₂ - q₂ G₁ + p₁
  let g5p := Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul n5 g4p) (Nat.mul e4 g3m))
    (Nat.mul t3 g2p)) (Nat.mul q2 g1m)) p1
  let g5m := Nat.add (Nat.add (Nat.add (Nat.mul n5 g4m) (Nat.mul e4 g3p)) (Nat.mul t3 g2m))
    (Nat.mul q2 g1p)
  -- G₆ = n₆ G₅ - e₅ G₄ + t₄ G₃ - q₃ G₂ + p₂ G₁ - x
  let g6p := Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul n6 g5p) (Nat.mul e5 g4m))
    (Nat.mul t4 g3p)) (Nat.mul q3 g2m)) (Nat.mul p2 g1p)
  let g6m := Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul n6 g5m) (Nat.mul e5 g4p))
    (Nat.mul t4 g3m)) (Nat.mul q3 g2p)) (Nat.mul p2 g1m)) x
  (g6p, g6m)

theorem dpG_eq (n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 : ℕ) :
    ((dpG n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5).1 : ℤ) - (dpG n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5).2
      = N6g n1 n2 n3 n4 n5 n6 e1 e2 e3 e4 e5 := by
  rw [← N6gPM_eq]
  simp only [dpG, N6gP, N6gM, minR_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
  push_cast
  ring

/-! ### Bit masks of pins -/

instance : Inhabited BPin6 := ⟨⟨BBlk6.none, [], 0⟩⟩

/-- Bit `a` of `S`. -/
def tb (S a : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight S a) 1) 1

theorem tb_eq (S a : ℕ) : tb S a = S.testBit a := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  unfold tb
  have e : Nat.land (Nat.shiftRight S a) 1 = S / 2 ^ a % 2 := by
    show (S >>> a) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [e]
  by_cases h : S / 2 ^ a % 2 = 1
  · rw [h]; simp
  · simp only [h, decide_false]
    cases hb : Nat.beq (S / 2 ^ a % 2) 1
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) h

/-- The mask of the pins satisfying `f`: bit `i` for pin `i`. -/
def maskOf (f : BPin6 → Bool) : List BPin6 → ℕ
  | [] => 0
  | q :: P => cond (f q) 1 0 + 2 * maskOf f P

theorem testBit_maskOf (f : BPin6 → Bool) : ∀ (P : List BPin6) (i : ℕ),
    (maskOf f P).testBit i = (i < P.length && f (P.getD i default))
  | [], i => by simp [maskOf]
  | q :: P, 0 => by
    simp only [maskOf, List.length_cons, List.getD_cons_zero]
    cases f q <;> simp [Nat.testBit_zero]
  | q :: P, i + 1 => by
    simp only [maskOf, List.length_cons, List.getD_cons_succ]
    rw [Nat.testBit_succ, show (cond (f q) 1 0 + 2 * maskOf f P) / 2 = maskOf f P by
      cases f q <;> simp <;> omega, testBit_maskOf f P i]
    simp

/-! ### Trees of denominators -/

abbrev D1 := ℕ × ℕ
abbrev D2 := D1 × D1
abbrev D3 := D2 × D2
abbrev D4 := D3 × D3
abbrev D5 := D4 × D4
abbrev D6 := D5 × D5

/-- Choose the half of the bonus `h`. -/
def sel {α : Type} (h : ℕ) (t : α × α) : α := cond (Nat.beq h 1) t.2 t.1

/-- The entry of a tree at the bonuses `h₁ … h₆`. -/
def look (t : D6) (h1 h2 h3 h4 h5 h6 : ℕ) : ℕ :=
  sel h6 (sel h5 (sel h4 (sel h3 (sel h2 (sel h1 t)))))

/-- A tree lists the entries of `L`. -/
def treeOK (t : D6) (L : List ℕ) : Bool :=
  (List.range 64).all fun i =>
    look t (i / 32 % 2) (i / 16 % 2) (i / 8 % 2) (i / 4 % 2) (i / 2 % 2) (i % 2) == L.getD i 0

theorem look_eq {t : D6} {L : List ℕ} (h : treeOK t L = true) {h1 h2 h3 h4 h5 h6 : ℕ}
    (g1 : h1 < 2) (g2 : h2 < 2) (g3 : h3 < 2) (g4 : h4 < 2) (g5 : h5 < 2) (g6 : h6 < 2) :
    look t h1 h2 h3 h4 h5 h6 = L.getD (nidx (5 + h1) (5 + h2) (5 + h3) (5 + h4) (5 + h5) (5 + h6)) 0 := by
  have hi : nidx (5 + h1) (5 + h2) (5 + h3) (5 + h4) (5 + h5) (5 + h6)
      = 32 * h1 + 16 * h2 + 8 * h3 + 4 * h4 + 2 * h5 + h6 := by unfold nidx; omega
  have := List.all_eq_true.mp h (32 * h1 + 16 * h2 + 8 * h3 + 4 * h4 + 2 * h5 + h6)
    (List.mem_range.mpr (by omega))
  rw [beq_iff_eq] at this
  rw [hi, ← this]
  congr 1 <;> omega

/-! ### Row masks -/

/-- The row masks of the pins: row `r`, code `c`. -/
def rowTable (P : List BPin6) : List (List ℕ) :=
  (List.range 6).map fun r => (List.range 5).map fun c => maskOf (fun q => rowOKp q r c) P

theorem rowTable_getD (P : List BPin6) {r c : ℕ} (hr : r < 6) (hc : c < 5) :
    getR ((rowTable P).getD r []) c = maskOf (fun q => rowOKp q r c) P := by
  rw [getR_eq]
  unfold rowTable
  have e1 : ((List.range 6).map fun r => (List.range 5).map fun c =>
      maskOf (fun q => rowOKp q r c) P).getD r [] = (List.range 5).map fun c =>
        maskOf (fun q => rowOKp q r c) P := by
    rw [List.getD_eq_getElem _ _ (by simp [hr])]; simp
  rw [e1, List.getD_eq_getElem _ _ (by simp [hc])]
  simp

theorem fired_filter (c p : T6) : ∀ P : List BPin6,
    fired P c p = ((P.filter fun q => q.evc c p).map BPin6.lam).sum
  | [] => rfl
  | q :: P => by
    have ih := fired_filter c p P
    unfold fired at ih ⊢
    simp only [List.map_cons, List.sum_cons, List.filter_cons]
    rw [ih]
    cases q.evc c p <;> simp

/-! ### Pins summed at their last row -/

/-- One more than the last row a pin's conditions read (`0` if none). -/
def lastOf (q : BPin6) : ℕ := (pconds q).foldr (fun rk acc => max (rk.1 + 1) acc) 0

theorem lt_lastOf {q : BPin6} {rk : ℕ × ℕ} (h : rk ∈ pconds q) : rk.1 < lastOf q := by
  unfold lastOf
  generalize pconds q = L at h
  induction L with
  | nil => exact absurd h List.not_mem_nil
  | cons x L ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
    · exact lt_of_lt_of_le (ih h) (le_max_right _ _)

theorem lastOf_le {q : BPin6} (hq : q.okb = true) : lastOf q ≤ 6 := by
  have hc := pconds_ok hq
  unfold lastOf
  generalize pconds q = L at hc
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.foldr_cons]
    have := hc x List.mem_cons_self
    exact max_le (by omega) (ih fun rk h => hc rk (List.mem_cons_of_mem _ h))

theorem rowOKp_of_last {q : BPin6} {r : ℕ} (hr : lastOf q ≤ r) (c : ℕ) : rowOKp q r c = true := by
  unfold rowOKp
  rw [List.all_eq_true]
  intro rk hrk
  have := lt_lastOf hrk
  have hne : Nat.beq rk.1 r = false := by
    rw [Bool.eq_false_iff]; intro h; have := Nat.eq_of_beq_eq_true h; omega
  simp [hne]

/-- The pins of last row `j`: their indices and multipliers. -/
def lastLists (P : List BPin6) : List (List (ℕ × ℕ)) :=
  (List.range 7).map fun j => ((List.range P.length).filter (fun i => lastOf (P.getD i default) == j)).map
    fun i => (i, (P.getD i default).lam)

/-- The multipliers of the listed pins whose bits are set. -/
def fmS (m : ℕ) (L : List (ℕ × ℕ)) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun x _ acc => Nat.add (cond (tb m x.1) x.2 0) acc) L

theorem fmS_map (m : ℕ) (g : ℕ → ℕ) : ∀ S : List ℕ,
    fmS m (S.map fun i => (i, g i)) = (S.map fun i => if m.testBit i then g i else 0).sum
  | [] => rfl
  | i :: S => by
    show Nat.add (cond (tb m i) (g i) 0) (fmS m (S.map fun i => (i, g i))) = _
    rw [fmS_map m g S, tb_eq]
    simp only [List.map_cons, List.sum_cons, Nat.add_eq]
    cases m.testBit i <;> rfl

theorem sum_range_ite (a v : ℕ) : ∀ {N : ℕ}, a < N →
    ((List.range N).map fun j => if a = j then v else 0).sum = v
  | 0, h => absurd h (Nat.not_lt_zero _)
  | N + 1, h => by
    rw [List.range_succ, List.map_append, List.sum_append]
    rcases Nat.lt_or_ge a N with h' | h'
    · rw [sum_range_ite a v h']
      have : a ≠ N := by omega
      simp [this]
    · have ha : a = N := by omega
      have e : ((List.range N).map fun j => if a = j then v else 0).sum = 0 := by
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
        have := List.mem_range.mp hj
        simp only [ite_eq_right_iff]; intro e; omega
      subst ha
      simp [e]

theorem sum_partition {α : Type*} (k : α → ℕ) (g : α → ℕ) {N : ℕ} : ∀ L : List α,
    (∀ x ∈ L, k x < N) →
    ((List.range N).map fun j => ((L.filter fun x => k x == j).map g).sum).sum = (L.map g).sum
  | [], _ => by simp
  | x :: L, h => by
    have ih := sum_partition k g L (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hx := h x List.mem_cons_self
    simp only [List.filter_cons, List.map_cons, List.sum_cons]
    have e : ((List.range N).map fun j => ((if (k x == j) = true then x :: L.filter (fun x => k x == j)
        else L.filter fun x => k x == j).map g).sum)
        = ((List.range N).map fun j => (if k x = j then g x else 0)
          + ((L.filter fun x => k x == j).map g).sum) := by
      apply List.map_congr_left
      intro j _
      by_cases hj : k x = j
      · simp [hj]
      · simp [hj]
    rw [e, List.sum_map_add, ih, sum_range_ite _ _ hx]

theorem sum_filter_range (f : BPin6 → Bool) : ∀ P : List BPin6,
    ((P.filter f).map BPin6.lam).sum
      = ((List.range P.length).map fun i => if f (P.getD i default) then (P.getD i default).lam
          else 0).sum
  | [] => rfl
  | q :: P => by
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons,
      List.filter_cons]
    have ih := sum_filter_range f P
    have e : ((List.range P.length).map ((fun i => if f ((q :: P).getD i default) = true then
        ((q :: P).getD i default).lam else 0) ∘ Nat.succ))
        = (List.range P.length).map (fun i => if f (P.getD i default) then (P.getD i default).lam
          else 0) := by
      apply List.map_congr_left; intro i _; simp [Function.comp, List.getD_cons_succ]
    rw [e, ← ih]
    simp only [List.getD_cons_zero]
    cases f q <;> simp

theorem lastLists_getD (P : List BPin6) {j : ℕ} (hj : j < 7) :
    (lastLists P).getD j [] = ((List.range P.length).filter (fun i => lastOf (P.getD i default) == j)).map
      fun i => (i, (P.getD i default).lam) := by
  unfold lastLists
  rw [List.getD_eq_getElem _ _ (by simp [hj])]
  simp

/-! ### The enumeration with the pins summed at their last row -/

def ew6 (B DK m5 : ℕ) (R5 lams L6 : List ℕ) (Q6 : List (ℕ × ℕ)) (t : D1) (msk F c5 n5 e4 t3 q2 p1
    g5p g5m g4p g4m g3p g3m g2p g2m g1p : ℕ) : Bool :=
  all5k fun c6 => !(Nat.beq (kXr c6) 0 && pairR m5 c5 c6) ||
    fN (Nat.add 5 (kHr c6)) fun n6 => fN (eR m5 c5 c6) fun e5 =>
    fN (Nat.sub (Nat.add e4 e5) n5) fun t4 => fN (minR t3 t4) fun q3 =>
    fN (Nat.sub (Nat.add q2 q3) t3) fun p2 => fN (minR p1 p2) fun x =>
    fN (Nat.add F (fmS (Nat.land msk (getR R5 c6)) Q6)) fun F6 =>
    Nat.ble (Nat.add (Nat.mul (Nat.sub DK F6) (sel (kHr c6) t))
      (Nat.mul B (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul n6 g5m) (Nat.mul e5 g4p))
        (Nat.mul t4 g3m)) (Nat.mul q3 g2p)) (Nat.mul p2 0)) x)))
      (Nat.mul B (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul n6 g5p) (Nat.mul e5 g4m))
        (Nat.mul t4 g3p)) (Nat.mul q3 g2m)) (Nat.mul p2 g1p)))

def ew5 (B DK m4 m5 : ℕ) (R4 R5 lams L6 : List ℕ) (Q5 Q6 : List (ℕ × ℕ)) (t : D2) (msk F c4 n4
    e3 t2 q1 g4p g4m g3p g3m g2p g2m g1p : ℕ) : Bool :=
  all5k fun c5 => !(pairR m4 c4 c5) ||
    fN (Nat.add 5 (kHr c5)) fun n5 => fN (eR m4 c4 c5) fun e4 =>
    fN (Nat.sub (Nat.add e3 e4) n4) fun t3 => fN (minR t2 t3) fun q2 =>
    fN (Nat.sub (Nat.add q1 q2) t2) fun p1 =>
    fN (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul n5 g4p) (Nat.mul e4 g3m)) (Nat.mul t3 g2p))
      (Nat.mul q2 0)) p1) fun g5p =>
    fN (Nat.add (Nat.add (Nat.add (Nat.mul n5 g4m) (Nat.mul e4 g3p)) (Nat.mul t3 g2m))
      (Nat.mul q2 g1p)) fun g5m =>
    fN (Nat.land msk (getR R4 c5)) fun mk => fN (Nat.add F (fmS mk Q5)) fun F5 =>
    ew6 B DK m5 R5 lams L6 Q6 (sel (kHr c5) t) mk F5 c5 n5 e4 t3 q2 p1 g5p g5m g4p g4m g3p g3m g2p
      g2m g1p

def ew4 (B DK m3 m4 m5 : ℕ) (R3 R4 R5 lams L6 : List ℕ) (Q4 Q5 Q6 : List (ℕ × ℕ)) (t : D3)
    (msk F c3 n3 e2 t1 g3p g3m g2p g2m g1p : ℕ) : Bool :=
  all5k fun c4 => !(pairR m3 c3 c4) ||
    fN (Nat.add 5 (kHr c4)) fun n4 => fN (eR m3 c3 c4) fun e3 =>
    fN (Nat.sub (Nat.add e2 e3) n3) fun t2 => fN (minR t1 t2) fun q1 =>
    fN (Nat.add (Nat.add (Nat.mul n4 g3p) (Nat.mul e3 g2m)) (Nat.mul t2 g1p)) fun g4p =>
    fN (Nat.add (Nat.add (Nat.add (Nat.mul n4 g3m) (Nat.mul e3 g2p)) (Nat.mul t2 0)) q1) fun g4m =>
    fN (Nat.land msk (getR R3 c4)) fun mk => fN (Nat.add F (fmS mk Q4)) fun F4 =>
    ew5 B DK m4 m5 R4 R5 lams L6 Q5 Q6 (sel (kHr c4) t) mk F4 c4 n4 e3 t2 q1 g4p g4m g3p g3m g2p
      g2m g1p

def ew3 (B DK m2 m3 m4 m5 : ℕ) (R2 R3 R4 R5 lams L6 : List ℕ) (Q3 Q4 Q5 Q6 : List (ℕ × ℕ))
    (t : D4) (msk F c2 n2 e1 g2p g2m g1p : ℕ) : Bool :=
  all5k fun c3 => !(pairR m2 c2 c3) ||
    fN (Nat.add 5 (kHr c3)) fun n3 => fN (eR m2 c2 c3) fun e2 =>
    fN (Nat.sub (Nat.add e1 e2) n2) fun t1 =>
    fN (Nat.add (Nat.add (Nat.mul n3 g2p) (Nat.mul e2 0)) t1) fun g3p =>
    fN (Nat.add (Nat.mul n3 g2m) (Nat.mul e2 g1p)) fun g3m =>
    fN (Nat.land msk (getR R2 c3)) fun mk => fN (Nat.add F (fmS mk Q3)) fun F3 =>
    ew4 B DK m3 m4 m5 R3 R4 R5 lams L6 Q4 Q5 Q6 (sel (kHr c3) t) mk F3 c3 n3 e2 t1 g3p g3m g2p g2m
      g1p

def ew2 (B DK m1 m2 m3 m4 m5 : ℕ) (R1 R2 R3 R4 R5 lams L6 : List ℕ)
    (Q2 Q3 Q4 Q5 Q6 : List (ℕ × ℕ)) (t : D5) (msk F c1 n1 : ℕ) : Bool :=
  all5k fun c2 => !(pairR m1 c1 c2) ||
    fN (Nat.add 5 (kHr c2)) fun n2 => fN (eR m1 c1 c2) fun e1 =>
    fN (Nat.add (Nat.mul n2 n1) 0) fun g2p => fN (Nat.add (Nat.mul n2 0) e1) fun g2m =>
    fN (Nat.land msk (getR R1 c2)) fun mk => fN (Nat.add F (fmS mk Q2)) fun F2 =>
    ew3 B DK m2 m3 m4 m5 R2 R3 R4 R5 lams L6 Q3 Q4 Q5 Q6 (sel (kHr c2) t) mk F2 c2 n2 e1 g2p g2m n1

def ew1 (B DK m1 m2 m3 m4 m5 : ℕ) (R0 R1 R2 R3 R4 R5 lams L6 : List ℕ)
    (Q1 Q2 Q3 Q4 Q5 Q6 : List (ℕ × ℕ)) (t : D6) (msk F : ℕ) : Bool :=
  all5k fun c1 => !(Nat.beq (kMr c1) 0) ||
    fN (Nat.add 5 (kHr c1)) fun n1 => fN (Nat.land msk (getR R0 c1)) fun mk =>
    fN (Nat.add F (fmS mk Q1)) fun F1 =>
    ew2 B DK m1 m2 m3 m4 m5 R1 R2 R3 R4 R5 lams L6 Q2 Q3 Q4 Q5 Q6 (sel (kHr c1) t) mk F1 c1 n1

/-- **The fast certificate check**, the pins summed at their last row (`Qs = lastLists`). -/
def chkW (m1 m2 m3 m4 m5 D K : ℕ) (t : D6) (Rs : List (List ℕ)) (Qs : List (List (ℕ × ℕ)))
    (init : ℕ) : Bool :=
  fN (Nat.mul D 1000000000000) fun B => fN (Nat.add D K) fun DK => fN init fun msk =>
  fN (fmS msk (Qs.getD 0 [])) fun F =>
    ew1 B DK m1 m2 m3 m4 m5 (Rs.getD 0 []) (Rs.getD 1 []) (Rs.getD 2 []) (Rs.getD 3 [])
      (Rs.getD 4 []) (Rs.getD 5 []) [] [] (Qs.getD 1 []) (Qs.getD 2 []) (Qs.getD 3 [])
      (Qs.getD 4 []) (Qs.getD 5 []) (Qs.getD 6 []) t msk F

/-- The masks after the rows `0, …, j-1`. -/
def maskAfter (P : List BPin6) (p c : T6) : ℕ → ℕ
  | 0 => maskOf (fun q => eqOKp q p) P
  | j + 1 => Nat.land (maskAfter P p c j) (maskOf (fun q => rowOKp q j (rowAt j c)) P)

theorem testBit_maskAfter (P : List BPin6) (p c : T6) (i : ℕ) : ∀ j,
    (maskAfter P p c j).testBit i = (decide (i < P.length) && eqOKp (P.getD i default) p &&
      (List.range j).all fun r => rowOKp (P.getD i default) r (rowAt r c))
  | 0 => by simp [maskAfter, testBit_maskOf]
  | j + 1 => by
    rw [maskAfter, show ∀ a b : ℕ, Nat.land a b = a &&& b from fun _ _ => rfl, Nat.testBit_and,
      testBit_maskAfter P p c i j, testBit_maskOf, List.range_succ, List.all_append]
    cases decide (i < P.length) <;> simp [Bool.and_assoc]

theorem all_range_stable (f : ℕ → Bool) {j : ℕ} (hf : ∀ r, j ≤ r → f r = true) :
    ∀ n, j ≤ n → (List.range n).all f = (List.range j).all f
  | 0, h => by rw [show j = 0 by omega]
  | n + 1, h => by
    rcases Nat.eq_or_lt_of_le h with e | h'
    · rw [e]
    · rw [List.range_succ, List.all_append, all_range_stable f hf n (by omega)]
      simp [hf n (by omega)]

/-- **The pins summed at their last row are the fired multipliers.** -/
theorem sum_last_eq {P : List BPin6} (hP : P.all BPin6.okb = true) (p c : T6) (hc : codes5 c) :
    ((List.range 7).map fun j => fmS (maskAfter P p c j) ((lastLists P).getD j [])).sum
      = fired P c p := by
  have hq : ∀ i < P.length, (P.getD i default).okb = true := by
    intro i hi
    rw [List.getD_eq_getElem _ _ hi]; exact List.all_eq_true.mp hP _ (List.getElem_mem hi)
  -- every pin at its last row sees the final mask
  have hstab : ∀ j < 7, ∀ i < P.length, lastOf (P.getD i default) = j →
      (maskAfter P p c j).testBit i = (maskAfter P p c 6).testBit i := by
    intro j hj i hi hl
    have hle := lastOf_le (hq i hi)
    have hall : ∀ r, j ≤ r → rowOKp (P.getD i default) r (rowAt r c) = true :=
      fun r hr => rowOKp_of_last (by omega) _
    rw [testBit_maskAfter, testBit_maskAfter,
      all_range_stable (fun r => rowOKp (P.getD i default) r (rowAt r c)) hall 6 (by omega)]
  have e1 : ((List.range 7).map fun j => fmS (maskAfter P p c j) ((lastLists P).getD j [])).sum
      = ((List.range 7).map fun j => (((List.range P.length).filter
          (fun i => lastOf (P.getD i default) == j)).map fun i =>
            if (maskAfter P p c 6).testBit i then (P.getD i default).lam else 0).sum).sum := by
    congr 1
    apply List.map_congr_left
    intro j hj
    have hj' := List.mem_range.mp hj
    rw [lastLists_getD P hj', fmS_map]
    congr 1
    apply List.map_congr_left
    intro i hi
    obtain ⟨hi1, hi2⟩ := List.mem_filter.mp hi
    rw [hstab j hj' i (List.mem_range.mp hi1) (by simpa using hi2)]
  rw [e1, sum_partition (fun i => lastOf (P.getD i default))
    (fun i => if (maskAfter P p c 6).testBit i then (P.getD i default).lam else 0)
    (List.range P.length) (fun i hi => by have := lastOf_le (hq i (List.mem_range.mp hi)); omega),
    fired_filter, sum_filter_range]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  congr 1
  rw [testBit_maskAfter, evc_split]
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := hc
  rw [← rows_all c _ (pconds_ok (hq i hi'))]
  simp only [rowOKp, List.range_succ, List.range_zero, List.nil_append, List.all_append,
    List.all_cons, List.all_nil, rowAt, Bool.and_true, decide_eq_true hi', Bool.true_and]
  cases eqOKp (P.getD i default) p <;>
    cases (pconds (P.getD i default)).all (fun rk => !(Nat.beq rk.1 5) || evk rk.2 (r6 c)) <;>
    cases (pconds (P.getD i default)).all (fun rk => !(Nat.beq rk.1 4) || evk rk.2 (r5 c)) <;>
    cases (pconds (P.getD i default)).all (fun rk => !(Nat.beq rk.1 3) || evk rk.2 (r4 c)) <;>
    cases (pconds (P.getD i default)).all (fun rk => !(Nat.beq rk.1 2) || evk rk.2 (r3 c)) <;>
    cases (pconds (P.getD i default)).all (fun rk => !(Nat.beq rk.1 1) || evk rk.2 (r2 c)) <;>
    cases (pconds (P.getD i default)).all (fun rk => !(Nat.beq rk.1 0) || evk rk.2 (r1 c)) <;> rfl

theorem chkW_spec {m1 m2 m3 m4 m5 D K : ℕ} {t : D6} {den : List ℕ} {P : List BPin6} {p : T6}
    (hP : P.all BPin6.okb = true) (ht : treeOK t den = true)
    (h : chkW m1 m2 m3 m4 m5 D K t (rowTable P) (lastLists P)
      (maskOf (fun q => eqOKp q p) P) = true) {c : T6}
    (hc : codes5 c) (hv : bvalid6 m1 m2 m3 m4 m5 c) :
    (D + K - fired P c p) * den.getD (nidx (5 + kH (r1 c)) (5 + kH (r2 c)) (5 + kH (r3 c))
        (5 + kH (r4 c)) (5 + kH (r5 c)) (5 + kH (r6 c))) 0
      + D * 1000000000000 * N6gM (5 + kH (r1 c)) (5 + kH (r2 c)) (5 + kH (r3 c))
        (5 + kH (r4 c)) (5 + kH (r5 c)) (5 + kH (r6 c)) (eR m1 (r1 c) (r2 c))
        (eR m2 (r2 c) (r3 c)) (eR m3 (r3 c) (r4 c)) (eR m4 (r4 c) (r5 c)) (eR m5 (r5 c) (r6 c))
      ≤ D * 1000000000000 * N6gP (5 + kH (r1 c)) (5 + kH (r2 c)) (5 + kH (r3 c))
        (5 + kH (r4 c)) (5 + kH (r5 c)) (5 + kH (r6 c)) (eR m1 (r1 c) (r2 c))
        (eR m2 (r2 c) (r3 c)) (eR m3 (r3 c) (r4 c)) (eR m4 (r4 c) (r5 c)) (eR m5 (r5 c) (r6 c)) := by
  have hc' := hc
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := hc
  obtain ⟨v1, v6, p1, p2, p3, p4, p5⟩ := hv
  have g1 : Nat.beq (kMr (r1 c)) 0 = true := by rw [kMr_eq, v1]; rfl
  have g6 : (Nat.beq (kXr (r6 c)) 0 && pairR m5 (r5 c) (r6 c)) = true := by
    rw [kXr_eq, v6, p5]; rfl
  unfold chkW at h
  rw [fN_eq, fN_eq, fN_eq, fN_eq] at h
  unfold ew1 at h
  have k1 := all5k_spec h l1
  rw [g1, Bool.not_true, Bool.false_or, fN_eq, fN_eq, fN_eq] at k1
  unfold ew2 at k1
  have k2 := all5k_spec k1 l2
  rw [p1, Bool.not_true, Bool.false_or, fN_eq, fN_eq, fN_eq, fN_eq, fN_eq, fN_eq] at k2
  unfold ew3 at k2
  have k3 := all5k_spec k2 l3
  rw [p2, Bool.not_true, Bool.false_or, fN_eq, fN_eq, fN_eq, fN_eq, fN_eq, fN_eq, fN_eq] at k3
  unfold ew4 at k3
  have k4 := all5k_spec k3 l4
  rw [p3, Bool.not_true, Bool.false_or, fN_eq, fN_eq, fN_eq, fN_eq, fN_eq, fN_eq, fN_eq,
    fN_eq] at k4
  unfold ew5 at k4
  have k5 := all5k_spec k4 l5
  rw [p4, Bool.not_true, Bool.false_or, fN_eq, fN_eq, fN_eq, fN_eq, fN_eq, fN_eq, fN_eq,
    fN_eq, fN_eq] at k5
  unfold ew6 at k5
  have k6 := all5k_spec k5 l6
  rw [g6, Bool.not_true, Bool.false_or, fN_eq, fN_eq, fN_eq, fN_eq, fN_eq, fN_eq, fN_eq] at k6
  -- the pins
  rw [rowTable_getD P (by norm_num) l1, rowTable_getD P (by norm_num) l2,
    rowTable_getD P (by norm_num) l3, rowTable_getD P (by norm_num) l4,
    rowTable_getD P (by norm_num) l5, rowTable_getD P (by norm_num) l6] at k6
  have hsum := sum_last_eq hP p c hc'
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, maskAfter, rowAt] at hsum
  have hF : Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add
      (fmS (maskOf (fun q => eqOKp q p) P) ((lastLists P).getD 0 []))
      (fmS (Nat.land (maskOf (fun q => eqOKp q p) P) (maskOf (fun q => rowOKp q 0 (r1 c)) P))
        ((lastLists P).getD 1 [])))
      (fmS (Nat.land (Nat.land (maskOf (fun q => eqOKp q p) P) (maskOf (fun q => rowOKp q 0 (r1 c)) P))
        (maskOf (fun q => rowOKp q 1 (r2 c)) P)) ((lastLists P).getD 2 [])))
      (fmS (Nat.land (Nat.land (Nat.land (maskOf (fun q => eqOKp q p) P)
        (maskOf (fun q => rowOKp q 0 (r1 c)) P)) (maskOf (fun q => rowOKp q 1 (r2 c)) P))
        (maskOf (fun q => rowOKp q 2 (r3 c)) P)) ((lastLists P).getD 3 [])))
      (fmS (Nat.land (Nat.land (Nat.land (Nat.land (maskOf (fun q => eqOKp q p) P)
        (maskOf (fun q => rowOKp q 0 (r1 c)) P)) (maskOf (fun q => rowOKp q 1 (r2 c)) P))
        (maskOf (fun q => rowOKp q 2 (r3 c)) P)) (maskOf (fun q => rowOKp q 3 (r4 c)) P))
        ((lastLists P).getD 4 [])))
      (fmS (Nat.land (Nat.land (Nat.land (Nat.land (Nat.land (maskOf (fun q => eqOKp q p) P)
        (maskOf (fun q => rowOKp q 0 (r1 c)) P)) (maskOf (fun q => rowOKp q 1 (r2 c)) P))
        (maskOf (fun q => rowOKp q 2 (r3 c)) P)) (maskOf (fun q => rowOKp q 3 (r4 c)) P))
        (maskOf (fun q => rowOKp q 4 (r5 c)) P)) ((lastLists P).getD 5 [])))
      (fmS (Nat.land (Nat.land (Nat.land (Nat.land (Nat.land (Nat.land
        (maskOf (fun q => eqOKp q p) P)
        (maskOf (fun q => rowOKp q 0 (r1 c)) P)) (maskOf (fun q => rowOKp q 1 (r2 c)) P))
        (maskOf (fun q => rowOKp q 2 (r3 c)) P)) (maskOf (fun q => rowOKp q 3 (r4 c)) P))
        (maskOf (fun q => rowOKp q 4 (r5 c)) P)) (maskOf (fun q => rowOKp q 5 (r6 c)) P))
        ((lastLists P).getD 6 [])) = fired P c p := by
    rw [← hsum]; simp only [Nat.add_eq]; ring
  rw [hF] at k6
  -- the denominator
  have hk : ∀ x, kHr x < 2 := fun x => by unfold kHr; cases Nat.beq x 0 <;> simp
  have hd := look_eq ht (hk (r1 c)) (hk (r2 c)) (hk (r3 c)) (hk (r4 c)) (hk (r5 c)) (hk (r6 c))
  unfold look at hd
  rw [hd] at k6
  simp only [kHr_eq] at k6
  -- the count
  have hG := dpG_eq (5 + kH (r1 c)) (5 + kH (r2 c)) (5 + kH (r3 c)) (5 + kH (r4 c))
    (5 + kH (r5 c)) (5 + kH (r6 c)) (eR m1 (r1 c) (r2 c)) (eR m2 (r2 c) (r3 c))
    (eR m3 (r3 c) (r4 c)) (eR m4 (r4 c) (r5 c)) (eR m5 (r5 c) (r6 c))
  rw [← N6gPM_eq] at hG
  rw [ble_eq_decide, decide_eq_true_eq] at k6
  simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at k6
  simp only [dpG, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at hG
  set A := (D + K - fired P c p) * den.getD (nidx (5 + kH (r1 c)) (5 + kH (r2 c)) (5 + kH (r3 c))
    (5 + kH (r4 c)) (5 + kH (r5 c)) (5 + kH (r6 c))) 0
  generalize N6gP (5 + kH (r1 c)) (5 + kH (r2 c)) (5 + kH (r3 c)) (5 + kH (r4 c))
    (5 + kH (r5 c)) (5 + kH (r6 c)) (eR m1 (r1 c) (r2 c)) (eR m2 (r2 c) (r3 c))
    (eR m3 (r3 c) (r4 c)) (eR m4 (r4 c) (r5 c)) (eR m5 (r5 c) (r6 c)) = NP at hG ⊢
  generalize N6gM (5 + kH (r1 c)) (5 + kH (r2 c)) (5 + kH (r3 c)) (5 + kH (r4 c))
    (5 + kH (r5 c)) (5 + kH (r6 c)) (eR m1 (r1 c) (r2 c)) (eR m2 (r2 c) (r3 c))
    (eR m3 (r3 c) (r4 c)) (eR m4 (r4 c) (r5 c)) (eR m5 (r5 c) (r6 c)) = NM' at hG ⊢
  have key : ∀ {GP GM : ℕ}, (GP : ℤ) - GM = (NP : ℤ) - NM' →
      A + D * 1000000000000 * GM ≤ D * 1000000000000 * GP →
      A + D * 1000000000000 * NM' ≤ D * 1000000000000 * NP := by
    intro GP GM e hle
    have : ((A + D * 1000000000000 * GM : ℕ) : ℤ) ≤ ((D * 1000000000000 * GP : ℕ) : ℤ) := by
      exact_mod_cast hle
    push_cast at this
    have h2 : (D : ℤ) * 1000000000000 * GP - D * 1000000000000 * GM
        = D * 1000000000000 * NP - D * 1000000000000 * NM' := by
      rw [← mul_sub, ← mul_sub, e]
    have : ((A + D * 1000000000000 * NM' : ℕ) : ℤ) ≤ ((D * 1000000000000 * NP : ℕ) : ℤ) := by
      push_cast; linarith
    exact_mod_cast this
  exact key hG k6

end GridGen.Six
