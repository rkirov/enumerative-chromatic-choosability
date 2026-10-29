/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.K5.Pins

/-!
# Height five at `k = 5`: the exact-certificate checker

The residual layer of `ai_research_notes/cx/h5k5/NOTE.md` §3 (Codex), checked in
`H5_K5_REVIEW_2026-10-28.md` (c). The machinery is that of `GridGen/Five/Exact5.lean` (`Ex5`):
packed Venn data, column types enumerated pattern by pattern with one atom per colour class,
reduced to touching atoms (`ratom`, the review's touching reduction), capacities. What changes:

* **The box test** becomes the cone test (`okc55`): for a type with successor orbit counts `c`,
  uniform row `u` and `e = D + K - pen`, `e · (u·F_d) ≤ D · (c·F_d)` at the five rays and the
  separable test `Σⱼ min(qLⱼ dⱼ, qUⱼ dⱼ) ≥ 0`, `dⱼ = D cⱼ - e uⱼ`, on `Q`.
* **The pins** (`XPin`) are those of `GridGen/Five/K5/Pins.lean`: a block of up to three
  consecutive rows and peels, each row condition a set of atoms (a bit mask over atom codes);
  the bounds use the atom sizes (`xbnd`). The bit-LP pins, row-atom pins (fibre or Lemma B),
  adjacent-pair blocks (alone and times one outside-row fibre), consecutive triples and
  nonadjacent equalities of the review are all of this form. On a type, a pin is evaluated
  through the reduced atoms of the class representatives (`penL`); on a non-touching class
  (reduced atom `0`) no pin fires, so the type's penalty is at most the actual one.
-/

namespace GridGen.Five.K5

open Finset GridGen.Five GridGen.Five.Ex5

/-! ### Data -/

/-- A peel of an exact pin: a row in a set of atoms, or two rows equal. -/
inductive XPeel
  | mem (r S : ℕ)
  | eq (r j : ℕ)

/-- An exact pin: a block of consecutive rows from `r0` with atom sets `bs`, peels, and the
multiplier. -/
structure XPin where
  r0 : ℕ
  bs : List ℕ
  peels : List XPeel
  lam : ℕ

/-- An exact certificate for one list shape. -/
structure XSpec where
  atoms : List (ℕ × ℕ)
  vennP : ℕ
  pins : List XPin
  K : ℕ
  D : ℕ
  pds : List (PatD × List (List (ℕ × ℕ) × ℕ))

/-- The shape as an `Ex5.Spec5` (atoms and packed Venn data only). -/
def XSpec.toSpec5 (sp : XSpec) : Spec5 := ⟨sp.atoms, sp.vennP, [], [], 0, 1, []⟩

/-! ### Forcing values -/

/-- Evaluate `x` once and pass the value on: the kernel reduces the recursor only after
evaluating its major premise to a literal, and then hands `k` a cheap expression. -/
def forceN (x : ℕ) (k : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (n + 1)) x

theorem forceN_eq (x : ℕ) (k : ℕ → Bool) : forceN x k = k x := by
  cases x <;> rfl

/-- Evaluate the eleven fields of an orbit vector once. -/
def forceC (c : C11) (k : C11 → Bool) : Bool :=
  forceN c.c0 fun a0 => forceN c.c1 fun a1 => forceN c.c2 fun a2 => forceN c.c3 fun a3 =>
  forceN c.c4 fun a4 => forceN c.c5 fun a5 => forceN c.c6 fun a6 => forceN c.c7 fun a7 =>
  forceN c.c8 fun a8 => forceN c.c9 fun a9 => forceN c.c10 fun a10 =>
    k ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩

theorem forceC_eq (c : C11) (k : C11 → Bool) : forceC c k = k c := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := c
  simp only [forceC, forceN_eq]

/-! ### The cone test -/

/-- The uniform rows at `k = 5`, by canonical pattern. -/
def urow55 (p : ℕ) : C11 :=
  match p with
  | 0 => ⟨13, 60, 30, 42, 96, 12, 60, 30, 42, 48, 36⟩
  | 1 => ⟨10, 55, 24, 40, 88, 17, 74, 23, 50, 38, 40⟩
  | 2 => ⟨10, 48, 32, 46, 100, 14, 64, 24, 36, 50, 36⟩
  | 3 => ⟨7, 40, 23, 49, 86, 23, 88, 17, 38, 36, 40⟩
  | 4 => ⟨8, 44, 25, 43, 92, 19, 79, 19, 40, 39, 42⟩
  | 5 => ⟨4, 34, 14, 46, 76, 32, 100, 16, 36, 36, 40⟩
  | 6 => ⟨7, 40, 23, 49, 86, 23, 88, 17, 38, 36, 40⟩
  | 7 => ⟨5, 37, 16, 44, 79, 25, 93, 18, 39, 39, 42⟩
  | 8 => ⟨10, 46, 24, 34, 76, 16, 72, 32, 50, 50, 40⟩
  | 9 => ⟨10, 55, 24, 40, 88, 17, 74, 23, 50, 38, 40⟩
  | 10 => ⟨7, 50, 18, 38, 80, 18, 78, 25, 53, 40, 42⟩
  | 11 => ⟨8, 38, 25, 36, 78, 18, 78, 25, 40, 53, 42⟩
  | 12 => ⟨5, 37, 16, 44, 79, 25, 93, 18, 39, 39, 42⟩
  | 13 => ⟨8, 44, 25, 43, 92, 19, 79, 19, 40, 39, 42⟩
  | _ => ⟨6, 40, 18, 40, 84, 20, 84, 20, 42, 42, 44⟩

/-- The rays, as orbit vectors. -/
def FC (k : ℕ) : C11 :=
  match k with
  | 0 => ⟨1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1⟩
  | 1 => ⟨469, 459, 460, 447, 450, 434, 437, 450, 449, 441, 440⟩
  | 2 => ⟨210205, 205329, 205902, 199452, 201027, 193112, 194687, 201150, 200564, 196847, 196262⟩
  | 3 => ⟨93875881, 91680307, 91943420, 89033797, 89748434, 86181438, 86896075, 89813338,
      89542585, 87880877, 87610712⟩
  | _ => ⟨41910174805, 40929163673, 41046972634, 39746676186, 40066233431, 38472377524,
      38791934769, 40095773898, 39974422256, 39232571727, 39111492014⟩

/-- The dot product of two orbit vectors. -/
def dot11 (a b : C11) : ℕ :=
  a.c0 * b.c0 + a.c1 * b.c1 + a.c2 * b.c2 + a.c3 * b.c3 + a.c4 * b.c4 + a.c5 * b.c5
    + a.c6 * b.c6 + a.c7 * b.c7 + a.c8 * b.c8 + a.c9 * b.c9 + a.c10 * b.c10

/-- Accumulate the separable minimum over `Q`: `(positive part, negative part)`. -/
def qterm (L U a b : ℕ) (acc : ℕ × ℕ) : ℕ × ℕ :=
  cond (Nat.ble b a) (Nat.add acc.1 (Nat.mul L (Nat.sub a b)), acc.2)
    (acc.1, Nat.add acc.2 (Nat.mul U (Nat.sub b a)))

/-- The separable accumulation over `Q`. -/
def qacc (D : ℕ) (u c : C11) (e : ℕ) : ℕ × ℕ :=
  qterm 933215 933220 (Nat.mul D c.c10) (Nat.mul e u.c10) <|
    qterm 936105 936110 (Nat.mul D c.c9) (Nat.mul e u.c9) <|
    qterm 953806 953811 (Nat.mul D c.c8) (Nat.mul e u.c8) <|
    qterm 956703 956708 (Nat.mul D c.c7) (Nat.mul e u.c7) <|
    qterm 925589 925594 (Nat.mul D c.c6) (Nat.mul e u.c6) <|
    qterm 917963 917968 (Nat.mul D c.c5) (Nat.mul e u.c5) <|
    qterm 955997 956002 (Nat.mul D c.c4) (Nat.mul e u.c4) <|
    qterm 948370 948375 (Nat.mul D c.c3) (Nat.mul e u.c3) <|
    qterm 979400 979405 (Nat.mul D c.c2) (Nat.mul e u.c2) <|
    qterm 976588 976593 (Nat.mul D c.c1) (Nat.mul e u.c1) <|
    qterm 1000000 1000000 (Nat.mul D c.c0) (Nat.mul e u.c0) (0, 0)

/-- The separable test on `Q`. -/
def qtestQ (D : ℕ) (u c : C11) (e : ℕ) : Bool :=
  Nat.ble (qacc D u c e).2 (qacc D u c e).1

/-- **The cone test of one column type**, for given successor counts `c`. -/
def okcC (D : ℕ) (u c : C11) (e : ℕ) : Bool :=
  Nat.ble (e * dot11 u (FC 0)) (D * dot11 c (FC 0)) &&
  Nat.ble (e * dot11 u (FC 1)) (D * dot11 c (FC 1)) &&
  Nat.ble (e * dot11 u (FC 2)) (D * dot11 c (FC 2)) &&
  Nat.ble (e * dot11 u (FC 3)) (D * dot11 c (FC 3)) &&
  Nat.ble (e * dot11 u (FC 4)) (D * dot11 c (FC 4)) &&
  qtestQ D u c e

/-- **The cone test of one column type**: `e · Σ uₒ wₒ ≤ D · Σ cₒ wₒ` on the cone, with the
counts and `e` evaluated once. -/
def okc55 (D : ℕ) (u : C11) (P e : ℕ) : Bool :=
  forceN P fun P' => forceN e fun e' => forceC (cls5 P') fun c => okcC D u c e'

theorem okc55_eq (D : ℕ) (u : C11) (P e : ℕ) : okc55 D u P e = okcC D u (cls5 P) e := by
  simp only [okc55, forceN_eq, forceC_eq]

/-! ### Pins on types -/

/-- The equalities of a pin hold on a pattern. -/
def eqsOK (c : T5) : List XPeel → Bool
  | [] => true
  | XPeel.eq r j :: ps => (rowAt r c == rowAt j c) && eqsOK c ps
  | XPeel.mem _ _ :: ps => eqsOK c ps

/-- The block conditions from row `r`. -/
def blkConds : ℕ → List ℕ → List (ℕ × ℕ)
  | _, [] => []
  | r, S :: Ss => (r, S) :: blkConds (r + 1) Ss

/-- The membership conditions of the peels. -/
def memConds : List XPeel → List (ℕ × ℕ)
  | [] => []
  | XPeel.mem r S :: ps => (r, S) :: memConds ps
  | XPeel.eq _ _ :: ps => memConds ps

/-- The row conditions of a pin. -/
def XPin.conds (q : XPin) : List (ℕ × ℕ) := blkConds q.r0 q.bs ++ memConds q.peels

/-- A pin compiled for a pattern: its conditions on the class representatives, and its
multiplier; `none` if its equalities fail. -/
def compileOne (c : T5) (q : XPin) : Option (List (ℕ × ℕ) × ℕ) :=
  if eqsOK c q.peels then some (q.conds.map (fun rs => (repOf c rs.1, rs.2)), q.lam) else none

/-- The compiled pins of a pattern. -/
def compileX (c : T5) (P : List XPin) : List (List (ℕ × ℕ) × ℕ) := P.filterMap (compileOne c)

/-- The penalty of a type: the multipliers of the compiled pins all of whose conditions hold on
the chosen atoms (`used`, row `4` first). -/
def penL (cps : List (List (ℕ × ℕ) × ℕ)) (used : List ℕ) : ℕ :=
  (cps.map fun cp => if cp.1.all (fun ks => ks.2.testBit (used.getD (4 - ks.1) 0)) then cp.2
    else 0).sum

/-! ### The enumeration -/

/-- **The enumeration** of the column types of a pattern, row by row (`Ex5.enumP` with the cone
test and the compiled pins at the leaves). -/
def enumX (D K : ℕ) (u : C11) (cps : List (List (ℕ × ℕ) × ℕ)) :
    List (List Ch) → ℕ → List ℕ → Bool
  | [], P, used => forceN (penL cps used) fun pen => okc55 D u P (Nat.sub (Nat.add D K) pen)
  | C :: Cs, P, used => allC (fun c => !(Nat.blt (Ex5.cnt c.1 used) c.2.1) ||
      enumX D K u cps Cs (Nat.sub P c.2.2.1) (c.1 :: used)) C

/-- **The check of one pattern**, with its compiled pins. -/
def patOkX (sp : XSpec) (pc : PatD × List (List (ℕ × ℕ) × ℕ)) : Bool :=
  pdOk sp.toSpec5 pc.1 && decide (compileX (canons.getD pc.1.p (0, 1, 0, 1, 0)) sp.pins = pc.2) &&
    enumX sp.D sp.K (urow55 pc.1.p) pc.2 pc.1.chs sp.vennP []

/-- All patterns pass. -/
def allOkX (sp : XSpec) : Bool := sp.pds.all (patOkX sp)

/-! ### The scalar conditions -/

/-- The number of colours of a set of atoms. -/
def dszX (A : List (ℕ × ℕ)) (S : ℕ) : ℕ :=
  ((List.range 32).map fun m => if S.testBit m then asz A m else 0).sum

/-- The bound of a peel. -/
def XPeel.bnd (A : List (ℕ × ℕ)) : XPeel → ℚ
  | mem r S => min (qX r * dszX A S) 1
  | eq r _ => qX r

/-- The bound of a block. -/
def blkBnd (A : List (ℕ × ℕ)) (r0 : ℕ) : List ℕ → ℚ
  | [S] => βQ5 (dszX A S) 4 (fsd r0 * fsd (4 - r0))
  | [S, S'] => βQ5 (dszX A S * dszX A S') 12 (fsd r0 * fsd (3 - r0))
  | [S, S', S''] => βQ5 (dszX A S * dszX A S' * dszX A S'') 36 (fsd r0 * fsd (2 - r0))
  | _ => 1

/-- The bound of a pin. -/
def xbnd (A : List (ℕ × ℕ)) (q : XPin) : ℚ :=
  (q.peels.map (XPeel.bnd A)).prod * blkBnd A q.r0 q.bs

/-- The row of a peel, and the rows it reads. -/
def XPeel.row : XPeel → ℕ | mem r _ => r | eq r _ => r
def XPeel.reads : XPeel → ℕ → Bool
  | mem r _, i => r == i
  | eq r j, i => r == i || j == i

/-- A peel is well formed: rows in range, no atom `0` in a set, two different rows. -/
def XPeel.okb : XPeel → Bool
  | mem r S => decide (r < 5) && !S.testBit 0
  | eq r j => decide (r < 5 ∧ j < 5 ∧ j ≠ r)

/-- The block reads row `i`. -/
def blkReads (r0 : ℕ) (bs : List ℕ) (i : ℕ) : Bool := decide (r0 ≤ i ∧ i < r0 + bs.length)

/-- The peel order. -/
def xpeelOK (r0 : ℕ) (bs : List ℕ) : List XPeel → Bool
  | [] => true
  | p :: ps => !(blkReads r0 bs p.row) && ps.all (fun g => !(g.reads p.row)) && p.okb &&
      xpeelOK r0 bs ps

/-- A pin is well formed. -/
def XPin.okb (q : XPin) : Bool :=
  decide (q.bs.length ≤ 3 ∧ q.r0 + q.bs.length ≤ 5) && q.bs.all (fun S => !S.testBit 0) &&
    xpeelOK q.r0 q.bs q.peels

/-- **The scalar conditions.** -/
def specOkX (sp : XSpec) : Bool :=
  Nat.blt 0 sp.D && Nat.beq sp.vennP (packV (vennOfAtoms sp.atoms)) && sp.pins.all XPin.okb &&
    (List.range 15).all (fun p => sp.pds.any (fun pd => Nat.beq pd.1.p p)) &&
    decide ((sp.pins.map fun q => (q.lam : ℚ) * xbnd sp.atoms q).sum ≤ sp.K)

end GridGen.Five.K5
