/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.SqMultiCheck

/-!
# Squares with three loaded edges: the checker of the fifteen-face records

Core Lean only, like `Outerplanar/SqMultiCheck.lean`, so that the data modules
`Outerplanar/Sq15Data/*.lean`, which import only this file, stay small. Soundness is in
`Outerplanar/Sq15Sound.lean`.

* The classes of the fifteen-face square lemmas as `Mode`s (constants of floors, bijections,
  six-families and ball pieces; `Outerplanar/SqMultiCheck.lean`), and `modes3`.
* **Ball targets.** The ball class at the root (`IdxBallAt id`, `Outerplanar/Loaded.lean`) is the
  family of inequalities `A ^ 600 ≤ (∏_{k ≠ j} F_k) ^ 100 · F_j ^ 91 · F_c ^ 9`, one for each cell
  `j` of the root family (the off-diagonal) and each proper root cell `c`. The rows of the test
  `(j, c)` are `bRows j c`: the six family cells with weight `100` (`91` at `j`) and the cell `c`
  with weight `9` (a second row when `c` is a family cell). The test `c = j` is the hexagon bound
  and follows from two others, so it needs no record.
* A record `Cert` is `(j, c, D, k, pieces)`, checked by `certB` (= `checkR` on `bRows j c`).
  `BallData md pat tn td l`: the records `l` cover every needed test of the pattern (`covers`,
  which also asks that the root family has no equal colours) and all pass (`AllCert`).

Part of milestone M4 of `ai_research_notes/OUTERPLANAR_13_15_LEAN_PLAN.md`; the generator is
`ai_research_notes/outerplanar/t4b_m4/gen15.py`.
-/

namespace Outerplanar.SqMulti

/-! ### The classes -/

/-- No pieces of this kind. -/
def nope : Nat × Nat := (0, 1)

/-- The plain side (no marks): at least the scale on every proper cell. -/
def m1 : Mode := ⟨(1, 1), nope, nope, nope⟩

/-- `Z` (one active mark): floor `2/3`, bijections `32/27`, ball `17/16`. -/
def mZ : Mode := ⟨(2, 3), (32, 27), nope, (17, 16)⟩

/-- `W` (two active marks): floor `4/9`, bijections `17/16`, ball `17/16`. -/
def mW : Mode := ⟨(4, 9), (17, 16), nope, (17, 16)⟩

/-- `AB_f` (three active marks): floor `8/27`, ball `17/16`. -/
def mABf : Mode := ⟨(8, 27), nope, nope, (17, 16)⟩

/-- `BAH_f` (four active marks): floor `16/81`, six-families `(17/16)^6`, ball `1`. -/
def mBAHf : Mode := ⟨(16, 81), nope, (17 ^ 6, 16 ^ 6), (1, 1)⟩

/-- `B_f5` (five marks): floor `32/243`, ball `1`. -/
def mBf5 : Mode := ⟨(32, 243), nope, nope, (1, 1)⟩

/-- `B_f6` (six marks): floor `64/729`, ball `1`. -/
def mBf6 : Mode := ⟨(64, 729), nope, nope, (1, 1)⟩

/-- `H7_f` (seven marks): floor `128/2187`, six-families `D₆ ^ 6 = (17/16)^8 (56/59)^6`. -/
def mH7f : Mode := ⟨(128, 2187), nope, (17 ^ 8 * 56 ^ 6, 16 ^ 8 * 59 ^ 6), nope⟩

/-- The unit ball class `B`. -/
def mB : Mode := ⟨nope, nope, nope, (1, 1)⟩

/-- The classes of the three path edges. -/
def modes3 (a b c : Mode) (j : Nat) : Mode := if j = 0 then a else if j = 1 then b else c

/-! ### Ball targets -/

/-- The cell of the root family with index `j` (the order of `offPair`). -/
def famCell (j : Nat) : Nat := dig 4 7754529 j

/-- The weight of the family row `k` in the test with `91` at `j`. -/
def bw (j k : Nat) : Nat := if k = j then 91 else 100

/-- The rows of the ball test `(j, c)`. -/
def bRows (j c : Nat) : List (Nat × Nat × Nat) :=
  [(0, 1, bw j 0), (0, 2, bw j 1), (1, 0, bw j 2), (1, 2, bw j 3), (2, 0, bw j 4),
    (2, 1, bw j 5), (c / 3, c % 3, 9)]

/-- A ball record: `(j, c, D, k, pieces)`. -/
abbrev Cert := Nat × Nat × Nat × Nat × List (Nat × Nat × Nat × Nat)

/-- The check of a ball record. -/
def certB (md : Nat → Mode) (pat tn td : Nat) (x : Cert) : Bool :=
  checkR md pat x.2.2.1 (bRows x.1 x.2.1) x.2.2.2.1 x.2.2.2.2 tn td

/-- Every record of a list passes. -/
def AllCert (md : Nat → Mode) (pat tn td : Nat) : List Cert → Prop
  | [] => True
  | x :: l => certB md pat tn td x = true ∧ AllCert md pat tn td l

/-- The records cover every ball test of the pattern, and the root family has no equal
colours. -/
def covers (pat : Nat) (l : List Cert) : Bool :=
  allN 6 (fun j => !eqc pat 3 (famCell j)) &&
  allN 6 fun j => allN 9 fun c => eqc pat 3 c || c == famCell j ||
    l.any fun x => x.1 == j && x.2.1 == c

/-- The ball data of a pattern. -/
def BallData (md : Nat → Mode) (pat tn td : Nat) (l : List Cert) : Prop :=
  covers pat l = true ∧ AllCert md pat tn td l

end Outerplanar.SqMulti
