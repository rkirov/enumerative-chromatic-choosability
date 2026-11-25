/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Squares with three loaded edges: the certificate checker

Core Lean only (no Mathlib), so that the data modules `Outerplanar/SqMultiData/*.lean`, which
import only this file, stay small and fast. The soundness theorems are in
`Outerplanar/SqMultiSound.lean`.

The setting is the index form of a square `u x₀ x₁ v` of `Outerplanar/Square.lean`: a pattern
code `pat` (36 bits, as `patOfCode`) gives the cells of equal colours of the three path edges
(`eqc pat j c`, `j < 3`, cell `c = 3 x + y`) and of the root edge (`j = 3`). A walk is
`(a, s, t, b)`; in a row with root pair `(a, b)` it is numbered `q = 3 s + t`.

A certificate gives conditional walk laws (integer weights, total `D` per row), and splits the
law of each path edge (the *marginal*) into *pieces*, each paid for by the class of that edge:

* `(e, 0, c, v)` — a floor: weight `v` on the cell `c`;
* `(e, 1, σ, v)` — a bijection: weight `v` on each of the three cells `(x, σ x)`;
* `(e, 2, σ, v)` — a matched six-family: weight `v` on each of the six cells `(x, y)`, `y ≠ σ x`;
* `(e, 3, σ, y)` — a ball piece: the vector `y` (nine slots of `WB` bits), within total
  variation `3/200` of the uniform law on the family of `σ` (`tvOK`).

The class of an edge (`Mode`) has one constant per kind of piece; a zero numerator forbids the
kind. The checks are: legal walks, row sums, valid pieces, the marginal of every cell equal to
the sum of its pieces, and the integer Gibbs inequality

`tn ^ (N D) · ∏ k ^ (n k) · den ≤ td ^ (N D) · D ^ (N D) · num`

(`N` the total row weight; `num / den` the product of the piece constants). No logarithms.

* `checkR` — a rooted record: rows `(a, b, n)`; it gives `∏ F(a, b) ^ n ≥ (N₀ N₁ N₂ tn / td) ^ N`.
* `checkC` — a closing record: one law on all walks with a proper root pair; it gives
  `∑ F(a, b) ≥ N₀ N₁ N₂ tn / td`.

Part of milestone M0 of `ai_research_notes/OUTERPLANAR_13_15_LEAN_PLAN.md` (the generator is
`ai_research_notes/outerplanar/t4b_m0/emit_sqmulti.py`).
-/

namespace Outerplanar.SqMulti

/-- The `i`-th digit of `c` in base `2 ^ b`. -/
def dig (b c i : Nat) : Nat := (c >>> (b * i)) % 2 ^ b

/-- The `i`-th bit of `c`. -/
def bit (c i : Nat) : Bool := (c >>> i) % 2 == 1

/-- The bijections of `Fin 3`, in the order of `permutations`: `permN σ x`. -/
def permN (sg x : Nat) : Nat := dig 2 6746936868 (3 * sg + x)

/-- Slot width of packed tables and vectors. -/
def WB : Nat := 24

/-- `f 0 + ⋯ + f (n - 1)`. -/
def sumN : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => sumN n f + f n

/-- `f 0 * ⋯ * f (n - 1)`. -/
def prodN : Nat → (Nat → Nat) → Nat
  | 0, _ => 1
  | n + 1, f => prodN n f * f n

/-- `p 0 && ⋯ && p (n - 1)`. -/
def allN : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | n + 1, p => allN n p && p n

/-- The sum of a list. -/
def lsum : List Nat → Nat
  | [] => 0
  | x :: l => x + lsum l

/-- The product of a list. -/
def lprod : List Nat → Nat
  | [] => 1
  | x :: l => x * lprod l

/-- Every element of a list passes. -/
def lall {α : Type} (p : α → Bool) : List α → Bool
  | [] => true
  | x :: l => p x && lall p l

/-- The class of an edge: the constants `(num, den)` of floors, bijections, six-families and
ball pieces. -/
structure Mode where
  fl : Nat × Nat
  bij : Nat × Nat
  hx : Nat × Nat
  ball : Nat × Nat

/-- Equal colours on the cell `c` of the edge `j` (`j = 3`: the root edge). -/
def eqc (pat j c : Nat) : Bool := bit pat (9 * j + c)

/-- The walk `(a, s, t, b)` has different colours on its three path edges. -/
def legal (pat a s t b : Nat) : Bool :=
  !eqc pat 0 (3 * a + s) && !eqc pat 1 (3 * s + t) && !eqc pat 2 (3 * t + b)

/-- The cell of the edge `j` of the walk `q` of the row with root pair `(a, b)`. -/
def cellOf (j a q b : Nat) : Nat :=
  if j = 0 then 3 * a + q / 3 else if j = 1 then q else 3 * (q % 3) + b

/-- The cell `c` is on the bijection `σ`. -/
def onPerm (sg c : Nat) : Bool := c % 3 == permN sg (c / 3)

/-- The weight of the piece `p` on the cell `c` of the edge `j`. -/
def contrib (p : Nat × Nat × Nat × Nat) (j c : Nat) : Nat :=
  if p.1 = j then
    if p.2.1 = 0 then (if c = p.2.2.1 then p.2.2.2 else 0)
    else if p.2.1 = 1 then (if onPerm p.2.2.1 c then p.2.2.2 else 0)
    else if p.2.1 = 2 then (if onPerm p.2.2.1 c then 0 else p.2.2.2)
    else dig WB p.2.2.2 c
  else 0

/-- The exponent of the constant of a piece. -/
def expo (p : Nat × Nat × Nat × Nat) : Nat :=
  if p.2.1 = 3 then sumN 9 (dig WB p.2.2.2) else p.2.2.2

/-- The constant of a piece. -/
def pconst (md : Nat → Mode) (p : Nat × Nat × Nat × Nat) : Nat × Nat :=
  if p.2.1 = 0 then (md p.1).fl else if p.2.1 = 1 then (md p.1).bij
  else if p.2.1 = 2 then (md p.1).hx else (md p.1).ball

/-- `σ` extends the equal colours of the edge `e`. -/
def compatB (pat e sg : Nat) : Bool := allN 9 fun c => !eqc pat e c || onPerm sg c

/-- The total-variation test of a ball piece: `200 (Σ_fam (6 y - λ)₊ + 6 Σ_off y) ≤ 18 λ`. -/
def tvOK (sg v : Nat) : Bool :=
  200 * sumN 9 (fun c => if onPerm sg c then 6 * dig WB v c
    else 6 * dig WB v c - sumN 9 (dig WB v)) ≤ 18 * sumN 9 (dig WB v)

/-- A valid piece. -/
def pieceOK (md : Nat → Mode) (pat : Nat) (p : Nat × Nat × Nat × Nat) : Bool :=
  decide (p.1 < 3) &&
  if p.2.1 = 0 then decide (p.2.2.1 < 9) && !eqc pat p.1 p.2.2.1 &&
    decide (0 < (md p.1).fl.1) && decide (0 < (md p.1).fl.2)
  else if p.2.1 = 1 then decide (p.2.2.1 < 6) &&
    allN 3 (fun x => !eqc pat p.1 (3 * x + permN p.2.2.1 x)) &&
    decide (0 < (md p.1).bij.1) && decide (0 < (md p.1).bij.2)
  else if p.2.1 = 2 then decide (p.2.2.1 < 6) && compatB pat p.1 p.2.2.1 &&
    decide (0 < (md p.1).hx.1) && decide (0 < (md p.1).hx.2)
  else decide (p.2.1 = 3) && decide (p.2.2.1 < 6) && compatB pat p.1 p.2.2.1 &&
    allN 9 (fun c => !eqc pat p.1 c || dig WB p.2.2.2 c == 0) && tvOK p.2.2.1 p.2.2.2 &&
    decide (0 < (md p.1).ball.1) && decide (0 < (md p.1).ball.2)

/-- The numerator of the product of the piece constants. -/
def pnum (md : Nat → Mode) (ps : List (Nat × Nat × Nat × Nat)) : Nat :=
  lprod (ps.map fun p => (pconst md p).1 ^ expo p)

/-- The denominator of the product of the piece constants. -/
def pden (md : Nat → Mode) (ps : List (Nat × Nat × Nat × Nat)) : Nat :=
  lprod (ps.map fun p => (pconst md p).2 ^ expo p)

/-- The marginal of the pieces on the cell `c` of the edge `j`. -/
def pmarg (ps : List (Nat × Nat × Nat × Nat)) (j c : Nat) : Nat :=
  lsum (ps.map fun p => contrib p j c)

/-! ### Rooted records -/

/-- The root index `a` of a row. -/
def rA (rows : List (Nat × Nat × Nat)) (i : Nat) : Nat := (rows.getD i (0, 0, 0)).1

/-- The root index `b` of a row. -/
def rB (rows : List (Nat × Nat × Nat)) (i : Nat) : Nat := (rows.getD i (0, 0, 0)).2.1

/-- The weight of a row. -/
def rN (rows : List (Nat × Nat × Nat)) (i : Nat) : Nat := (rows.getD i (0, 0, 0)).2.2

/-- The walk weight `K i q`. -/
def kk (k i q : Nat) : Nat := dig WB k (9 * i + q)

/-- The marginal of the walk law on the cell `c` of the edge `j`. -/
def wmargR (rows : List (Nat × Nat × Nat)) (k j c : Nat) : Nat :=
  sumN rows.length fun i => rN rows i *
    sumN 9 fun q => if cellOf j (rA rows i) q (rB rows i) = c then kk k i q else 0

/-- The total row weight. -/
def rTot (rows : List (Nat × Nat × Nat)) : Nat := sumN rows.length (rN rows)

/-- The check of a rooted record. -/
def checkR (md : Nat → Mode) (pat D : Nat) (rows : List (Nat × Nat × Nat)) (k : Nat)
    (ps : List (Nat × Nat × Nat × Nat)) (tn td : Nat) : Bool :=
  decide (0 < D) && decide (0 < tn) && decide (0 < td) &&
  allN rows.length (fun i => decide (rA rows i < 3) && decide (rB rows i < 3) &&
    decide (0 < rN rows i) && sumN 9 (kk k i) == D &&
    allN 9 fun q => kk k i q == 0 || legal pat (rA rows i) (q / 3) (q % 3) (rB rows i)) &&
  lall (pieceOK md pat) ps &&
  allN 3 (fun j => allN 9 fun c => wmargR rows k j c == pmarg ps j c) &&
  decide (tn ^ (rTot rows * D) *
      prodN rows.length (fun i => prodN 9 fun q => kk k i q ^ (rN rows i * kk k i q)) *
      pden md ps ≤ td ^ (rTot rows * D) * D ^ (rTot rows * D) * pnum md ps)

/-- The rows of a hexagon target: the six cells off the diagonal, weight `1`. -/
def hexRows : List (Nat × Nat × Nat) :=
  [(0, 1, 1), (0, 2, 1), (1, 0, 1), (1, 2, 1), (2, 0, 1), (2, 1, 1)]

/-- The check of a record with a hexagon target. -/
def checkH (md : Nat → Mode) (pat D k : Nat) (ps : List (Nat × Nat × Nat × Nat)) (tn td : Nat) :
    Bool :=
  checkR md pat D hexRows k ps tn td

/-! ### Closing records -/

/-- The marginal of a closing law (rows `i = 3 a + b`) on the cell `c` of the edge `j`. -/
def wmargC (k j c : Nat) : Nat :=
  sumN 9 fun i => sumN 9 fun q => if cellOf j (i / 3) q (i % 3) = c then kk k i q else 0

/-- The check of a closing record. -/
def checkC (md : Nat → Mode) (pat D k : Nat) (ps : List (Nat × Nat × Nat × Nat)) (tn td : Nat) :
    Bool :=
  decide (0 < D) && decide (0 < tn) && decide (0 < td) &&
  allN 9 (fun i => allN 9 fun q => kk k i q == 0 ||
    (legal pat (i / 3) (q / 3) (q % 3) (i % 3) && !eqc pat 3 i)) &&
  sumN 9 (fun i => sumN 9 (kk k i)) == D &&
  lall (pieceOK md pat) ps &&
  allN 3 (fun j => allN 9 fun c => wmargC k j c == pmarg ps j c) &&
  decide (tn ^ D * prodN 9 (fun i => prodN 9 fun q => kk k i q ^ kk k i q) * pden md ps ≤
    td ^ D * D ^ D * pnum md ps)

/-! ### The classes of the runs -/

/-- The ball class `B`. -/
def modeB : Mode := ⟨(0, 1), (0, 1), (0, 1), (1, 1)⟩

/-- The matching class `M`. -/
def modeM : Mode := ⟨(0, 1), (1, 1), (0, 1), (0, 1)⟩

/-- The hexagon class `H`. -/
def modeH : Mode := ⟨(0, 1), (0, 1), (1, 1), (0, 1)⟩

/-- The modes of a run, from a code: digit `j` (base 4) is the class of edge `j`, `0 = B`,
`1 = M`, `2 = H`. -/
def modesOf (code j : Nat) : Mode :=
  if dig 2 code j = 0 then modeB else if dig 2 code j = 1 then modeM else modeH

end Outerplanar.SqMulti
