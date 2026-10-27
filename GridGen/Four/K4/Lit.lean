/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Lean

/-!
# Height four at `k = 4`: compact certificate literals

The generated data modules of `GridGen/Four/K4/Data/` carry large certificate terms (trees,
certificate lists, search tables). Written as ordinary Lean terms, every constructor and numeral
is elaborated separately and recorded in the info trees, and writing the module's `.ilean` then
costs as much as checking the certificate. `lit% "…"` (one term), `lits% "…"` (a list of terms)
and `natss% "…"` (a list of lists of naturals) build the same terms directly from a compact string.
They only construct terms: the kernel type-checks the result like any other term, so nothing here
is trusted.

The string is in prefix form. A letter is a constructor (table `litCon`), followed by its
arguments; a natural is its decimal digits followed by `,`; a list of naturals is `[` naturals
`]`; a value vector `V5` is ten naturals (positive and negative part of each valuation).
-/

namespace GridGen.Four.K4.Lit

open Lean Elab Term Meta

/-- The arguments of a constructor. -/
inductive Arg where
  | nat
  | nats
  | term
  | v5

/-- The constructors, by letter. -/
def litCon : Char → Option (Name × List Arg)
  -- chain trees (`Tree.lean`)
  | 'L' => some (`GridGen.Four.K4.CT.leaf, [])
  | 'P' => some (`GridGen.Four.K4.CT.prune, [])
  | 'N' => some (`GridGen.Four.K4.CT.node, [.nat, .nats, .term, .term])
  | 'G' => some (`GridGen.Four.K4.CT.given, [.nat])
  | 'E' => some (`GridGen.Four.K4.CTL.nil, [])
  | 'K' => some (`GridGen.Four.K4.CTL.cons, [.term, .term])
  -- numeric trees of general nodes (`GTree.lean`)
  | 'l' => some (`GridGen.Four.K4.GCT.leaf, [])
  | 'p' => some (`GridGen.Four.K4.GCT.prune, [])
  | 'n' => some (`GridGen.Four.K4.GCT.node, [.nat, .nats, .term, .term])
  | 'e' => some (`GridGen.Four.K4.GCTL.nil, [])
  | 'k' => some (`GridGen.Four.K4.GCTL.cons, [.term, .term])
  -- explicit-list branching trees (`GAnd.lean`)
  | 'A' => some (`GridGen.Four.K4.GAT.num, [.term])
  | 'S' => some (`GridGen.Four.K4.GAT.split, [.nat, .term])
  | 'F' => some (`GridGen.Four.K4.GAT.badF, [.nat, .nat, .nat, .nat, .nat])
  | 'M' => some (`GridGen.Four.K4.GAT.badM, [.nat, .nat, .nat, .nat, .nat])
  | 'g' => some (`GridGen.Four.K4.GAT.given, [.nat])
  | 'z' => some (`GridGen.Four.K4.GATL.nil, [])
  | 'c' => some (`GridGen.Four.K4.GATL.cons, [.term, .term])
  -- pointwise certificates (`Point.lean`)
  | 'T' => some (`GridGen.Four.K4.PC.tree, [.term])
  | 'C' => some (`GridGen.Four.K4.PC.cl, [.nat])
  | 'B' => some (`GridGen.Four.K4.PT.box, [])
  | 'X' => some (`GridGen.Four.K4.PT.exact, [])
  | 'Y' => some (`GridGen.Four.K4.PT.split, [.term])
  | 'Q' => some (`GridGen.Four.K4.PTL.nil, [])
  | 'R' => some (`GridGen.Four.K4.PTL.cons, [.term, .term])
  -- search tables (`GTree.lean`)
  | 'o' => some (`GridGen.Four.K4.KT.leaf, [])
  | 'w' => some (`GridGen.Four.K4.KT.node, [.term, .nat, .term])
  | 'u' => some (`GridGen.Four.K4.KV.leaf, [])
  | 'v' => some (`GridGen.Four.K4.KV.node, [.term, .nat, .v5, .term])
  | _ => none

/-- A natural at position `i`: its digits and an optional `,`. -/
partial def parseNat (b : ByteArray) (i : Nat) : Except String (Nat × Nat) :=
  let rec go (j acc : Nat) (seen : Bool) : Except String (Nat × Nat) :=
    if h : j < b.size then
      let c := b[j]
      if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then go (j + 1) (acc * 10 + (c.toNat - 48)) true
      else if seen then .ok (acc, if c.toNat == 44 then j + 1 else j)
      else .error s!"lit%: a natural expected at {j}"
    else if seen then .ok (acc, j) else .error s!"lit%: a natural expected at {j}"
  go i 0 false

/-- `List ℕ` from a list of terms of type `ℕ`. -/
def mkNatList (xs : List Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [levelZero]) (mkConst ``Nat) x acc)
    (mkApp (mkConst ``List.nil [levelZero]) (mkConst ``Nat))

/-- A list of naturals `[a,b,…]` at position `i` (as raw literals, or as numerals `OfNat.ofNat`
like elaborated ones). -/
partial def parseNats (b : ByteArray) (i : Nat) (raw : Bool := true) : Except String (Expr × Nat) := do
  unless i < b.size && b[i]!.toNat == 91 do throw s!"lit%: `[` expected at {i}"
  let rec go (j : Nat) (acc : Array Expr) : Except String (Expr × Nat) := do
    if j < b.size && b[j]!.toNat == 93 then return (mkNatList acc.toList, j + 1)
    let (n, j') ← parseNat b j
    go j' (acc.push (if raw then mkRawNatLit n else mkNatLit n))
  go (i + 1) #[]

/-- A term at position `i`. -/
partial def parseTerm (b : ByteArray) (i : Nat) : Except String (Expr × Nat) := do
  unless i < b.size do throw "lit%: unexpected end"
  let c := Char.ofNat b[i]!.toNat
  let some (nm, args) := litCon c | throw s!"lit%: unknown constructor `{c}` at {i}"
  let mut j := i + 1
  let mut es : Array Expr := #[]
  for a in args do
    match a with
    | .nat =>
      let (n, j') ← parseNat b j
      es := es.push (mkRawNatLit n); j := j'
    | .nats =>
      let (e, j') ← parseNats b j
      es := es.push e; j := j'
    | .term =>
      let (e, j') ← parseTerm b j
      es := es.push e; j := j'
    | .v5 =>
      let mut zs : Array Expr := #[]
      for _ in [0:5] do
        let (p, j1) ← parseNat b j
        let (q, j2) ← parseNat b j1
        zs := zs.push (mkApp2 (mkConst `GridGen.Four.K4.Zp.mk) (mkRawNatLit p) (mkRawNatLit q))
        j := j2
      es := es.push (mkAppN (mkConst `GridGen.Four.K4.V5.mk) zs)
  return (mkAppN (mkConst nm) es, j)

/-- A whole string as one term. -/
def parseLit (s : String) : Except String Expr := do
  let b := s.toUTF8
  let (e, j) ← parseTerm b 0
  unless j == b.size do throw s!"lit%: trailing input at {j}"
  return e

/-- A whole string as a list of terms of type `ty`. -/
partial def parseLits (ty : Expr) (s : String) : Except String Expr := do
  let b := s.toUTF8
  let rec go (j : Nat) (acc : Array Expr) : Except String Expr := do
    if j ≥ b.size then
      return acc.foldr (fun x l => mkApp3 (mkConst ``List.cons [levelZero]) ty x l)
        (mkApp (mkConst ``List.nil [levelZero]) ty)
    let (e, j') ← parseTerm b j
    go j' (acc.push e)
  go 0 #[]

/-- A whole string `[…][…]…` as a list of lists of naturals. -/
partial def parseNatss (s : String) : Except String Expr := do
  let b := s.toUTF8
  let ty := mkApp (mkConst ``List [levelZero]) (mkConst ``Nat)
  let rec go (j : Nat) (acc : Array Expr) : Except String Expr := do
    if j ≥ b.size then
      return acc.foldr (fun x l => mkApp3 (mkConst ``List.cons [levelZero]) ty x l)
        (mkApp (mkConst ``List.nil [levelZero]) ty)
    let (e, j') ← parseNats b j false
    go j' (acc.push e)
  go 0 #[]

/-- `lit% "…"`: one certificate term. -/
syntax (name := litStx) "lit% " str : term

/-- `lits% T "…"`: a list of certificate terms of type `T`. -/
syntax (name := litsStx) "lits% " ident str : term

/-- `natss% "…"`: a list of lists of naturals (numerals, as in elaborated statements). -/
syntax (name := natssStx) "natss% " str : term

@[term_elab litStx] def elabLit : TermElab := fun stx _ => do
  let some s := stx[1].isStrLit? | throwUnsupportedSyntax
  match parseLit s with
  | .ok e => pure e
  | .error msg => throwError msg

@[term_elab litsStx] def elabLits : TermElab := fun stx _ => do
  let some s := stx[2].isStrLit? | throwUnsupportedSyntax
  let ty ← elabType stx[1]
  match parseLits ty s with
  | .ok e => pure e
  | .error msg => throwError msg

@[term_elab natssStx] def elabNatss : TermElab := fun stx _ => do
  let some s := stx[1].isStrLit? | throwUnsupportedSyntax
  match parseNatss s with
  | .ok e => pure e
  | .error msg => throwError msg

end GridGen.Four.K4.Lit
