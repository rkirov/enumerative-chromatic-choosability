/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Lean

/-!
# Height five at `k = 5`: compact certificate literals

The certificate modules of `GridGen/Five/K5/` carry large data terms (nested lists, tuples and
structures of naturals). Written as ordinary Lean terms, every numeral and constructor is
elaborated separately and recorded in the info trees. `data% "…"` builds the same term directly
from a compact string, guided by the expected type (as `GridGen/Four/K4/Lit.lean` does at height
four). It only constructs a term: the kernel type-checks the result like any other term, so
nothing here is trusted.

Format: a natural is its decimal digits; a list is `[x,y,…]`; a pair, or a structure (an
inductive type with one constructor), is `(x,y,…)` — a tuple of more than two entries for a pair
type `α × β` nests to the right; a constructor of an inductive type with several constructors is
`@i(x,y,…)`, `i` its index.
-/

namespace GridGen.Five.K5.Lit

open Lean Elab Term Meta

/-- A parsed literal. -/
inductive Node where
  | num (n : Nat)
  | list (xs : Array Node)
  | tup (xs : Array Node)
  | ctor (i : Nat) (xs : Array Node)
  deriving Inhabited

/-- Decimal digits from position `j`. -/
partial def parseDigits (b : ByteArray) (j acc : Nat) : Nat × Nat :=
  if h : j < b.size then
    let d := b[j].toNat
    if 48 ≤ d ∧ d ≤ 57 then parseDigits b (j + 1) (acc * 10 + (d - 48)) else (acc, j)
  else (acc, j)

/-- Parse a node at position `i` of `b`. -/
partial def parseNode (b : ByteArray) (i : Nat) : Except String (Node × Nat) := do
  unless i < b.size do throw "data%: unexpected end"
  let c := b[i]!.toNat
  if 48 ≤ c ∧ c ≤ 57 then
    let (n, j) := parseDigits b i 0
    return (.num n, j)
  else if c == 91 then -- `[`
    let (xs, j) ← parseSeq b (i + 1) 93
    return (.list xs, j)
  else if c == 40 then -- `(`
    let (xs, j) ← parseSeq b (i + 1) 41
    return (.tup xs, j)
  else if c == 64 then -- `@`
    let (k, j) := parseDigits b (i + 1) 0
    unless j < b.size && b[j]!.toNat == 40 do throw s!"data%: `(` expected at {j}"
    let (xs, j') ← parseSeq b (j + 1) 41
    return (.ctor k xs, j')
  else throw s!"data%: unexpected character at {i}"
where
  /-- A comma-separated sequence up to the closing byte `close`. -/
  parseSeq (b : ByteArray) (i : Nat) (close : Nat) : Except String (Array Node × Nat) := do
    if i < b.size && b[i]!.toNat == close then return (#[], i + 1)
    let mut j := i
    let mut xs : Array Node := #[]
    repeat
      let (x, j') ← parseNode b j
      xs := xs.push x
      if j' < b.size && b[j']!.toNat == 44 then j := j' + 1
      else if j' < b.size && b[j']!.toNat == close then return (xs, j' + 1)
      else throw s!"data%: `,` or closing bracket expected at {j'}"
    return (xs, j)

/-- The constructor index and fields of a node. -/
def nodeCtor (nm : Name) (nctors : Nat) : Node → MetaM (Nat × Array Node)
  | .tup xs => do
    unless nctors == 1 do throwError "data%: `{nm}` has several constructors"
    return (0, xs)
  | .ctor k xs => return (k, xs)
  | _ => throwError "data%: unexpected literal for `{nm}`"

/-- Build the term of type `ty` described by a node. -/
partial def build (ty : Expr) (n : Node) : MetaM Expr := do
  let ty ← whnfR ty
  let fn := ty.getAppFn
  let args := ty.getAppArgs
  match fn, n with
  | .const ``Nat _, .num k => return mkRawNatLit k
  | .const ``List [u], .list xs => do
    let α := args[0]!
    let mut acc := mkApp (mkConst ``List.nil [u]) α
    for x in xs.reverse do
      acc := mkApp3 (mkConst ``List.cons [u]) α (← build α x) acc
    return acc
  | .const ``Prod [u, v], .tup xs => do
    unless 2 ≤ xs.size do throwError "data%: a pair needs two entries"
    let α := args[0]!; let β := args[1]!
    let a ← build α xs[0]!
    let b ← if xs.size == 2 then build β xs[1]! else build β (.tup (xs.extract 1 xs.size))
    return mkApp4 (mkConst ``Prod.mk [u, v]) α β a b
  | .const nm us, _ => do
    let info ← getConstInfoInduct nm
    let (k, xs) ← nodeCtor nm info.ctors.length n
    let some cn := info.ctors[k]? | throwError "data%: `{nm}` has no constructor {k}"
    let cinfo ← getConstInfoCtor cn
    let params := args.extract 0 info.numParams
    let mut cty := cinfo.type.instantiateLevelParams cinfo.levelParams us
    cty ← instantiateForall cty params
    let mut e := mkAppN (mkConst cn us) params
    for x in xs do
      let cty' ← whnfR cty
      let .forallE _ d body _ := cty' | throwError "data%: too many fields for `{cn}`"
      let a ← build d x
      e := mkApp e a
      cty := body.instantiate1 a
    return e
  | _, _ => throwError "data%: cannot build a literal of type {ty}"

/-- `data% "…"`: the term of the expected type described by the string. -/
elab "data% " s:str : term <= ty => do
  let b := s.getString.toUTF8
  match parseNode b 0 with
  | .error err => throwError err
  | .ok (n, j) =>
    unless j == b.size do throwError "data%: trailing input at {j}"
    build ty n

end GridGen.Five.K5.Lit
