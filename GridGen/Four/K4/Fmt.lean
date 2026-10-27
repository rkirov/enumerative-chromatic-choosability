/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.K4.Tree

/-!
# Height four at `k = 4`: short names for generated certificate trees

The generated modules (`ai_research_notes/h4k4lean/`) write certificate trees with these
abbreviations, and check each with `chainOK`.
-/

namespace GridGen.Four.K4

/-- A leaf. -/
abbrev Lf : CT := CT.leaf
/-- A pruned node. -/
abbrev Pr : CT := CT.prune
/-- A branching. -/
abbrev Nd (i : ℕ) (ts : List ℕ) (k : CTL) (o : CT) : CT := CT.node i ts k o
/-- A list of trees. -/
abbrev Ks (a : CT) (b : CTL) : CTL := CTL.cons a b
/-- The empty list of trees. -/
abbrev En : CTL := CTL.nil

/-- The value of a node, for every column of the shape. -/
def GoodSh (sh : Sh) (nd : Node) (v : V5) : Prop := ∀ B : Col, ShapeOf B sh → Good B nd v

/-- **The chain check of a shape**: the tree's root value is nonnegative. -/
def chainOK (sh : Sh) (gs : List (Node × V5)) (T : CT) : Bool :=
  match evalCT sh gs Node.root T with
  | some v => v.nonneg
  | none => false

theorem raysOK_of_chainOK {B : Col} {sh : Sh} (hB : ShapeOf B sh) {gs : List (Node × V5)}
    (hgs : ∀ p ∈ gs, GoodSh sh p.1 p.2) {T : CT}
    (h : chainOK sh gs T = true) {Y : Col} (hY : CardsIn 3 4 Y) : RaysOK (dvec Y B) := by
  unfold chainOK at h
  split at h
  · next v hv => exact raysOK_of_tree hB (fun p hp => hgs p hp B hB) hv h hY
  · exact absurd h (by decide)

/-- **A separately checked subtree**: its value at the node is at least `v`. -/
def subOK (sh : Sh) (gs : List (Node × V5)) (nd : Node) (T : CT) (v : V5) : Bool :=
  match evalCT sh gs nd T with
  | some u => V5.leB v u
  | none => false

theorem goodSh_of_subOK {sh : Sh} {gs : List (Node × V5)} {nd : Node} {T : CT} {v : V5}
    (hgs : ∀ p ∈ gs, GoodSh sh p.1 p.2) (h : subOK sh gs nd T v = true) : GoodSh sh nd v := by
  intro B hB
  unfold subOK at h
  split at h
  · next u hu => exact good_mono (evalCT_sound hB (fun p hp => hgs p hp B hB) T nd u hu) h
  · exact absurd h (by decide)

end GridGen.Four.K4
