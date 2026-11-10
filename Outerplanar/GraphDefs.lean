/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ListColoring.Defs
import Outerplanar.Pot

/-!
# Graphs built by pendant vertices and ears on edges: definitions

`EarBuilt G m₀ S` says that the subgraph of `G` induced on the vertex set `S` can be built from
nothing by repeatedly adding

* a new vertex with at most one neighbour among the vertices already present, or
* an *ear on an edge*: a path of `m ≥ max m₀ 1` new vertices `x 0, …, x (m - 1)` joined to two
  **adjacent** old vertices `u` and `v` (so that `u, x 0, …, x (m - 1), v` is a cycle of length
  `m + 2`), with no other edges between the new vertices and the old ones or each other.

For `m₀ = 1` these are exactly the graphs each of whose blocks is an edge or an edge-retaining
2-sum of cycles; they include all outerplanar graphs. For `m₀ = 2` no ear closes a triangle.

`ZG` is the weighted partition function on a vertex set, with vertex weights `ω` and a pair
profile `Ω x y` on every ordered pair of adjacent vertices.
-/

namespace Outerplanar

open Finset

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The induced subgraph on `S` is built by pendant vertices and by ears of at least `m₀`
vertices on edges. -/
inductive EarBuilt (m₀ : ℕ) : Finset V → Prop
  | empty : EarBuilt m₀ ∅
  | pendant (S : Finset V) (x : V) (hx : x ∉ S) (hS : EarBuilt m₀ S)
      (hdeg : (S.filter (G.Adj x)).card ≤ 1) : EarBuilt m₀ (insert x S)
  | ear (S : Finset V) (m : ℕ) (hm : 1 ≤ m) (hm₀ : m₀ ≤ m) (u v : V) (hu : u ∈ S) (hv : v ∈ S)
      (huv : G.Adj u v) (x : Fin m → V) (hinj : Function.Injective x) (hxS : ∀ j, x j ∉ S)
      (hS : EarBuilt m₀ S)
      (hold : ∀ j, ∀ y ∈ S, G.Adj (x j) y ↔ (j.val = 0 ∧ y = u) ∨ (j.val + 1 = m ∧ y = v))
      (hnew : ∀ j j', G.Adj (x j) (x j') ↔ j.val + 1 = j'.val ∨ j'.val + 1 = j.val) :
      EarBuilt m₀ (S ∪ univ.image x)

/-- The ordered pairs of adjacent vertices of `S`. -/
def adjPairs (S : Finset V) : Finset (V × V) := (S ×ˢ S).filter fun p => G.Adj p.1 p.2

/-- The assignments on `S`: a colour of `L x` for `x ∈ S`, and `0` elsewhere. -/
def assignments (S : Finset V) (L : V → Finset ℕ) : Finset (V → ℕ) :=
  Fintype.piFinset fun x => if x ∈ S then L x else {0}

/-- The weighted partition function of the vertex set `S`. -/
noncomputable def ZG (S : Finset V) (L : V → Finset ℕ) (ω : V → ℕ → ℝ)
    (Ω : V → V → ℕ → ℕ → ℝ) : ℝ :=
  ∑ f ∈ assignments S L, (∏ x ∈ S, ω x (f x)) * ∏ p ∈ adjPairs G S, Ω p.1 p.2 (f p.1) (f p.2)

/-- The pair profile of an ordinary edge, on one of its two orientations. -/
def neProfile : V → V → ℕ → ℕ → ℝ := fun _ _ c d => if c ≠ d then 1 else 0

end Outerplanar
