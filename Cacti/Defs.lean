/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ListColoring

/-!
# Cacti: definitions

**Provenance.** This library formalizes the cactus ECC classification developed in
`ai_research_notes/` (2026-08-15) by the two AI research agents working on this repository.
It is **not** part of the Kirov–Naimi paper formalization in `ListColoring/`, which it imports
but must never be imported by. The mathematical source of record is
`ai_research_notes/FINAL_CACTI_ECC_HANDOFF.md`, reviewed in
`ai_research_notes/ADVERSARIAL_REVIEW_2026-08-15_HANDOFF.md`.

A **cactus** is a connected graph in which every edge lies in at most one cycle. We separate the
cycle condition (`IsCactusForest`) from connectedness (`IsCactus`), so componentwise extensions can
reuse the former without changing the scope of the classification proved in this directory. The
cycle condition says that any two cycles (closed walks satisfying `Walk.IsCycle`) sharing an edge
have equal edge sets. This is the form the decomposition consumes; a bridge to a future block-tree
API can be proved independently.
-/

namespace ListColoring

open SimpleGraph

variable {V : Type} [DecidableEq V] (G : SimpleGraph V)

/-- A **cactus forest**: any two cycles sharing an edge coincide as edge sets. This is the
componentwise cycle condition; unlike `IsCactus`, it does not assert connectedness. -/
def IsCactusForest : Prop :=
  ∀ ⦃u v : V⦄ (p : G.Walk u u) (q : G.Walk v v), p.IsCycle → q.IsCycle →
    ∀ e ∈ p.edges, e ∈ q.edges → p.edges.toFinset = q.edges.toFinset

/-- A **cactus**: a connected graph in which any two cycles sharing an edge coincide as edge
sets. The classification in this directory is for this connected notion. Equivalence with the
usual block characterization (every block is an edge or a cycle) is not yet part of the API. -/
def IsCactus : Prop :=
  G.Connected ∧ IsCactusForest G

theorem isCactus_iff_connected_and_forest :
    IsCactus G ↔ G.Connected ∧ IsCactusForest G := Iff.rfl

/-- **At most one cycle**: any two cycles coincide as edge sets. Together with connectivity this
covers trees (no cycles at all) and unicyclic graphs. This is the structural side of the `k = 2`
cactus classification. -/
def HasAtMostOneCycle : Prop :=
  ∀ ⦃u v : V⦄ (p : G.Walk u u) (q : G.Walk v v), p.IsCycle → q.IsCycle →
    p.edges.toFinset = q.edges.toFinset

end ListColoring
