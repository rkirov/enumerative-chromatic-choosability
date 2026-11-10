/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.CapacityLemma
import Outerplanar.WitnessThree
import Outerplanar.Face
import Outerplanar.Graph
import Outerplanar.Dissection

/-!
# Graphs built by pendant vertices and ears on edges are enumeratively chromatic-choosable

## What is claimed

`EarBuilt G m₀ univ` says that `G` can be built from nothing by adding, one at a time, a vertex
with at most one earlier neighbour, or an *ear on an edge*: a path of at least `max m₀ 1` new
vertices joined to two adjacent earlier vertices, with no other new edges. For `m₀ = 1` these
are the graphs each of whose blocks is an edge or an edge-retaining 2-sum of cycles; every
outerplanar graph is one (so are 2-trees and books of cycles). Mathlib has no planarity, so that
inclusion is formal only for polygon dissections — the outerplanar graphs with a Hamiltonian
cycle (`Outerplanar/Dissection.lean`); for outerplanar graphs with cut vertices it is a remark.

* `ecc_of_earBuilt_of_four_le` — such a graph is `k`-ECC for every `k ≥ 4`;
* `ecc_three_of_earBuilt` — if every ear has at least two vertices (no ear closes a
  triangle), it is `3`-ECC;
* `ecc_of_isDissection`, `ecc_three_of_isDissection` — the same for polygon dissections.

"`k`-ECC" is the pointwise notion `SimpleGraph.ECCAt`; in the vocabulary of Kaul et al. and
Allred–Mudrock these are the threshold statements `τ(G) ≤ 4`, resp. `τ(G) ≤ 3`. The case of
three colours with triangles is open.

## Provenance

These are results of the 2026-11 AI research collaboration on this repository, not of the
Kirov–Naimi paper. Source of record: `ai_research_notes/OUTERPLANAR_PROOF_DRAFT_2026-11-09.md`.
Cacti (`Cacti/`), ladders (`Ladder/`) and chordal graphs with this structure are special cases
proved earlier; Chi et al. (arXiv:2605.10861) classify theta graphs, which overlaps the case of
two cycles sharing an edge. The proof uses Egerváry's theorem (`Outerplanar/Egervary.lean`).
-/

namespace Outerplanar

open Finset

/-- **The capacity lemma for three colours** on cycles of length at least three. -/
theorem cl_three (n : ℕ) [NeZero n] (hn : 3 ≤ n) : CL 3 n :=
  cl_three_of witness_three_three (fun _ _ h => witness_three_zero h) n hn

/-- **The capacity lemma**: `k ≥ 4` colours, cycles of length at least two. -/
theorem cl_four_le {k : ℕ} (hk : 4 ≤ k) (n : ℕ) [NeZero n] (hn : 2 ≤ n) : CL k n :=
  cl_of_four_le (fun n _ hn => cl_three n hn) k hk n hn

theorem faceClosed_of_cl {k m : ℕ} (hk : 3 ≤ k) (hm : 1 ≤ m) (hCL : CL k (m + 1)) :
    FaceClosed k m := fun Lu Lv Li hLu hLv hLi ω hω E hE0 A hA hE =>
  face_hasPot hk hm hCL Lu Lv Li hLu hLv hLi ω hω E hE0 A hA hE

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Graphs built by pendant vertices and ears on edges are `k`-ECC for `k ≥ 4`.**
In particular every outerplanar graph is. -/
theorem ecc_of_earBuilt_of_four_le {k : ℕ} (hk : 4 ≤ k) (h : EarBuilt G 1 univ) : G.ECCAt k :=
  ecc_of_earBuilt G (by omega) (fun m hm _ => faceClosed_of_cl (by omega) hm
    (cl_four_le hk (m + 1) (by omega))) h

/-- **If no ear closes a triangle, the graph is `3`-ECC.** -/
theorem ecc_three_of_earBuilt (h : EarBuilt G 2 univ) : G.ECCAt 3 :=
  ecc_of_earBuilt G (le_refl 3) (fun m hm hm2 => faceClosed_of_cl (le_refl 3) hm
    (cl_three (m + 1) (by omega))) h

/-- **Every outerplanar graph with a Hamiltonian cycle** (a polygon dissection) **is `k`-ECC
for `k ≥ 4`.** -/
theorem ecc_of_isDissection {n k : ℕ} (hk : 4 ≤ k) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (h : IsDissection G) : G.ECCAt k :=
  ecc_of_earBuilt_of_four_le G hk (earBuilt_of_isDissection G h)

/-- **A triangle-free polygon dissection is `3`-ECC.** -/
theorem ecc_three_of_isDissection {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : IsDissection G) (htri : ∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj a c) :
    G.ECCAt 3 :=
  ecc_three_of_earBuilt G (earBuilt_two_of_isDissection G h htri)

end Outerplanar


/-! The four statements depend on no axioms beyond the three standard ones. -/

/-- info: 'Outerplanar.ecc_of_earBuilt_of_four_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Outerplanar.ecc_of_earBuilt_of_four_le

/-- info: 'Outerplanar.ecc_three_of_earBuilt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Outerplanar.ecc_three_of_earBuilt

/-- info: 'Outerplanar.ecc_of_isDissection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Outerplanar.ecc_of_isDissection

/-- info: 'Outerplanar.ecc_three_of_isDissection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Outerplanar.ecc_three_of_isDissection
