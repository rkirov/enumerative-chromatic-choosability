/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.ExtendW

/-!
# Graphs whose blocks are polygon dissections

**`BlockDecomp G ι`** — a decomposition of the graph `G` into blocks indexed by `ι`: each block is
a polygon dissection `H i` on `Fin (n i)` with `n i ≥ 2` (for `n i = 2` a single edge, a bridge),
embedded in `G` by an injective `ψ i`, such that

* the edges of `G` are the edges of the blocks (`adj`);
* two blocks share at most one vertex (`meet`);
* the blocks form a tree (`tree`): after deleting the edges of a block, no two of its vertices
  are connected.

Every outerplanar graph has such a decomposition into its blocks: a block of an outerplanar graph
is a single edge or a 2-connected outerplanar graph, i.e. a polygon dissection of its Hamiltonian
cycle (the statement `IsDissection` of `Outerplanar/Dissection.lean` is in terms of that cycle);
the converse holds as well. These classical facts are not formalized here: the theorems are
stated for graphs with a block decomposition.

What hangs at a vertex `y` of a block `i` away from the block is `hang i y`: the vertices reachable
from `ψ i y` once the edges of the block are deleted. The facts proved here:

* `hangOK` — the hanging sets of a block are pairwise disjoint, `hang i y` meets the block in
  `ψ i y` only, and every neighbour of `ψ i y` outside the block hangs at `y`
  (`Outerplanar/ExtendW.lean`'s `HangOK`);
* `hang_sub`, `hang_decomp`, `branch_disj` — what hangs at `x` away from `i` is the union of the
  branches at `x` of the other blocks at `x`: for such a block `j` with `x = ψ j z₀`, the sets
  `hang j z` with `z ≠ z₀`; branches of different blocks are disjoint;
* `block_mem_hang` — a block meeting `hang j z` (`j` another block) lies in it;
* `hang_cover` — in a connected graph, the hanging sets of one block cover all vertices;
* views — a block read in coordinates rotated by `c` (`vψ`, `vH`, `vhang`), with the facts of
  `extendW`.

Part of the formalization of the seven-even-face theorem with cut vertices (research note
`ai_research_notes/OUTERPLANAR_SEVEN_AND_CUTS_2026-11-23.md`); formalized by Claude.
-/

namespace Outerplanar

open Finset SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The edges of a block, as unordered pairs of vertices of `G`. -/
def blockEdgeSet {n : ℕ} (H : SimpleGraph (Fin n)) (ψ : Fin n → V) : Set (Sym2 V) :=
  {e | ∃ a b, H.Adj a b ∧ s(ψ a, ψ b) = e}

/-- **A decomposition of `G` into blocks that are polygon dissections** (or single edges),
arranged in a tree. -/
structure BlockDecomp (G : SimpleGraph V) (ι : Type) where
  /-- The number of vertices of each block. -/
  n : ι → ℕ
  /-- Each block, as a graph on its polygon `0, 1, …, n i - 1`. -/
  H : (i : ι) → SimpleGraph (Fin (n i))
  /-- The vertices of each block in `G`. -/
  ψ : (i : ι) → Fin (n i) → V
  two_le : ∀ i, 2 ≤ n i
  diss : ∀ i, IsDissection (H i)
  inj : ∀ i, Function.Injective (ψ i)
  /-- The edges of `G` are the edges of the blocks. -/
  adj : ∀ x y, G.Adj x y ↔ ∃ i a b, (H i).Adj a b ∧ ψ i a = x ∧ ψ i b = y
  /-- Two blocks share at most one vertex. -/
  meet : ∀ i j, i ≠ j → ∀ a b a' b', ψ i a = ψ j a' → ψ i b = ψ j b' → a = b
  /-- The blocks form a tree: without the edges of a block, its vertices are disconnected. -/
  tree : ∀ i (y y' : Fin (n i)), y ≠ y' →
    ¬ (G.deleteEdges (blockEdgeSet (H i) (ψ i))).Reachable (ψ i y) (ψ i y')

/-- A property spreading along the edges of a walk from `s` holds at its end. -/
theorem reach_closed {G' : SimpleGraph V} {s : V} {P : V → Prop} (hs : P s)
    (hstep : ∀ u w, G'.Reachable s u → G'.Adj u w → P u → P w) {v : V}
    (hv : G'.Reachable s v) : P v := by
  obtain ⟨p⟩ := hv
  suffices h : ∀ {u v : V} (p : G'.Walk u v), G'.Reachable s u → P u → P v from
    h p (Reachable.refl s) hs
  intro u v p
  induction p with
  | nil => exact fun _ h => h
  | cons h p ih => exact fun hr hu => ih (hr.trans h.reachable) (hstep _ _ hr h hu)

namespace BlockDecomp

variable {G : SimpleGraph V} {ι : Type} (D : BlockDecomp G ι)

/-- `G` without the edges of the block `i`. -/
abbrev del (i : ι) : SimpleGraph V := G.deleteEdges (blockEdgeSet (D.H i) (D.ψ i))

variable {D}

theorem mem_blockEdgeSet {i : ι} {v w : V} :
    s(v, w) ∈ blockEdgeSet (D.H i) (D.ψ i) ↔
      ∃ a b, (D.H i).Adj a b ∧ D.ψ i a = v ∧ D.ψ i b = w := by
  constructor
  · rintro ⟨a, b, h, e⟩
    rcases Sym2.eq_iff.mp e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨a, b, h, rfl, rfl⟩
    · exact ⟨b, a, h.symm, rfl, rfl⟩
  · rintro ⟨a, b, h, rfl, rfl⟩
    exact ⟨a, b, h, rfl⟩

/-- Adjacency in `G` between vertices of a block is adjacency in the block. -/
theorem adj_block {i : ι} {a b : Fin (D.n i)} : G.Adj (D.ψ i a) (D.ψ i b) ↔ (D.H i).Adj a b := by
  rw [D.adj]
  constructor
  · rintro ⟨j, a', b', h, e1, e2⟩
    by_cases hj : j = i
    · subst hj
      rwa [← D.inj j e1, ← D.inj j e2]
    · exact absurd (D.meet j i hj a' b' a b e1 e2) h.ne
  · intro h
    exact ⟨i, a, b, h, rfl, rfl⟩

/-- An edge of another block is not an edge of the block `i`. -/
theorem notMem_blockEdgeSet {i k : ι} (hk : k ≠ i) {a b : Fin (D.n k)} (h : (D.H k).Adj a b) :
    s(D.ψ k a, D.ψ k b) ∉ blockEdgeSet (D.H i) (D.ψ i) := by
  rw [mem_blockEdgeSet]
  rintro ⟨a', b', -, e1, e2⟩
  exact h.ne (D.meet k i hk a b a' b' e1.symm e2.symm)

/-- The vertices of a block are connected by its own edges. -/
theorem block_reach {E : Set (Sym2 V)} {k : ι}
    (hE : ∀ a b, (D.H k).Adj a b → s(D.ψ k a, D.ψ k b) ∉ E) (a b : Fin (D.n k)) :
    (G.deleteEdges E).Reachable (D.ψ k a) (D.ψ k b) := by
  have hstep : ∀ t (ht : t + 1 < D.n k),
      (G.deleteEdges E).Adj (D.ψ k ⟨t, by omega⟩) (D.ψ k ⟨t + 1, ht⟩) := fun t ht => by
    have h := (D.diss k).1 ⟨t, by omega⟩ ⟨t + 1, ht⟩ rfl
    rw [deleteEdges_adj]
    exact ⟨adj_block.mpr h, hE _ _ h⟩
  have h0 : ∀ t (ht : t < D.n k),
      (G.deleteEdges E).Reachable (D.ψ k ⟨0, by omega⟩) (D.ψ k ⟨t, ht⟩) := by
    intro t
    induction t with
    | zero => intro _; exact Reachable.refl _
    | succ t ih => intro ht; exact (ih (by omega)).trans (hstep t ht).reachable
  exact (h0 a.val a.isLt).symm.trans (h0 b.val b.isLt)

/-! ### What hangs at a vertex of a block -/

variable (D) in
open Classical in
/-- What hangs at the vertex `y` of the block `i`: the vertices reachable from `ψ i y` without
the edges of the block. -/
noncomputable def hang (i : ι) (y : Fin (D.n i)) : Finset V :=
  univ.filter fun v => (D.del i).Reachable (D.ψ i y) v

theorem mem_hang {i : ι} {y : Fin (D.n i)} {v : V} :
    v ∈ D.hang i y ↔ (D.del i).Reachable (D.ψ i y) v := by
  unfold hang
  simp only [mem_filter, mem_univ, true_and]

theorem hang_self (i : ι) (y : Fin (D.n i)) : D.ψ i y ∈ D.hang i y :=
  mem_hang.mpr (Reachable.refl _)

theorem hang_disj {i : ι} {y y' : Fin (D.n i)} {v : V} (h : v ∈ D.hang i y)
    (h' : v ∈ D.hang i y') : y = y' := by
  by_contra hne
  exact D.tree i y y' hne ((mem_hang.mp h).trans (mem_hang.mp h').symm)

theorem hang_idx {i : ι} {y a : Fin (D.n i)} (h : D.ψ i a ∈ D.hang i y) : a = y :=
  hang_disj (hang_self i a) h

/-- **What hangs at `y` is closed in `G`**, except for the edges of the block at `ψ i y`. -/
theorem hang_closed {i : ι} {y : Fin (D.n i)} {v w : V} (hv : v ∈ D.hang i y)
    (hvw : G.Adj v w) : w ∈ D.hang i y ∨ (v = D.ψ i y ∧ ∃ b, D.ψ i b = w) := by
  by_cases he : s(v, w) ∈ blockEdgeSet (D.H i) (D.ψ i)
  · obtain ⟨a, b, -, rfl, rfl⟩ := mem_blockEdgeSet.mp he
    right
    rw [hang_idx hv]
    exact ⟨rfl, b, rfl⟩
  · left
    exact mem_hang.mpr ((mem_hang.mp hv).trans (Adj.reachable
      ((deleteEdges_adj).mpr ⟨hvw, he⟩)))

/-- **The hanging sets of a block satisfy the hypotheses of `extendW`.** -/
theorem hangOK (i : ι) : HangOK G (D.ψ i) (D.hang i) where
  self := hang_self i
  disj _ _ _ h h' := hang_disj h h'
  nbr z y h := by
    rcases hang_closed (hang_self i z) h with h | ⟨-, b, hb⟩
    · exact Or.inr h
    · exact Or.inl ⟨b, hb⟩

/-- **A block meeting what hangs at a vertex of another block lies in it.** -/
theorem block_mem_hang {j k : ι} (hkj : k ≠ j) {z : Fin (D.n j)} {a : Fin (D.n k)}
    (ha : D.ψ k a ∈ D.hang j z) (b : Fin (D.n k)) : D.ψ k b ∈ D.hang j z :=
  mem_hang.mpr ((mem_hang.mp ha).trans
    (block_reach (fun _ _ h => notMem_blockEdgeSet hkj h) a b))

/-- **The branch of another block at `x = ψ i y`** hangs at `y`. -/
theorem hang_sub {i j : ι} (hji : j ≠ i) {y : Fin (D.n i)} {z₀ z : Fin (D.n j)}
    (hz₀ : D.ψ j z₀ = D.ψ i y) (hz : z ≠ z₀) : D.hang j z ⊆ D.hang i y := by
  intro v hv
  have hjz : D.ψ j z ∈ D.hang i y :=
    block_mem_hang hji (by rw [hz₀]; exact hang_self i y) z
  refine reach_closed (G' := D.del j) (s := D.ψ j z) (P := (· ∈ D.hang i y)) hjz ?_
    (mem_hang.mp hv)
  intro u w hru huw hu
  rcases hang_closed hu ((deleteEdges_adj).mp huw).1 with h | ⟨h, -⟩
  · exact h
  · exfalso
    have : D.ψ j z₀ ∈ D.hang j z := mem_hang.mpr (by rw [hz₀, ← h]; exact hru)
    exact hz (hang_idx this).symm

/-- **What hangs at `x = ψ i y`** is `x` and the branches of the other blocks at `x`. -/
theorem hang_decomp {i : ι} {y : Fin (D.n i)} {v : V} (hv : v ∈ D.hang i y) :
    v = D.ψ i y ∨ ∃ j, j ≠ i ∧ ∃ z₀ z, D.ψ j z₀ = D.ψ i y ∧ z ≠ z₀ ∧ v ∈ D.hang j z := by
  refine reach_closed (G' := D.del i) (s := D.ψ i y)
    (P := fun v => v = D.ψ i y ∨ ∃ j, j ≠ i ∧ ∃ z₀ z, D.ψ j z₀ = D.ψ i y ∧ z ≠ z₀ ∧
      v ∈ D.hang j z) (Or.inl rfl) ?_ (mem_hang.mp hv)
  intro u w _ huw hu
  obtain ⟨hG, hnot⟩ := (deleteEdges_adj).mp huw
  obtain ⟨k, a, b, hk, rfl, rfl⟩ := (D.adj _ _).mp hG
  have hki : k ≠ i := by
    rintro rfl
    exact hnot ⟨a, b, hk, rfl⟩
  rcases hu with hu | ⟨j, hji, z₀, z, hz₀, hzz, hu⟩
  · exact Or.inr ⟨k, hki, a, b, hu, hk.ne.symm, hang_self k b⟩
  · rcases hang_closed hu hG with h | ⟨-, b', h2⟩
    · exact Or.inr ⟨j, hji, z₀, z, hz₀, hzz, h⟩
    · by_cases hb : b' = z₀
      · left
        rw [← h2, hb, hz₀]
      · exact Or.inr ⟨j, hji, z₀, b', hz₀, hb, h2 ▸ hang_self j b'⟩

/-- **Branches of different blocks at a vertex are disjoint.** -/
theorem branch_disj {j j' : ι} (hjj : j ≠ j') {z₀ z : Fin (D.n j)} {z₀' z' : Fin (D.n j')}
    (he : D.ψ j' z₀' = D.ψ j z₀) (hz : z ≠ z₀) (hz' : z' ≠ z₀') {v : V}
    (hv : v ∈ D.hang j z) (hv' : v ∈ D.hang j' z') : False :=
  hz (hang_disj hv (hang_sub (Ne.symm hjj) he hz' hv'))

/-- **In a connected graph the hanging sets of a block cover all vertices.** -/
theorem hang_cover (hc : G.Connected) (i : ι) (v : V) : ∃ y, v ∈ D.hang i y := by
  have h0 : 0 < D.n i := by have := D.two_le i; omega
  refine reach_closed (G' := G) (s := D.ψ i ⟨0, h0⟩) (P := fun v => ∃ y, v ∈ D.hang i y)
    ⟨_, hang_self i _⟩ ?_ (hc.preconnected _ v)
  rintro u w - huw ⟨y, hu⟩
  rcases hang_closed hu huw with h | ⟨-, b, rfl⟩
  · exact ⟨y, h⟩
  · exact ⟨b, hang_self i b⟩

/-! ### A block in rotated coordinates -/

variable (D) in
/-- The vertices of the block `i`, read from `c`. -/
def vψ (i : ι) (c : Fin (D.n i)) : Fin (D.n i) → V := fun k => D.ψ i (rot c k)

variable (D) in
/-- The block `i`, read from `c`. -/
def vH (i : ι) (c : Fin (D.n i)) : SimpleGraph (Fin (D.n i)) := (D.H i).comap (rot c)

variable (D) in
/-- What hangs at the vertices of the block `i`, read from `c`. -/
noncomputable def vhang (i : ι) (c : Fin (D.n i)) : Fin (D.n i) → Finset V :=
  fun k => D.hang i (rot c k)

theorem view_diss (i : ι) (c : Fin (D.n i)) : IsDissection (D.vH i c) :=
  isDissection_rot (D.diss i) c

theorem view_inj (i : ι) (c : Fin (D.n i)) : Function.Injective (D.vψ i c) :=
  (D.inj i).comp (rot_injective c)

theorem view_adj (i : ι) (c : Fin (D.n i)) (a b : Fin (D.n i)) :
    G.Adj (D.vψ i c a) (D.vψ i c b) ↔ (D.vH i c).Adj a b := adj_block

theorem view_hangOK (i : ι) (c : Fin (D.n i)) : HangOK G (D.vψ i c) (D.vhang i c) where
  self k := hang_self i _
  disj _ _ _ h h' := rot_injective c (hang_disj h h')
  nbr z y h := by
    rcases (hangOK i).nbr _ y h with ⟨b, rfl⟩ | h
    · left
      haveI : NeZero (D.n i) := ⟨by have := D.two_le i; omega⟩
      refine ⟨b - c, ?_⟩
      simp only [vψ, rot, sub_add_cancel]
    · exact Or.inr h

end BlockDecomp

end Outerplanar
