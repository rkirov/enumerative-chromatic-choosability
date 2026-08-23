/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Cacti.Rooted

/-!
# Weighted coloring counts

The block induction (handoff §4) attaches **weights** to vertices: when a subtree hangs off a
cut vertex `v`, its rooted profile becomes a per-colour weight multiplying every coloring of
the rest. `wcol` is the weighted partition function `Z(w) = ∑_f ∏_v w v (f v)` over proper
`L`-colorings; weights are natural numbers, because the weights that actually occur are rooted
coloring counts.

* `wcol_const_one` — trivial weights recover `col`.
-/

namespace ListColoring

open SimpleGraph Finset

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The **weighted count**: proper `L`-colorings, each weighted by the product over vertices of
the vertex's weight at its colour. -/
def wcol (L : ListAssignment V) (w : V → ℕ → ℕ) : ℕ :=
  ∑ f ∈ G.colorings L, ∏ v, w v (f v)

/-- The **weighted rooted count**. -/
def rootedWcol (L : ListAssignment V) (w : V → ℕ → ℕ) (r : V) (c : ℕ) : ℕ :=
  ∑ f ∈ (G.colorings L).filter (fun f => f r = c), ∏ v, w v (f v)

@[simp] theorem wcol_const_one (L : ListAssignment V) :
    wcol G L (fun _ _ => 1) = G.col L := by
  rw [wcol, SimpleGraph.col]
  simp

section WeightedCut

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Splitting a product over all vertices along a cover `A ∪ B` meeting exactly at `r`, with
the `r`-factor charged to the `A` side. -/
theorem prod_split_of_cut {A B : Set V} [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    {r : V} (hrA : r ∈ A) (hrB : r ∈ B) (hcover : ∀ v, v ∈ A ∨ v ∈ B)
    (hmeet : ∀ v, v ∈ A → v ∈ B → v = r) (F : V → ℕ) :
    ∏ v, F v = (∏ v : A, F v.val) * (∏ v : B, if v.val = r then 1 else F v.val) := by
  have hsub : ∀ (s : Set V) [DecidablePred (· ∈ s)] (H : V → ℕ),
      (∏ v : s, H v.val) = ∏ v ∈ s.toFinset, H v := by
    intro s _ H
    rw [← Finset.prod_subtype s.toFinset (fun v => Set.mem_toFinset) H]
  rw [hsub A F, hsub B (fun x => if x = r then 1 else F x)]
  have hB : (∏ v ∈ B.toFinset, if v = r then 1 else F v)
      = ∏ v ∈ B.toFinset.erase r, F v := by
    rw [← Finset.mul_prod_erase B.toFinset _ (Set.mem_toFinset.mpr hrB), if_pos rfl, one_mul]
    exact Finset.prod_congr rfl fun v hv => if_neg (Finset.ne_of_mem_erase hv)
  rw [hB, ← Finset.prod_union (by
    rw [Finset.disjoint_right]
    intro v hv hvA
    have hvB : v ∈ B.toFinset.erase r → v ∈ B := fun h => Set.mem_toFinset.mp (Finset.mem_of_mem_erase h)
    exact Finset.ne_of_mem_erase hv (hmeet v (Set.mem_toFinset.mp hvA) (hvB hv)))]
  apply Finset.prod_congr _ (fun _ _ => rfl)
  ext v
  simp only [Finset.mem_union, Set.mem_toFinset, Finset.mem_erase, Finset.mem_univ, true_iff]
  rcases hcover v with h | h
  · exact Or.inl h
  · by_cases hvr : v = r
    · exact Or.inl (hvr ▸ hrA)
    · exact Or.inr ⟨hvr, h⟩

end WeightedCut

end ListColoring
