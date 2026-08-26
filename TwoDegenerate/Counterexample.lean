/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ListColoring.K23

/-!
# A 2-degenerate graph that is not enumeratively chromatic-choosable at 4

The proposed statement

> Every 2-degenerate graph is enumeratively chromatic-choosable at every `k ≥ 4`

is false.  Kaul, Kumar, Liu, Mudrock, Rewers, Shin, Tanahara and To, *Bounding the List Color
Function Threshold from Above*, Involve **16** (2023), 849–882, Theorem 7(ii), prove that the
2-degenerate complete bipartite graph `K₂,₂₇` is not ECC at list size four.

An independent audit of their balanced four-list construction gives the slightly stronger
counterexample `K₂,₂₆`; the paper left `K₂,₂₅` and `K₂,₂₆` open.  The two vertices on the
small side receive the lists `{0,1,2,3}` and `{0,1,4,5}`.  The 26 vertices on the other side
receive four list types, with multiplicities `6, 7, 7, 6`:

* `{0,1,2,4}` six times;
* `{0,1,2,5}` seven times;
* `{0,1,3,4}` seven times;
* `{0,1,3,5}` six times.

The proof does not enumerate `4^28` assignments.  `col_completeBipartite_two_right` first fibres a
coloring over the 16 choices on the small side, after which every fibre is a product of 26 numbers
in `{2,3,4}`.  Kernel computation then checks the resulting small closed expressions.
-/

open Finset

namespace SimpleGraph
namespace TwoDegenerate

/-! ## A product formula for `K₂,n` -/

section Formula

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {L : ListAssignment (Fin 2 ⊕ W)} {a b : ℕ}

/-- The fibre over fixed colors `a,b` on the two-vertex side of `K₂,W`. -/
private lemma card_filter_completeBipartite_two_right
    (ha : a ∈ L (Sum.inl 0)) (hb : b ∈ L (Sum.inl 1)) :
    (((completeBipartiteGraph (Fin 2) W).colorings L).filter
        fun f => (f (Sum.inl 0), f (Sum.inl 1)) = (a, b)).card
      = ∏ w : W, (L (Sum.inr w) \ {a, b}).card := by
  rw [← Fintype.card_piFinset]
  refine Finset.card_nbij' (fun f w => f (Sum.inr w)) (fun g => Sum.elim ![a, b] g) ?_ ?_ ?_ ?_
  · intro f hf
    simp only [Finset.mem_coe, Finset.mem_filter, mem_colorings, Prod.mk.injEq] at hf
    obtain ⟨⟨hmem, hproper⟩, h0, h1⟩ := hf
    rw [isProperColoring_completeBipartiteGraph_iff] at hproper
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_sdiff, Finset.mem_insert,
      Finset.mem_singleton, not_or]
    exact fun w => ⟨hmem _, fun hc => hproper 0 w (h0 ▸ hc.symm),
      fun hc => hproper 1 w (h1 ▸ hc.symm)⟩
  · intro g hg
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_sdiff, Finset.mem_insert,
      Finset.mem_singleton, not_or] at hg
    simp only [Finset.mem_coe, Finset.mem_filter, mem_colorings, Prod.mk.injEq]
    refine ⟨⟨?_, ?_⟩, rfl, rfl⟩
    · rintro (i | w)
      · fin_cases i
        · exact ha
        · exact hb
      · exact (hg w).1
    · rw [isProperColoring_completeBipartiteGraph_iff]
      intro i w
      fin_cases i
      · exact fun hc => (hg w).2.1 hc.symm
      · exact fun hc => (hg w).2.2 hc.symm
  · intro f hf
    simp only [Finset.mem_coe, Finset.mem_filter, Prod.mk.injEq] at hf
    funext v
    rcases v with i | w
    · fin_cases i
      · exact hf.2.1.symm
      · exact hf.2.2.symm
    · rfl
  · intro g _
    funext w
    rfl

/-- A coloring of `K₂,W` is a choice of the two colors on the small side followed by independent
choices on all vertices of `W`, avoiding those two colors. -/
theorem col_completeBipartite_two_right (L : ListAssignment (Fin 2 ⊕ W)) :
    (completeBipartiteGraph (Fin 2) W).col L
      = ∑ a ∈ L (Sum.inl 0), ∑ b ∈ L (Sum.inl 1),
          ∏ w : W, (L (Sum.inr w) \ {a, b}).card := by
  have hfib : ∀ f ∈ (completeBipartiteGraph (Fin 2) W).colorings L,
      (f (Sum.inl 0), f (Sum.inl 1)) ∈ L (Sum.inl 0) ×ˢ L (Sum.inl 1) := by
    intro f hf
    exact Finset.mem_product.mpr ⟨mem_list_of_mem_colorings hf _, mem_list_of_mem_colorings hf _⟩
  rw [col, Finset.card_eq_sum_card_fiberwise hfib, Finset.sum_product]
  exact Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb =>
    card_filter_completeBipartite_two_right ha hb

end Formula

/-! ## A finite ordering certificate for degeneracy -/

section Degeneracy

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A finite graph is `d`-degenerate when it has a construction ordering in which every vertex
has at most `d` earlier neighbours.  Reversing the ordering gives the usual elimination-order
definition. -/
def IsDegenerateAtMost (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : Prop :=
  ∃ rank : V → ℕ, Function.Injective rank ∧
    ∀ v, ((G.neighborFinset v).filter fun w => rank w < rank v).card ≤ d

end Degeneracy

/-! ## The counterexample -/

namespace K2_26

/-- `K₂,₂₆`, on `Fin 2 ⊕ Fin 26`. -/
abbrev G : SimpleGraph (Fin 2 ⊕ Fin 26) := completeBipartiteGraph (Fin 2) (Fin 26)

/-- The explicit four-list assignment from the balanced `K₂,n` construction. -/
def badList : ListAssignment (Fin 2 ⊕ Fin 26) :=
  Sum.elim
    (fun i => if i = 0 then {0, 1, 2, 3} else {0, 1, 4, 5})
    (fun j =>
      if j.val < 6 then {0, 1, 2, 4}
      else if j.val < 13 then {0, 1, 2, 5}
      else if j.val < 20 then {0, 1, 3, 4}
      else {0, 1, 3, 5})

/-- Every list in `badList` has four colors. -/
theorem isNListAssignment_badList : IsNListAssignment badList 4 := by
  rintro (i | j)
  · fin_cases i <;> decide
  · fin_cases j <;> decide

/-- The exact number of colorings from the bad list assignment. -/
theorem col_badList : G.col badList = 9925029789650 := by
  rw [col_completeBipartite_two_right]
  decide

/-- The exact number of ordinary four-colorings of `K₂,₂₆`. -/
theorem colConst_four : G.colConst 4 = 10168268619684 := by
  rw [colConst, col_completeBipartite_two_right]
  decide

/-- **The counterexample:** `K₂,₂₆` is not enumeratively chromatic-choosable at four. -/
theorem not_eccAt_four : ¬ G.ECCAt 4 := by
  intro h
  have hle := h badList isNListAssignment_badList
  rw [colConst_four, col_badList] at hle
  omega

/-- An ordering witnessing 2-degeneracy: put the two-vertex side first, followed by the other
side. -/
def rank : Fin 2 ⊕ Fin 26 → ℕ
  | Sum.inl i => i.val
  | Sum.inr j => 2 + j.val

theorem rank_injective : Function.Injective rank := by decide

/-- `K₂,₂₆` is 2-degenerate. -/
theorem isDegenerateAtMost_two : IsDegenerateAtMost G 2 := by
  refine ⟨rank, rank_injective, ?_⟩
  decide

/-- The proposed universal statement for 2-degenerate graphs at list size four is false. -/
theorem not_every_twoDegenerate_eccAt_four :
    ¬ (∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (H : SimpleGraph V)
        (_ : DecidableRel H.Adj), IsDegenerateAtMost H 2 → H.ECCAt 4) := by
  intro h
  exact not_eccAt_four (h (Fin 2 ⊕ Fin 26) inferInstance inferInstance G inferInstance
    isDegenerateAtMost_two)

end K2_26
end TwoDegenerate
end SimpleGraph

#print axioms SimpleGraph.TwoDegenerate.K2_26.not_eccAt_four
#print axioms SimpleGraph.TwoDegenerate.K2_26.isDegenerateAtMost_two
#print axioms SimpleGraph.TwoDegenerate.K2_26.not_every_twoDegenerate_eccAt_four
