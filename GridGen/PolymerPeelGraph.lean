/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.PolymerPeel
import GridGen.PolymerBlockEdges

/-!
# Connected blocks can be peeled outward

In a graph of maximum degree `D`, call a vertex *small* in a set `C` when it has at most `D - 1`
neighbours in `C`. If `T` spans a block `S` connected (`ConnectedOn T S`), then starting from any
nonempty part `R` of `S` already deleted, the rest of `S` can be deleted one vertex at a time,
each vertex small when it goes: it always has a neighbour in the deleted part, by connectivity.
-/

namespace GridGen.Polymer

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `u` has at most `d` neighbours in `C`. -/
def smallIn (d : ℕ) (C : Finset V) (u : V) : Prop := (C.filter (G.Adj u)).card ≤ d

/-- A spanning connected edge set crosses every proper nonempty cut of its block. -/
theorem exists_cross_of_mem_blockEdgeSets {S : Finset V} {T : Finset (Sym2 V)}
    (hT : T ∈ blockEdgeSets G S) {R : Finset V} (hRS : R ⊆ S) (hR : R.Nonempty)
    (hne : ¬ S ⊆ R) : ∃ u ∈ S, u ∉ R ∧ ∃ r ∈ R, G.Adj u r := by
  classical
  rw [mem_blockEdgeSets] at hT
  obtain ⟨hTsub, hconn⟩ := hT
  obtain ⟨r, hr⟩ := hR
  obtain ⟨s, hsS, hsR⟩ := Finset.not_subset.mp hne
  obtain ⟨p⟩ := hconn.2 r (hRS hr) s hsS
  obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart (R : Set V) (by simpa using hr)
    (by simpa using hsR)
  have hadj := d.adj
  simp only [SimpleGraph.fromEdgeSet_adj, Finset.mem_coe] at hadj
  have hmem : s(d.fst, d.snd) ∈ edgesWithin G.edgeFinset S := hTsub hadj.1
  rw [mem_edgesWithin] at hmem
  refine ⟨d.snd, hmem.2 _ (Sym2.mem_mk_right _ _), by simpa using hd2, d.fst, by simpa using hd1, ?_⟩
  exact (G.mem_edgeFinset.mp hmem.1).symm

/-- **Peeling a connected block.** With `R ⊆ S` nonempty already deleted from `U`, the rest of the
block is deleted from `U ∖ R` one small vertex at a time. -/
theorem peelChain_of_mem_blockEdgeSets {D : ℕ} (hdeg : ∀ v, G.degree v ≤ D)
    {S : Finset V} {T : Finset (Sym2 V)} (hT : T ∈ blockEdgeSets G S) (U : Finset V) :
    ∀ R : Finset V, R ⊆ S → R.Nonempty →
      PeelChain (smallIn G (D - 1)) (U \ R) (U \ S) := by
  classical
  intro R
  induction hn : (S \ R).card generalizing R with
  | zero =>
    intro hRS _
    have hSR : S ⊆ R := by
      intro x hx
      by_contra h
      have : x ∈ S \ R := Finset.mem_sdiff.mpr ⟨hx, h⟩
      rw [Finset.card_eq_zero] at hn
      rw [hn] at this
      exact Finset.notMem_empty x this
    rw [Finset.Subset.antisymm hRS hSR]
    exact PeelChain.refl _
  | succ m ih =>
    intro hRS hR
    have hne : ¬ S ⊆ R := by
      intro h
      have : (S \ R).card = 0 := by rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset]; exact h
      omega
    obtain ⟨u, huS, huR, r, hrR, hur⟩ := exists_cross_of_mem_blockEdgeSets G hT hRS hR hne
    by_cases huU : u ∈ U
    · refine PeelChain.step (u := u) (Finset.mem_sdiff.mpr ⟨huU, huR⟩) ?_ ?_
      · -- `u` has lost its neighbour `r`
        unfold smallIn
        have hsub : (U \ R).filter (G.Adj u) ⊆ (G.neighborFinset u).erase r := by
          intro y hy
          obtain ⟨hyUR, hyu⟩ := Finset.mem_filter.mp hy
          refine Finset.mem_erase.mpr ⟨?_, (G.mem_neighborFinset u y).mpr hyu⟩
          rintro rfl
          exact (Finset.mem_sdiff.mp hyUR).2 hrR
        have hcard := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem ((G.mem_neighborFinset u r).mpr hur),
          G.card_neighborFinset_eq_degree] at hcard
        have := hdeg u
        omega
      · have heq : (U \ R).erase u = U \ insert u R := by
          ext y; simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert]; tauto
        rw [heq]
        apply ih (insert u R)
        · have h1 : S \ insert u R = (S \ R).erase u := by
            ext y; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]; tauto
          rw [h1, Finset.card_erase_of_mem (Finset.mem_sdiff.mpr ⟨huS, huR⟩), hn]
          rfl
        · exact Finset.insert_subset huS hRS
        · exact Finset.insert_nonempty u R
    · -- `u` is not in `U` at all: count it as deleted without a step
      have heq : U \ R = U \ insert u R := by
        ext y; simp only [Finset.mem_sdiff, Finset.mem_insert]
        constructor
        · rintro ⟨hy, hyR⟩; exact ⟨hy, fun h => h.elim (fun h => huU (h ▸ hy)) hyR⟩
        · rintro ⟨hy, hyR⟩; exact ⟨hy, fun h => hyR (Or.inr h)⟩
      rw [heq]
      apply ih (insert u R)
      · have h1 : S \ insert u R = (S \ R).erase u := by
          ext y; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]; tauto
        rw [h1, Finset.card_erase_of_mem (Finset.mem_sdiff.mpr ⟨huS, huR⟩), hn]
        rfl
      · exact Finset.insert_subset huS hRS
      · exact Finset.insert_nonempty u R

end GridGen.Polymer
