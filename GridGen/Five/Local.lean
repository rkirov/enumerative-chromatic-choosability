/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.Relabel
import GridGen.Four.Local

/-!
# Height five: the local data of a column against the next lists

For a column `s` and next lists `B₁, …, B₅` of `k` colours, the successor lists are
`Aᵢ = Bᵢ.erase sᵢ`. The local data of a pair of consecutive rows are those of
`GridGen/Four/Local.lean`, which is stated for lists and applies unchanged: the bonus
`Four.hb B c`, the mismatch `Four.mu k B C = k − |B ∩ C|`, the difference-set bits `Four.zz`, and
the size of a consecutive intersection of punctured lists (`Four.card_inter_erase`,
`|Aⱼ₋₁ ∩ Aⱼ| = k − μⱼ − 2 + hⱼ₋₁ + hⱼ + zⱼ`).

This file adds what is specific to five rows:

* the exact count of a five-row column, by inclusion–exclusion over the four consecutive
  intersections (`card_sts_formula`; sixteen terms);
* monotonicity of the count in the lists (`card_sts_mono`);
* the bound `|Aⱼ₋₁ ∩ Aⱼ| ≤ |Bⱼ₋₁ ∩ Bⱼ| = k − μⱼ` (`card_inter_erase_le`,
  `card_inter_erase_le_mu`; `ai_research_notes/H5_K6_ANALYTIC_2026-10-23.md` §1.1);
* a list punctured at all the colours of a column (`card_inter_erase_rowSet`).
-/

namespace GridGen.Five

open Finset

/-- **The exact count of a five-row column**, by inclusion–exclusion over the consecutive
intersections. -/
theorem card_sts_formula (A B C D E : Finset ℕ) :
    ((sts A B C D E).card : ℤ) =
      A.card * B.card * C.card * D.card * E.card
        - (A ∩ B).card * C.card * D.card * E.card - A.card * (B ∩ C).card * D.card * E.card
        - A.card * B.card * (C ∩ D).card * E.card - A.card * B.card * C.card * (D ∩ E).card
        + (A ∩ B ∩ C).card * D.card * E.card + (A ∩ B).card * (C ∩ D).card * E.card
        + (A ∩ B).card * C.card * (D ∩ E).card + A.card * (B ∩ C ∩ D).card * E.card
        + A.card * (B ∩ C).card * (D ∩ E).card + A.card * B.card * (C ∩ D ∩ E).card
        - (A ∩ B ∩ C ∩ D).card * E.card - (A ∩ B ∩ C).card * (D ∩ E).card
        - (A ∩ B).card * (C ∩ D ∩ E).card - A.card * (B ∩ C ∩ D ∩ E).card
        + (A ∩ B ∩ C ∩ D ∩ E).card := by
  rw [card_sts, Four.card_sts_formula, Four.card_sts_formula]
  ring

/-- The number of proper colourings is monotone in the lists. -/
theorem card_sts_mono {A B C D E A' B' C' D' E' : Finset ℕ} (hA : A ⊆ A') (hB : B ⊆ B')
    (hC : C ⊆ C') (hD : D ⊆ D') (hE : E ⊆ E') :
    (sts A B C D E).card ≤ (sts A' B' C' D' E').card := by
  refine Finset.card_le_card fun t ht => ?_
  rw [mem_sts] at ht ⊢
  obtain ⟨h1, h2, h3, h4, h5, p⟩ := ht
  exact ⟨hA h1, hB h2, hC h3, hD h4, hE h5, p⟩

/-- Consecutive punctured lists share at most what the lists share. -/
theorem card_inter_erase_le (B C : Finset ℕ) (a b : ℕ) :
    ((B.erase a) ∩ (C.erase b)).card ≤ (B ∩ C).card :=
  Finset.card_le_card (Finset.inter_subset_inter (Finset.erase_subset a B)
    (Finset.erase_subset b C))

/-- **`|Aⱼ₋₁ ∩ Aⱼ| ≤ k − μⱼ`**, in the terms of `GridGen/Four/Local.lean`. -/
theorem card_inter_erase_le_mu (k : ℕ) (B C : Finset ℕ) (a b : ℕ) :
    (((B.erase a) ∩ (C.erase b)).card : ℝ) ≤ (k : ℝ) - Four.mu k B C := by
  unfold Four.mu
  have : (((B.erase a) ∩ (C.erase b)).card : ℝ) ≤ (B ∩ C).card := by
    exact_mod_cast card_inter_erase_le B C a b
  linarith

/-- A list punctured at all the colours of a column whose colours it contains. -/
theorem card_inter_erase_rowSet {k : ℕ} {B : Finset ℕ} (hB : B.card = k) {s : T5}
    (hs : RowsIn s B) :
    ((B.erase (r1 s)) ∩ (B.erase (r2 s)) ∩ (B.erase (r3 s)) ∩ (B.erase (r4 s))
      ∩ (B.erase (r5 s))).card = k - (rowSet s).card := by
  have hset : (B.erase (r1 s)) ∩ (B.erase (r2 s)) ∩ (B.erase (r3 s)) ∩ (B.erase (r4 s))
      ∩ (B.erase (r5 s)) = B \ rowSet s := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_sdiff, rowSet, Finset.mem_insert,
      Finset.mem_singleton]
    tauto
  have hsub : rowSet s ⊆ B := by
    intro x hx
    simp only [rowSet, Finset.mem_insert, Finset.mem_singleton] at hx
    obtain ⟨h1, h2, h3, h4, h5⟩ := hs
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  rw [hset, Finset.card_sdiff_of_subset hsub, hB]

end GridGen.Five
