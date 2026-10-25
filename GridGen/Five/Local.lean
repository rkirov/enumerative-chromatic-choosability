/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.Relabel

/-!
# Height five: the local data of a column against the next lists

For a column `s` and next lists `B₁, …, B₅` of `k` colours, the successor lists are
`Aᵢ = Bᵢ.erase sᵢ`. The local data of a pair of consecutive rows are those of
`GridGen/Lookback/Common.lean`, which is stated for lists and serves every height: the bonus
`Lookback.hb B c`, the mismatch `Lookback.mu k B C = k − |B ∩ C|`, the difference-set bits
`Lookback.zz`, and the size of a consecutive intersection of punctured lists
(`Lookback.card_inter_erase`, `|Aⱼ₋₁ ∩ Aⱼ| = k − μⱼ − 2 + hⱼ₋₁ + hⱼ + zⱼ`).

This file adds what is specific to five rows: the exact count of a five-row column, by
inclusion–exclusion over the four consecutive intersections (`card_sts_formula`; sixteen terms).
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

end GridGen.Five
