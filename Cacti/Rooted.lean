/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Cacti.Defs

/-!
# Rooted coloring counts

The cactus induction (handoff §4) passes **rooted profiles** up a decomposition: for a rooted
graph, the vector of counts of proper `L`-colorings taking each colour at the root. This file
defines rooted counts and proves the one fact every layer consumes:

* `col_eq_sum_rootedCol` — the total count is the sum of the rooted counts over the root's list.

The weighted refinement is `rootedWcol` in `Cacti/Weighted.lean`; the block induction never
composes bare rooted counts across a cut, only weighted ones, and it does that by absorbing one
side into the weight at the cut vertex (`rootedWcol_absorb`, `Cacti/Absorb.lean`).
-/

namespace ListColoring

open SimpleGraph Finset

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The **rooted count**: proper `L`-colorings of `G` giving colour `c` to the root `r`. -/
def rootedCol (L : ListAssignment V) (r : V) (c : ℕ) : ℕ :=
  ((G.colorings L).filter (fun f => f r = c)).card

/-- The total count partitions over the root's list. -/
theorem col_eq_sum_rootedCol (L : ListAssignment V) (r : V) :
    G.col L = ∑ c ∈ L r, rootedCol G L r c :=
  Finset.card_eq_sum_card_fiberwise fun f hf => G.mem_list_of_mem_colorings hf r

end ListColoring
