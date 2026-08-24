import Mathlib.Combinatorics.SimpleGraph.Prod
import ListColoring.Defs

/-!
# Decidable adjacency in a Cartesian product

Mathlib does not supply `DecidableRel (G □ H).Adj` at the pinned revision, and none of `col`,
`colConst` or `ECCAt` can be stated for a product without it. It lives here, in the library, so
that both `OpenProblems.lean` — which states Kirov–Naimi §6 Question 1 about products — and
`Ladder/` — which proves its height-two case for paths — can use it without either importing the
other.
-/

namespace SimpleGraph

/-- Adjacency in a Cartesian product is decidable when it is decidable in both factors and both
vertex types have decidable equality. -/
instance instDecidableRelBoxProd {α β : Type*} [DecidableEq α] [DecidableEq β]
    (G : SimpleGraph α) [DecidableRel G.Adj] (H : SimpleGraph β) [DecidableRel H.Adj] :
    DecidableRel (G □ H).Adj :=
  fun _ _ => decidable_of_iff' _ boxProd_adj

end SimpleGraph
