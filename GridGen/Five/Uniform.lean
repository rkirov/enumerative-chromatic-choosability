/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.Relabel

/-!
# Height five: the uniform transfer at `k = 6`, by orbit counts

For each of the fifteen canonical patterns `c` (`canons`), the uniform successors of `c` — the
proper colourings from the lists `{0, …, 5} ∖ {cᵢ}` — are counted by the orbit of their pattern
(`cntU c o`). The counts depend only on the orbit of `c`, and they are the rows of the reduced
transfer matrix `Vmat` of `ai_research_notes/h5k6/pat.py` (`reduced(5, 6)`, orbit numbering of
`GridGen/Five/Defs.lean`): `cntU_canons`, one kernel evaluation over the fifteen patterns.
Each row sums to the number of uniform successors, from `1597` (`01010`) down to `1539`
(`01201`).
-/

namespace GridGen.Five

open Finset

/-- The reduced uniform transfer at `k = 6`: `Vmat i j` is the number of uniform successors in
orbit `j` of a column in orbit `i`. -/
def Vmat : Fin 11 → Fin 11 → ℕ :=
  ![![21, 136, 68, 104, 336, 36, 240, 68, 156, 168, 264],
    ![17, 126, 56, 98, 312, 43, 273, 55, 174, 138, 288],
    ![17, 112, 71, 110, 348, 39, 252, 56, 132, 174, 270],
    ![13, 98, 55, 114, 309, 55, 312, 43, 138, 135, 288],
    ![14, 104, 58, 103, 323, 46, 286, 46, 144, 142, 298],
    ![9, 86, 39, 110, 276, 71, 348, 42, 135, 135, 288],
    ![10, 91, 42, 104, 286, 58, 325, 45, 142, 142, 298],
    ![17, 110, 56, 86, 276, 42, 270, 71, 174, 174, 288],
    ![13, 116, 44, 92, 288, 45, 284, 58, 181, 144, 298],
    ![14, 92, 58, 90, 284, 45, 284, 58, 144, 181, 298],
    ![11, 96, 45, 96, 298, 48, 298, 48, 149, 149, 309]]

/-- The fifteen canonical patterns. -/
def canons : List T5 :=
  [(0, 1, 0, 1, 0), (0, 1, 0, 1, 2), (0, 1, 0, 2, 0), (0, 1, 0, 2, 1), (0, 1, 0, 2, 3),
    (0, 1, 2, 0, 1), (0, 1, 2, 0, 2), (0, 1, 2, 0, 3), (0, 1, 2, 1, 0), (0, 1, 2, 1, 2),
    (0, 1, 2, 1, 3), (0, 1, 2, 3, 0), (0, 1, 2, 3, 1), (0, 1, 2, 3, 2), (0, 1, 2, 3, 4)]

/-- The number of uniform successors of `c` at `k = 6` whose pattern lies in orbit `o`. -/
def cntU (c : T5) (o : Fin 11) : ℕ :=
  ((sts ((range 6).erase (r1 c)) ((range 6).erase (r2 c)) ((range 6).erase (r3 c))
    ((range 6).erase (r4 c)) ((range 6).erase (r5 c))).filter (fun t => orb t = o)).card

/-- **The uniform orbit counts at `k = 6`**, for all fifteen canonical patterns. -/
theorem cntU_canons : ∀ c ∈ canons, cntU c = Vmat (orb c) := by
  decide +kernel

/-- The canonical realisation of a proper column is one of the fifteen canonical patterns. -/
theorem canon_mem {s : T5} (hs : Proper s) : canon s ∈ canons := by
  obtain ⟨p1, p2, p3, p4⟩ := hs
  unfold canon canons
  simp only [r1, r2, r3, r4, r5] at *
  split_ifs <;> simp_all

end GridGen.Five
