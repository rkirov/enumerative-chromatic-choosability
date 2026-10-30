import ListColoring
import Cacti
import NonPersistence
import Ladder
import Grid3
import Grid3.Three.Main
import GridGen.Polymer
import GridGen.Four.Main
import GridGen.Five.Main
import GridGen.Six.Main
import GridGen.Gauge.Seven.Assemble7
import TwoDegenerate
/-!
# Submission: the real development

Section 13 is proved in `GridGen/PeelDegree.lean`: maximum degree four at every list size at
least 16.
Section 14 is proved in `GridGen/MaximumDegree.lean` (the uniform bound `k ≥ ceil(5.67Δ)` for
arbitrary maximum degree), `GridGen/PeelDegree.lean` (subcubic graphs at `k ≥ 11`) and
`GridGen/PolymerStability.lean` (the equality case).
Section 15 is proved in `TwoDegenerate/`: `K₂,₂₆` is not ECC at four
(`TwoDegenerate/Counterexample.lean`), and `K₂,ₙ` at list sizes three, four and five
(`TwoDegenerate/K2n/Main.lean`).
Section 16 is proved in `TwoDegenerate/K2nSqrt/Main.lean`: `K₂,ₙ` is ECC at every `k ≥ 300`
with `n ≤ k²`, so `τ(K₂,ₙ) = O(√n)`.
Section 17 is proved in `GridGen/Four/Main.lean`: every `4 × (n+1)` grid is ECC at every `k ≥ 4`.
Section 20 is proved in `GridGen/Six/Main.lean`: every `6 × (n+1)` grid is ECC at every `k ≥ 6`.
Section 19 is proved in `GridGen/Five/Main.lean`: every `5 × (n+1)` grid is ECC at every `k ≥ 5`.
Section 18 is proved in `GridGen/Gauge/Seven/Assemble7.lean`: every rectangular grid is ECC at every
`k ≥ 7`.

The comparator matches the placeholder statements of `Challenge.lean` against declarations of the
same fully-qualified names in this module's environment. Every one of them is proved in the
`ListColoring` library of this repository (and, for §9, in `Cacti/`; for §10, in
`NonPersistence/`; for §11, in `Ladder/`; for §12, in `Grid3/`, with the list-size-three case in
`Grid3/Three/Main.lean`, which `Grid3.lean` does not import because it rests on the 22,157
kernel-checked seam records of `Grid3/Three/Cert/Data/`), under exactly those names, so importing the libraries is the whole submission — no re-export shim is needed, and none is
wanted: a shim would put a second declaration between the comparator and the thing that was
actually proved.

`config.json` therefore sets `"solution_module": "Submission"`.
-/
