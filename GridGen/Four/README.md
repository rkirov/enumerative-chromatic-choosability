# `GridGen/Four/`: height-four grids at `k ≥ 7`

**`GridGen.Four.ecc_boxProd_pathG_three`**: for every `k ≥ 7` and every `n`,
`(pathG 3 □ pathG n).ECCAt k`, i.e. every `4 × (n+1)` grid is ECC at list size `k`. The axioms
are `[propext, Classical.choice, Quot.sound]` (`GridGen/PolymerAxiomAudit.lean`, comparator §17).
For `k ≥ 8` this is the gauge route's `ListColoring.ecc_boxProd_pathG_of_eight`. The new case is
`k = 7`; `3 ≤ k ≤ 6` remains open. (The certificates below once covered `8 ≤ k ≤ 15`, when the
other route stopped at `16`; they were removed on 2026-10-17 and 2026-10-18 as the gauge route
reached `9` and then `8`.)

## Route

GridGen's telescoping (`GridGen/Explicit.lean`) needs, for the row graph `pathG 3`, an explicit
two-step inequality, a first-seam inequality and an initial inequality.

1. **Reduction to two inequalities** (`Statement`, `Relabel`, `Cone`, `Bridge`, `Final`). The
   uniform pattern futures of a four-row column are `vA · gw (nextW k w)`: five patterns (`0101`,
   `0102`/`0121`, `0120`, `0123`) weighted by `w = (a, b, c)` relative to `0101`. The box
   `ρ ≤ a, b, c ≤ 1`, `ρ = 1 − 2/(k−2)³`, is mapped into itself by the uniform transfer for every
   `k ≥ 5` (`nextW_inBox`). Hence every horizon follows from `Seam4Holds k` (for every weight in
   the box: the uniform successor weights of the previous columns `s ∈ sts X` are at most the
   actual ones in the next lists `B`) and `Init4Holds k` (`ecc_pathG_three_of_holds`).
2. **The initial inequality** (`Init`), for every `k ≥ 7`.
3. **One previous column** (`Local`, `LogBounds`, `CountBound`, `Palette`, `Pattern`, `State`).
   With `Aᵢ = Bᵢ.erase sᵢ`, the count `|sts A|` is a product of four row rates. Each rate's log is
   bounded against the uniform rate by a main term `log (1 + μᵢ/A)` (with `μᵢ = k − |Bᵢ₋₁ ∩ Bᵢ|`),
   state-bit losses `zᵢ`, bonuses `hᵢ = [sᵢ ∉ Bᵢ]`, and one-sided errors in rows three and four
   (`count_log_bound`). The pattern term is compared with a reference palette next to `B₂`
   (`exists_palette`, `pattern_log_ge`), and is never below `log ρ`. Together: `GB ≥ GU · (1 + Λ)`
   (`state_bound`, and `state_bound_cap` with the pattern term capped at `(1−ρ)/ρ`).
4. **Averaging** (`Fibre`, `Seam`). Any two uniform weights `GU` are within `1/ρ`, so a row pinned
   to a colour set `D` by the other rows carries at most `|D|/(ρ(k−3))` of the weight. This turns
   `Σ GU · Λ` into `(Σ GU) · Fval k μ₂ μ₃ μ₄`, or `Fcap` with the cap (`seam_of_cert`).
5. **The averaged gain** (`Cert`): `Fval` and the capped `Fcap`, as functions of the three
   mismatches.
6. **`k = 7`** (`Cert7`, `Exact`, `Small7`, `Seam7`). `Fcap` holds at 506 of the 512 integer
   mismatch triples (`cert7`, smallest value about `3.6·10⁻⁴`); `(0,0,0)` uses `Fval`. The five
   remaining triples, `(0,1,0)`, `(1,0,0)`, `(0,0,1)`, `(0,1,1)`, `(0,2,0)`, force the lists into
   eight shapes up to relabelling. For a state `s`, every intersection of the lists `Bᵢ.erase sᵢ` is
   the corresponding intersection of the `Bᵢ` minus the distinct `sᵢ` in it, so `GB` and `GU` are
   explicit integer functions of the Venn sizes, the membership bits `[sᵢ ∈ Bⱼ]` and the pattern
   bits (`dat_eq`, `GB_cls`, `GU_urow`). For each shape a `Spec` gives multipliers for pins (a row
   in a small atom, `s₁ = s₃`, `s₂ = s₄`); `allOk` checks `(1 − y)·GB ≥ GU` on the whole box for
   every column type by kernel evaluation (464 to 1980 types per shape), and `specOk` that the
   averaged gain is nonnegative (`exact_seam`).

At `k = 6` the step-3 bounds fail at 101 of the 342 nonzero mismatch triples, too many to certify
exactly this way. With exact per-state values the averaged inequality still held in the list
configurations we tested at `k = 6` (smallest margin about `0.009`, at `(0,1,0)`), but it fails at
`k = 5` (about `−0.019` at `(0,1,0)`), so `k = 5` needs a different argument.

## Credits

The reduction to the box, the row-rate localisation, the palette form of the pattern term, the
initial inequality, the vertex certificate, the `k = 7` cap and exact certificates, and the Lean
development are this repository's (Claude). Codex (OpenAI), consulted on 2026-10-15
(`ai_research_notes/CODEX_H4_SEAM_BOUNDS_2026-10-15.md`), supplied the symbolic box `ρ`, the
one-sided row-three and row-four error bounds, and the defect-free tail that replaces strict
three-row locality. See `provenance.md`.

## Build

`lake build GridGen.Four.Main`. The numerical lemmas (`LogBounds`, `Cert`, `Cert7`, `Seam`) and
the kernel checks of `Small7` (about 80 s, 0.7 GB above the import baseline) take a few minutes in
total.
