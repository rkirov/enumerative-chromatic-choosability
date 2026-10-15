# `GridGen/Four/`: height-four grids at `k ≥ 8`

**`GridGen.Four.ecc_boxProd_pathG_three`**: for every `k ≥ 8` and every `n`,
`(pathG 3 □ pathG n).ECCAt k`, i.e. every `4 × (n+1)` grid is ECC at list size `k`. The axioms
are `[propext, Classical.choice, Quot.sound]` (`GridGen/PolymerAxiomAudit.lean`, comparator §17).
For `k ≥ 16` this is `ListColoring.ecc_boxProd_pathG_of_sixteen`. The new range is `8 ≤ k ≤ 15`;
`3 ≤ k ≤ 7` remains open.

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
2. **The initial inequality** (`Init`), for every `k ≥ 8`.
3. **One previous column** (`Local`, `LogBounds`, `CountBound`, `Palette`, `Pattern`, `State`).
   With `Aᵢ = Bᵢ.erase sᵢ`, the count `|sts A|` is a product of four row rates. Each rate's log is
   bounded against the uniform rate by a main term `log (1 + μᵢ/A)` (with `μᵢ = k − |Bᵢ₋₁ ∩ Bᵢ|`),
   state-bit losses `zᵢ`, bonuses `hᵢ = [sᵢ ∉ Bᵢ]`, and one-sided errors in rows three and four
   (`count_log_bound`). The pattern term is compared with a reference palette next to `B₂`
   (`exists_palette`, `pattern_log_ge`). Together: `GB ≥ GU · (1 + Λ)` (`state_bound`).
4. **Averaging** (`Fibre`, `Seam`). Any two uniform weights `GU` are within `1/ρ`, so a row pinned
   to a colour set `D` by the other rows carries at most `|D|/(ρ(k−3))` of the weight. This turns
   `Σ GU · Λ` into `(Σ GU) · Fval k μ₂ μ₃ μ₄` (`seam4Holds`).
5. **Certificate** (`Cert`). `Fval` is bounded below by a polynomial that, on each region where
   the mismatch indicators are constant, is concave in each `μᵢ` separately. Its minimum over a box
   is therefore at a vertex; fourteen vertex values per `k = 8, …, 15` are checked by `norm_num`.
   The smallest margin is at `(μ₂, μ₃, μ₄) = (0, 1, 0)`, `k = 8`, about `0.0013`.

At `k = 7` the certificate is negative at some vertices, so these bounds stop at `8`; the seam
inequality itself held in numerical checks at `k = 5, 6, 7`.

## Credits

The reduction to the box, the row-rate localisation, the palette form of the pattern term, the
initial inequality, the vertex certificate and the Lean development are this repository's (Claude).
Codex (OpenAI), consulted on 2026-10-15
(`ai_research_notes/CODEX_H4_SEAM_BOUNDS_2026-10-15.md`), supplied the symbolic box `ρ`, the
one-sided row-three and row-four error bounds, and the defect-free tail that replaces strict
three-row locality. See `provenance.md`.

## Build

`lake build GridGen.Four.Main` (the per-`k` numerical lemmas in `LogBounds`, `Cert` and `Seam` take
about a minute in total).
