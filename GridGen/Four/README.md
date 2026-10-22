# `GridGen/Four/`: height-four grids at `k ≥ 6`

**`GridGen.Four.ecc_boxProd_pathG_three`**: for every `k ≥ 6` and every `n`,
`(pathG 3 □ pathG n).ECCAt k`, i.e. every `4 × (n+1)` grid is ECC at list size `k`. The axioms
are `[propext, Classical.choice, Quot.sound]` (`GridGen/PolymerAxiomAudit.lean`, comparator §17).
For `k ≥ 7` this is the gauge route's `ListColoring.ecc_boxProd_pathG_of_seven`. The new case is
`k = 6` (2026-10-21); `3 ≤ k ≤ 5` remains open. (The certificates below once covered
`7 ≤ k ≤ 15`, when the other route stopped at `16`; they were removed on 2026-10-17, 2026-10-18
and 2026-10-22 as the gauge route reached `9`, `8` and then `7`.)

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
2. **The initial inequality** (`Init`), with the box edge `487/500`, at `k = 6`
   (`init4Holds_six`).
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
6. **Exact certificates** (`Exact`). For a state `s`, every intersection of the lists
   `Bᵢ.erase sᵢ` is the corresponding intersection of the `Bᵢ` minus the distinct `sᵢ` in it, so
   `GB` and `GU` are explicit integer functions of the Venn sizes, the membership bits `[sᵢ ∈ Bⱼ]`
   and the pattern bits (`dat_eq`, `GB_cls`, `GU_urow`). For a list shape a `Spec` gives
   multipliers for pins (a row in a small atom, `s₁ = s₃`, `s₂ = s₄`); a kernel evaluation checks
   `(1 − y)·GB ≥ GU` on the whole box for every column type, and that the averaged gain is
   nonnegative.
7. **`k = 6`** (`CountBound6`, `Fibre6`, `State6`, `Seam6`, `Cert6`, `Exact6`, `Small6`, `Six`).
   The step-3 and step-4 bounds above fail at 101 of the 342 nonzero mismatch triples. Seven
   sharpenings bring that to sixteen:
   * the box edge `ρ = 487/500` (`rho_six`, `box_six`; `488/500` is not invariant);
   * sharp fibre bounds: a row with `m` free options carries at most `1/(1 + (m−1)ρ)` per colour
     (`fibre_row_sharp`), `250/737` on the middle rows;
   * the end rows separately: they have one more option, so `500/1961`, and `c₁₃`, `c₂₄` are
     pinned through them;
   * pinned sums capped at the whole weight, `min(q|D|, 1)`;
   * the row-three and row-four errors in `e`-min form (`rate3_err_emin`, `rate4_err_emin`);
   * the chord of the logarithm for the state-bit loss (`zslope`, `log_chord`);
   * a pattern lemma (`pattern_six`): the uniform class frequencies of a column with lists of size
     at least `5`, against the box corners, cap the pattern term at `209/14123` (about `0.55` of
     `(1−ρ)/ρ`).
   `F6cap` then holds at the other 326 triples (`cert6`, smallest value about `1.6·10⁻³`, at
   `(1,2,1)`; the chord slope is bounded through `log (1+y) ≤ y − y²/2 + y³/3`), and `(0,0,0)` uses
   `F6val`. The sixteen triples (`ExactTriple6`) force 69 list shapes (`dispatch6`, a kernel
   enumeration of the atom-size equations); `Exact6` generalises `Exact` to atom sizes with a
   capacity filter, and `Small6/Cert*.lean` check 79,439 column types (smallest LP margin
   `0.009`, at `(0,1,0)`).

With exact per-state values the averaged inequality fails at `k = 5` (about `−0.019` at
`(0,1,0)`), so `k = 5` needs a different argument.

## Credits

The reduction to the box, the row-rate localisation, the palette form of the pattern term, the
initial inequality, the vertex certificate, the exact-certificate method, the `k = 6`
sharpenings, pattern lemma and certificates (2026-10-21), and the Lean development are this
repository's (Claude). Codex (OpenAI), consulted on 2026-10-15
(`ai_research_notes/CODEX_H4_SEAM_BOUNDS_2026-10-15.md`), supplied the symbolic box `ρ`, the
one-sided row-three and row-four error bounds, and the defect-free tail that replaces strict
three-row locality. See `provenance.md`.

## Build

`lake build GridGen.Four.Main`. The numerical lemmas (`LogBounds`, `Cert`, `Seam`, `Cert6`) take a
few minutes. The `k = 6` exact certificates dominate: eleven modules `Small6/Cert*.lean` of about
2 minutes each (about 15 ms per column type, about 1 GB above the import baseline). The
multipliers come from a linear program (`ai_research_notes/h4k6/gen6lean.py`, not tracked), but
only the kernel checks matter.
