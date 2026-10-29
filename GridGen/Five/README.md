# `GridGen/Five/`: height-five grids at `k ≥ 5`

**`GridGen.Five.ecc_boxProd_pathG_four`**: for every `k ≥ 5` and every `n`,
`(pathG 4 □ pathG n).ECCAt k`, i.e. every `5 × (n+1)` grid is ECC at list size `k`. The axioms
are `[propext, Classical.choice, Quot.sound]` (`GridGen/PolymerAxiomAudit.lean`, comparator §19).
For `k ≥ 7` this is the gauge route's `ListColoring.ecc_boxProd_pathG_of_seven`; the new case is
`k = 6`, and `k = 5` (`K5/`, with its own README: Codex's (OpenAI) cone of five transient rays and a
narrow invariant box). `3 ≤ k ≤ 4` remains open.

## Route

The column-lookback route of [`GridGen/Four/`](../Four/README.md), with five rows.
The model builds on height four's (a five-row column is a colour in front of a four-row column,
`GridGen/Four/Defs.lean`), and the helpers that do not depend on the height (the local data
`hb`, `mu`, `zz`, the counting lemmas, the one-row rate bounds `rate_first` and `rate_main_chord`,
the sharp fibre bound `fibre_row_sharp`) are in
[`GridGen/Lookback/Common.lean`](../Lookback/Common.lean). Nothing else of `GridGen/Four/` is
imported, so `GridGen/Five/` builds without height four's certificates.

1. **Reduction** (`Defs`, `Statement`, `Relabel`, `Uniform`, `Cone`, `Bridge`, `Final`). A
   five-row column has fifteen equality patterns in eleven reflection orbits. Their weights lie
   in a per-pattern box (`InBox5`, lower edges `lo5` from `959/1000` to `1977/2000`, the
   alternating pattern fixed at `1`), which the uniform transfer at `k = 6` maps into itself
   (`nextW_inBox`, a kernel check of the reduced `11 × 11` transfer matrix and 22 corner
   inequalities). Every horizon then follows from `Seam5Holds 6` and `Init5Holds 6`
   (`ecc_pathG_four_of_holds`).
2. **The initial inequality** (`Init5`, `InitCert5`): `|sts X| ≥ 3750 + 120·S` and the pattern
   loss by exact dual certificates at the box corners.
3. **The seam inequality off the exact quads** (`Count5`, `Kappa5a/b`, `State5`, `Chain5`,
   `PatLP5`, `PatCert5`, `Pattern5`, `LogB5`, `Seam5`, `CertF5`, `BitLP5`, `BitCert5`, `Cert5`).
   The mismatches `μⱼ = 6 − |Bⱼ₋₁ ∩ Bⱼ|` form a quad.
   * The successor count is bounded below by a universal constant times the product of the row
     rates, `κ = 123125/128018`, minimised by greedy interval profiles (`kapOK_all`, 49,069
     profiles).
   * The pattern term is bounded by a chain of fibre bounds over the fourteen equality events, with
     exact rational duals at the 1,024 box corners (`pattern5`).
   * Averaging with fibre pins gives the analytic certificate `F5`, nonnegative at 2,338 quads
     (`F5_nonneg`); `(0,0,0,0)` holds by relabelling; 38 quads have dual certificates over the
     state bits (`seam_bit5`).
4. **Exact certificates** (`Exact5`, `Small5/`, `Small5.lean`) for the 24 quads of `Quads.lean`
   (13 up to row reflection, `seam_of_rev`): for each of 58 list shapes a `Spec5` certificate is
   checked over every column type (137,717 in all) by kernel evaluation, and a pruned search
   (`search_sound`) dispatches each quad to its shapes.
5. **Assembly** (`Six`, `Main`): `seam5Holds_six`, `ecc_boxProd_pathG_four`.

## Credits

The height-five box, the count constant, the chain-fibre pattern lemma, the bit-level and exact
certificates and the Lean development are this repository's (Claude, 2026-10-23). They build on
the height-four method, whose credits, including Codex's (OpenAI), are in
[`GridGen/Four/README.md`](../Four/README.md). The research notes are
`ai_research_notes/H5_K6_*_2026-10-23.md` (not tracked). See `provenance.md`.

## Build

`lake build GridGen.Five.Main`. The certificate modules `Small5/Cert0*.lean` take one to two minutes
each and the thirteen dispatch modules `Small5/Disp_*.lean` 10–20 s each, about 20 minutes in all. The largest module needs about 1.2 GB above the import baseline; build them one at a time
on small machines.
