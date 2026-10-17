# `GridGen/Gauge/` — every grid is `k`-ECC for `k ≥ 9`

`ListColoring.ecc_boxProd_pathG_of_nine : 9 ≤ k → (pathG r □ pathG n).ECCAt k`, for every height
and width. For `k ≥ 10` the proof uses the generic constants of `Seam.lean` (`ecc_rowG_boxProd`),
and for `k = 9` the sharper ones of `Nine/`. It is complete (no unproved steps), its axioms are
`[propext, Classical.choice, Quot.sound]`, and the comparator claims it (§18).

## The argument

GridGen's column telescope compares the actual chain of list columns with uniform futures through
a *reference*. The older references ranked colours by value (`patCap`). Their errors were not
local, and the weights they average were not a Gibbs measure.

Here the reference is a *gauge*. Each column's rows get bijections from their lists onto
`{0, …, k-1}` that are vertically consistent (VC): a colour shared by adjacent rows gets one label.
The telescoped quantity is

  `W j = ∑_{s ∈ column j} vec j s · F_{n-j}(gauge j ∘ s)`.

That is the number of correspondence (DP) colourings of an explicit cover of the whole grid.

* `W 0` is at least the uniform count: a VC labelling pulls uniform states back (`init_le`).
* `W n` is the list count.
* Each seam satisfies `W j ≤ W (j+1)` (`W_le_succ`):
  * **Stage (a).** The new column maps onto uniform states by its gauge (`stage_a`).
  * **Stage (b).** Expand the chain one or two columns back into *slabs*: a past column, the seam
    column, and the future (`Slab.lean`, `stage_b`). On each slab the old gauge's seam keys become
    the new gauge's keys in two phases (`slab_core`):
    * **Stars** (`Star.lean`, `Box.lean`). Each colour leaving its row deletes one seam pair. A
      fibre-by-fibre bound on the 2 + 6 cells around the pair shows that a
      `γ_k = (k-4)²(k-5)²/(k²(k-3)⁴)` fraction of solutions realizes the new pair.
    * **Moves** (`Kempe.lean`, `Bad.lean`, `Paths.lean`). The new gauge is glued from the old one
      by at most `2H` label transpositions on the rows below a row edge (`Labelling.lean`; `H` is
      the number of stars). A transposition loses at most the solutions in which an `x/y`-coloured
      component of the future joins seam cells on both sides of the edge. Swapping the remaining
      components is an injection (Kempe). The bad event needs an alternating crossing path. Each
      path is a chain whose prescribed colours cost `(k-3)^{L+1}(k-4)` (`CSP.lean`'s chain bound).
      Crossing paths are counted by their step shapes: `1, 2, 4, 10, 31, 76` exactly for `L ≤ 7`
      (`decide +kernel`), and at most `(L-1)3^{L-1}` beyond.
* **Threshold.** `2ε_k ≤ γ_k` for every `k ≥ 10` (`two_epsK_le_gammaK`). After substituting
  `k = 10 + u`, the difference is a polynomial in `u` with positive coefficients.

## Modules

| file | content |
|---|---|
| `CSP.lean` | finite constraint systems, fibres, the chain bound |
| `Slab.lean` | the slab model of a seam; `#Ω = ∑_p ∑_s F(keys ∘ s)` |
| `Star.lean` | deleting a seam pair adds exactly the solutions that use it |
| `Box.lean` | the box bound |
| `Kempe.lean` | the Kempe swap and the wall lemma |
| `Bad.lean` | bad solutions realize prescribed chains; union bound |
| `Paths.lean` | crossing-path shapes, their enumerator and counts, the series |
| `Labelling.lean` | transposition realization, glueing VC labellings, the move list |
| `Seam.lean` | `γ_k`, `ε_k`, the threshold, star and move steps, `slab_core` |
| `Main.lean` | gauges of a chain, stages (a) and (b), the telescope, `ecc_rowG_boxProd` |
| `Grid.lean` | `pathG r ≃g rowG (r+1)` |
| `Nine/` | the sharper constants and `ecc_boxProd_pathG_of_nine` |

## `k = 9` (`Nine/`)

The seam machinery is generic in the constants (`SlabBounds`, `GaugeBounds`). At `k = 9`:

* **Box** (`Nine/Box9.lean`). The fibre is split by the centre values `(a, b)`. The `y₁` factors
  sum to at most `53/5` lower-bound factors. For each label `b`, the `y₆` factor has ratio `1`
  or `6/5`, and each domino factor has ratio `9/7` or `3/2`, depending on whether `b` is
  available at that cell. At most `3, 2, 2` labels are unavailable, so the nine labels contribute
  at most `8478/490`. The result is `γ₉ = 2450/449334`, against `400/104976` for the uniform
  bound.
* **Paths** (`Nine/Bad9.lean`, `Nine/Counts.lean`). A 2-cell crossing path closes a 4-cycle with
  its seam cells; its first cell has two later neighbours, so its chain costs `7 · 6² · 5`. The
  other chains cost `5 · 6^{L+1}`. Shape counts are exact up to twelve cells:
  `212, 552, 1607, 4250, 12296` for `L = 8, …, 12`, by kernel evaluation of a count-only
  enumerator (about 2.5 minutes). The `(L-1)3^{L-1}` tail covers longer paths.
* **Threshold.** `(1 - ε₉)² ≥ 1 - γ₉` with a margin of about 3%.

`k = 8` fails for this method: the path loss alone is about `0.0076`.

## Credit

The route and its proof are new in this development, worked out by Claude (Anthropic) on
2026-10-15 to 17. The building blocks are classical:
* DP-colourings are Dvořák–Postle's;
* the swap is Kempe's;
* the column telescope is GridGen's (`GridGen/Telescope.lean`), used here with a column-dependent
  reference.
